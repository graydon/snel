// Recursive-descent parser. Mirrors src/parse.rs. Uses setjmp/longjmp for the
// error path; nodes are arena-allocated (leaked).
#include "lex.h"
#include "snel.h"
#include <setjmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

Node *node_new(AKind k, uint32_t lo);

static const char *KEYWORDS[] = {"let", "fun", "typ",  "mod",   "pub", "use", "try", "else",
                                 "err", "if",  "then", "where", "nil", "is",  "and", "or",
                                 "not", "inf", "nan",  "true",  "false", "do",  "end", "bit",
                                 "i64", "f64", "u8",   NULL};

typedef struct {
    Lexed L;
    size_t pos;
    uint32_t depth;
    SnelErr err;
    jmp_buf jb;
} P;

static void perr(P *p, const char *msg) {
    snprintf(p->err.msg, sizeof p->err.msg, "%s", msg);
    p->err.span = p->L.t[p->pos].at;
    longjmp(p->jb, 1);
}
static bool is_kw_str(const uint8_t *b, size_t n) {
    for (int i = 0; KEYWORDS[i]; i++)
        if (strlen(KEYWORDS[i]) == n && memcmp(KEYWORDS[i], b, n) == 0)
            return true;
    return false;
}

static Tok *cur(P *p) {
    return &p->L.t[p->pos];
}
static Tok *peek(P *p) {
    // newlines are insignificant whitespace everywhere; `;` separates decls. doc
    // comments are only skipped inside brackets (top level, p_decl reads them).
    for (;;) {
        TokKind k = p->L.t[p->pos].k;
        if (k == TK_NEWLINE || (k == TK_DOC && p->depth > 0))
            p->pos++;
        else
            break;
    }
    return &p->L.t[p->pos];
}
static uint32_t at(P *p) {
    return p->L.t[p->pos].at;
}
static bool is_punct(P *p, const char *s) {
    Tok *t = peek(p);
    return t->k == TK_PUNCT && strcmp(t->punct, s) == 0;
}
static bool is_name(P *p, const char *s) {
    Tok *t = peek(p);
    return t->k == TK_NAME && t->bin.len == strlen(s) &&
           memcmp(bin_bytes(&t->bin), s, t->bin.len) == 0;
}
static bool take_punct(P *p, const char *s) {
    if (is_punct(p, s)) {
        p->pos++;
        return true;
    }
    return false;
}
static bool take_kw(P *p, const char *s) {
    if (is_name(p, s)) {
        p->pos++;
        return true;
    }
    return false;
}
static void eat(P *p, const char *s) {
    peek(p);
    if (cur(p)->k == TK_PUNCT && strcmp(cur(p)->punct, s) == 0) {
        p->pos++;
        return;
    }
    char m[64];
    snprintf(m, sizeof m, "expected `%s`", s);
    perr(p, m);
}
static void eat_kw(P *p, const char *s) {
    if (take_kw(p, s))
        return;
    char m[64];
    snprintf(m, sizeof m, "expected `%s`", s);
    perr(p, m);
}

static Bin p_name(P *p) {
    peek(p);
    Tok *t = cur(p);
    if (t->k != TK_NAME)
        perr(p, "expected name");
    if (is_kw_str(bin_bytes(&t->bin), t->bin.len) ||
        op_by_name(bin_bytes(&t->bin), t->bin.len) >= 0)
        perr(p, "reserved name");
    p->pos++;
    return bin_clone(t->bin);
}
// Field names (record keys, tab-type fields, projections) are tab keys, not
// terms, so builtin names are allowed here — only keywords are excluded.
static Bin p_field(P *p) {
    peek(p);
    Tok *t = cur(p);
    if (t->k != TK_NAME)
        perr(p, "expected a field name");
    if (is_kw_str(bin_bytes(&t->bin), t->bin.len))
        perr(p, "reserved name");
    p->pos++;
    return bin_clone(t->bin);
}

// forward decls
static Node *p_expr(P *p);
static Node *p_decl(P *p);
static Ty p_ty(P *p);
static Node *p_atom(P *p);
static Node *p_postfix(P *p);
static Node *p_unary(P *p);

static void set_span(P *p, Node *n, uint32_t lo) {
    n->lo = lo;
    n->hi = at(p);
}

// ----- separators -----
static void skip_seps(P *p) {
    for (;;) {
        Tok *t = &p->L.t[p->pos];
        if (t->k == TK_NEWLINE || (t->k == TK_PUNCT && strcmp(t->punct, ";") == 0)) {
            p->pos++;
            continue;
        }
        if (t->k == TK_DOC &&
            (p->L.t[p->pos + 1].k == TK_NEWLINE || p->L.t[p->pos + 1].k == TK_EOF)) {
            p->pos++;
            continue;
        }
        break;
    }
}

// parse decls until a terminator punct (")" or "}") or EOF, given by `end`
static Node *p_decls(P *p, const char *end, bool end_eof, size_t *count) {
    Node *out = NULL;
    size_t n = 0, cap = 0;
    for (;;) {
        skip_seps(p);
        Tok *t = &p->L.t[p->pos];
        if ((end_eof && t->k == TK_EOF) ||
            (!end_eof && t->k == TK_PUNCT && strcmp(t->punct, end) == 0)) {
            p->pos++;
            *count = n;
            return out;
        }
        Node *d = p_decl(p);
        if (n == cap) {
            cap = cap ? cap * 2 : 8;
            out = realloc(out, cap * sizeof(Node));
        }
        out[n++] = *d;
        while (p->L.t[p->pos].k == TK_NEWLINE)
            p->pos++; // trailing whitespace before the separator
        Tok *nx = &p->L.t[p->pos];
        bool ok = (nx->k == TK_PUNCT && strcmp(nx->punct, ";") == 0) ||
                  (end_eof && nx->k == TK_EOF) ||
                  (!end_eof && nx->k == TK_PUNCT && strcmp(nx->punct, end) == 0);
        if (!ok)
            perr(p, "expected `;` or end of block");
    }
}

// ----- types -----
static Ty p_ty_atom(P *p) {
    Ty t;
    memset(&t, 0, sizeof t);
    if (take_punct(p, "[")) {
        p->depth++;
        Ty inner = p_ty(p);
        p->depth--;
        eat(p, "]");
        t.k = T_VEC;
        t.elem = malloc(sizeof(Ty));
        t.elem[0] = inner;
        t.n = 1;
        return t;
    }
    if (take_punct(p, "{")) {
        p->depth++;
        Bin *fs = NULL;
        Ty *ts = NULL;
        size_t n = 0, cap = 0;
        if (!is_punct(p, "}")) {
            for (;;) {
                Bin k = p_field(p);
                eat(p, ":");
                Ty ft = p_ty(p);
                if (n == cap) {
                    cap = cap ? cap * 2 : 4;
                    fs = realloc(fs, cap * sizeof(Bin));
                    ts = realloc(ts, cap * sizeof(Ty));
                }
                fs[n] = k;
                ts[n] = ft;
                n++;
                if (!take_punct(p, ","))
                    break;
            }
        }
        p->depth--;
        eat(p, "}");
        t.k = T_TAB;
        t.n = n;
        t.fields = fs;
        t.elem = ts;
        return t;
    }
    if (take_kw(p, "fun")) {
        eat(p, "(");
        p->depth++;
        Ty *args = NULL;
        size_t n = 0, cap = 0;
        if (!is_punct(p, ")")) {
            for (;;) {
                Ty a = p_ty(p);
                if (n == cap) {
                    cap = cap ? cap * 2 : 4;
                    args = realloc(args, cap * sizeof(Ty));
                }
                args[n++] = a;
                if (!take_punct(p, ","))
                    break;
            }
        }
        eat(p, ")");
        p->depth--;
        eat(p, "->");
        Ty r = p_ty(p);
        t.k = T_FUN;
        t.n = n;
        t.elem = args;
        t.ret = malloc(sizeof(Ty));
        *t.ret = r;
        return t;
    }
    peek(p);
    Tok *tk = cur(p);
    if (tk->k != TK_NAME)
        perr(p, "expected type");
    const uint8_t *b = bin_bytes(&tk->bin);
    size_t bn = tk->bin.len;
    p->pos++;
    if (bn == 3 && !memcmp(b, "nil", 3)) {
        t.k = T_NIL;
        return t;
    }
    if (bn == 3 && !memcmp(b, "bit", 3)) {
        t.k = T_BIT;
        return t;
    }
    if (bn == 3 && !memcmp(b, "i64", 3)) {
        t.k = T_I64;
        return t;
    }
    if (bn == 3 && !memcmp(b, "f64", 3)) {
        t.k = T_F64;
        return t;
    }
    if (bn == 2 && !memcmp(b, "u8", 2)) {
        t.k = T_U8;
        return t;
    }
    if (is_kw_str(b, bn))
        perr(p, "not a type");
    t.k = T_NAME;
    t.name = bin_clone(tk->bin);
    return t;
}

// union_of: flatten + dedup
static Ty union_of(Ty *parts, size_t n) {
    Ty flat[64];
    size_t fn = 0;
    for (size_t i = 0; i < n; i++) {
        if (parts[i].k == T_UNION)
            for (size_t j = 0; j < parts[i].n; j++)
                flat[fn++] = parts[i].elem[j];
        else
            flat[fn++] = parts[i];
    }
    // dedup by structural fmt equality (cheap: compare printed forms)
    Ty out[64];
    size_t on = 0;
    for (size_t i = 0; i < fn; i++) {
        bool dup = false;
        char *fi = fmt_ty(&flat[i]);
        for (size_t j = 0; j < on; j++) {
            char *fj = fmt_ty(&out[j]);
            if (!strcmp(fi, fj))
                dup = true;
            free(fj);
            if (dup)
                break;
        }
        free(fi);
        if (!dup)
            out[on++] = flat[i];
    }
    if (on == 1)
        return out[0];
    Ty u;
    memset(&u, 0, sizeof u);
    u.k = T_UNION;
    u.n = on;
    u.elem = malloc(on * sizeof(Ty));
    memcpy(u.elem, out, on * sizeof(Ty));
    return u;
}

static Ty p_ty_post(P *p) {
    Ty t = p_ty_atom(p);
    if (take_punct(p, "?")) {
        Ty nilt;
        memset(&nilt, 0, sizeof nilt);
        nilt.k = T_NIL;
        Ty parts[2] = {t, nilt};
        return union_of(parts, 2);
    }
    return t;
}
static Ty p_ty(P *p) {
    Ty parts[64];
    size_t n = 0;
    parts[n++] = p_ty_post(p);
    while (take_punct(p, "|"))
        parts[n++] = p_ty_post(p);
    if (n == 1)
        return parts[0];
    return union_of(parts, n);
}

// ----- params -----
static void p_params(P *p, Bin **names, Ty **types, size_t *count) {
    eat(p, "(");
    p->depth++;
    Bin *ns = NULL;
    Ty *ts = NULL;
    size_t n = 0, cap = 0;
    if (!is_punct(p, ")")) {
        for (;;) {
            Bin x = p_name(p);
            eat(p, ":");
            Ty t = p_ty(p);
            if (n == cap) {
                cap = cap ? cap * 2 : 4;
                ns = realloc(ns, cap * sizeof(Bin));
                ts = realloc(ts, cap * sizeof(Ty));
            }
            ns[n] = x;
            ts[n] = t;
            n++;
            if (!take_punct(p, ","))
                break;
        }
    }
    eat(p, ")");
    p->depth--;
    *names = ns;
    *types = ts;
    *count = n;
}

static Node *p_fun_expr(P *p, uint32_t lo) {
    Node *n = node_new(A_FUN, lo);
    p_params(p, &n->params, &n->ptypes, &n->nparams);
    eat(p, "->");
    n->ty = p_ty(p);
    n->has_ty = true;
    eat(p, "=");
    n->a = p_expr(p);
    set_span(p, n, lo);
    return n;
}

// ----- binops -----
typedef struct {
    const char *surf, *name;
} OpPair;

static Node *mk_app2(P *p, uint32_t lo, const char *opname, Node *l, Node *r) {
    Node *f = node_new(A_VAR, lo);
    f->name = bin_str(opname);
    Node *n = node_new(A_APP, lo);
    n->a = f;
    n->kids = malloc(2 * sizeof(Node));
    n->kids[0] = *l;
    n->kids[1] = *r;
    n->nkids = 2;
    return n;
}

static Node *binlevel(P *p, const OpPair *ops, size_t nops, Node *(*next)(P *)) {
    uint32_t lo = at(p);
    Node *e = next(p);
    for (;;) {
        bool matched = false;
        for (size_t k = 0; k < nops; k++) {
            bool alpha = (ops[k].surf[0] >= 'a' && ops[k].surf[0] <= 'z');
            bool hit = alpha ? take_kw(p, ops[k].surf) : take_punct(p, ops[k].surf);
            if (hit) {
                Node *r = next(p);
                e = mk_app2(p, lo, ops[k].name, e, r);
                matched = true;
                break;
            }
        }
        if (!matched)
            return e;
    }
}

static Node *lvl_mul(P *p) {
    static const OpPair o[] = {{"*", "mul"}, {"/", "div"}, {"%", "rem"}};
    return binlevel(p, o, 3, p_unary);
}
static Node *lvl_add(P *p) {
    static const OpPair o[] = {{"+", "add"}, {"-", "sub"}};
    return binlevel(p, o, 2, lvl_mul);
}
static Node *lvl_cmp(P *p) {
    static const OpPair o[] = {{"=", "eq"},  {"<>", "ne"}, {"<=", "le"},
                               {">=", "ge"}, {"<", "lt"},  {">", "gt"}};
    return binlevel(p, o, 6, lvl_add);
}
static Node *lvl_and(P *p) {
    static const OpPair o[] = {{"and", "and"}};
    return binlevel(p, o, 1, lvl_cmp);
}
static Node *lvl_or(P *p) {
    static const OpPair o[] = {{"or", "or"}};
    return binlevel(p, o, 1, lvl_and);
}

static Node *p_unary(P *p) {
    uint32_t lo = at(p);
    if (take_punct(p, "-")) {
        // Fold `-<int literal>` before the atom's range check, so -2^63 works.
        peek(p);
        if (cur(p)->k == TK_INT) {
            uint64_t m = cur(p)->mag;
            p->pos++;
            if (m > (uint64_t)INT64_MAX + 1)
                perr(p, "int out of range");
            int64_t v = (m == (uint64_t)INT64_MAX + 1) ? INT64_MIN : -(int64_t)m;
            Node *n = node_new(A_LIT, lo);
            n->lit = vi64(v);
            return n;
        }
        Node *e = p_unary(p);
        if (e->k == A_LIT && e->lit.k == V_F64) {
            Node *n = node_new(A_LIT, lo);
            n->lit = vf64(canon_f64(-e->lit.u.f));
            return n;
        }
        Node *f = node_new(A_VAR, lo);
        f->name = bin_str("neg");
        Node *n = node_new(A_APP, lo);
        n->a = f;
        n->kids = malloc(sizeof(Node));
        n->kids[0] = *e;
        n->nkids = 1;
        return n;
    }
    if (take_kw(p, "not")) {
        Node *e = p_unary(p);
        Node *f = node_new(A_VAR, lo);
        f->name = bin_str("not");
        Node *n = node_new(A_APP, lo);
        n->a = f;
        n->kids = malloc(sizeof(Node));
        n->kids[0] = *e;
        n->nkids = 1;
        return n;
    }
    return p_postfix(p);
}

static Node *p_postfix(P *p) {
    uint32_t lo = at(p);
    Node *e = p_atom(p);
    for (;;) {
        if (take_punct(p, ".")) {
            Bin x = p_field(p);
            Node *n = node_new(A_PROJ, lo);
            n->a = e;
            n->name = x;
            e = n;
        } else if (is_punct(p, "[")) {
            p->pos++;
            p->depth++;
            Node *i = p_expr(p);
            p->depth--;
            eat(p, "]");
            Node *n = node_new(A_IDX, lo);
            n->a = e;
            n->b = i;
            e = n;
        } else if (is_punct(p, "(")) {
            p->pos++;
            p->depth++;
            Node *args = NULL;
            size_t na = 0, cap = 0;
            if (!is_punct(p, ")")) {
                for (;;) {
                    Node *a = p_expr(p);
                    if (na == cap) {
                        cap = cap ? cap * 2 : 4;
                        args = realloc(args, cap * sizeof(Node));
                    }
                    args[na++] = *a;
                    if (!take_punct(p, ","))
                        break;
                }
            }
            p->depth--;
            eat(p, ")");
            Node *n = node_new(A_APP, lo);
            n->a = e;
            n->kids = args;
            n->nkids = na;
            e = n;
        } else
            return e;
    }
}

static bool is_decl_node(Node *n) {
    return n->k == A_LET || n->k == A_TYP || n->k == A_USE;
}

static Node *p_atom(P *p) {
    uint32_t lo = at(p);
    peek(p);
    Tok *t = cur(p);
    switch (t->k) {
        case TK_INT: {
            p->pos++;
            if (t->mag > (uint64_t)INT64_MAX)
                perr(p, "int out of range");
            Node *n = node_new(A_LIT, lo);
            n->lit = vi64((int64_t)t->mag);
            return n;
        }
        case TK_FLOAT: {
            p->pos++;
            Node *n = node_new(A_LIT, lo);
            n->lit = vf64(t->f);
            return n;
        }
        case TK_U8: {
            p->pos++;
            Node *n = node_new(A_LIT, lo);
            Val v;
            v.k = V_U8;
            v.u.i = t->u8;
            n->lit = v;
            return n;
        }
        case TK_BITVEC: {
            p->pos++;
            const uint8_t *d = bin_bytes(&t->bin);
            Bits bits = bits_new(0, false);
            for (size_t k = 0; k < t->bin.len; k++)
                bits_push(&bits, d[k] == '1');
            Payload pl;
            memset(&pl, 0, sizeof pl);
            pl.k = P_BITS;
            pl.u.bits = bits;
            Node *n = node_new(A_LIT, lo);
            Val v;
            v.k = V_VEC;
            v.u.vec = col_simple(pl);
            n->lit = v;
            return n;
        }
        case TK_STR: {
            p->pos++;
            Node *n = node_new(A_LIT, lo);
            Val v;
            v.k = V_VEC;
            v.u.vec = col_u8s(bin_bytes(&t->bin), t->bin.len);
            n->lit = v;
            return n;
        }
        case TK_PUNCT:
            if (!strcmp(t->punct, ":")) { // :name is sugar for the string "name"
                p->pos++;
                Bin name = p_field(p);
                Node *n = node_new(A_LIT, lo);
                Val v;
                v.k = V_VEC;
                v.u.vec = col_u8s(bin_bytes(&name), name.len);
                n->lit = v;
                return n;
            }
            if (!strcmp(t->punct, "(")) {
                p->pos++;
                p->depth++;
                Node *first = p_decl(p);
                if (!is_decl_node(first) && take_punct(p, ":")) {
                    Ty ty = p_ty(p);
                    p->depth--;
                    eat(p, ")");
                    Node *n = node_new(A_AS, lo);
                    n->a = first;
                    n->ty = ty;
                    n->has_ty = true;
                    return n;
                }
                Node *ds = NULL;
                size_t n = 0, cap = 0;
                ds = realloc(ds, sizeof(Node));
                ds[n++] = *first;
                cap = 1;
                for (;;) {
                    if (take_punct(p, ")"))
                        break;
                    eat(p, ";"); // `;` separates block items
                    skip_seps(p);
                    if (take_punct(p, ")"))
                        break; // trailing `;`
                    Node *d = p_decl(p);
                    if (n == cap) {
                        cap *= 2;
                        ds = realloc(ds, cap * sizeof(Node));
                    }
                    ds[n++] = *d;
                }
                p->depth--;
                if (n == 1 && !is_decl_node(&ds[0])) {
                    Node *r = malloc(sizeof(Node));
                    *r = ds[0];
                    return r;
                }
                Node *seq = node_new(A_SEQ, lo);
                seq->kids = ds;
                seq->nkids = n;
                return seq;
            }
            if (!strcmp(t->punct, "[")) {
                p->pos++;
                p->depth++;
                Node *es = NULL;
                size_t n = 0, cap = 0;
                if (!is_punct(p, "]"))
                    for (;;) {
                        Node *e = p_expr(p);
                        if (n == cap) {
                            cap = cap ? cap * 2 : 4;
                            es = realloc(es, cap * sizeof(Node));
                        }
                        es[n++] = *e;
                        if (!take_punct(p, ","))
                            break;
                    }
                p->depth--;
                eat(p, "]");
                Node *nn = node_new(A_VEC, lo);
                nn->kids = es;
                nn->nkids = n;
                return nn;
            }
            if (!strcmp(t->punct, "{")) {
                p->pos++;
                p->depth++;
                Bin *ks = NULL;
                Node *vs = NULL;
                size_t n = 0, cap = 0;
                if (!is_punct(p, "}"))
                    for (;;) {
                        Bin k = p_field(p);
                        eat(p, "=");
                        Node *e = p_expr(p);
                        if (n == cap) {
                            cap = cap ? cap * 2 : 4;
                            ks = realloc(ks, cap * sizeof(Bin));
                            vs = realloc(vs, cap * sizeof(Node));
                        }
                        ks[n] = k;
                        vs[n] = *e;
                        n++;
                        if (!take_punct(p, ","))
                            break;
                    }
                p->depth--;
                eat(p, "}");
                Node *nn = node_new(A_TAB, lo);
                nn->keys = ks;
                nn->nkeys = n;
                nn->kids = vs;
                nn->nkids = n;
                return nn;
            }
            perr(p, "unexpected punctuation");
            return NULL;
        case TK_NAME: {
            const uint8_t *b = bin_bytes(&t->bin);
            size_t bn = t->bin.len;
            p->pos++;
            if (bn == 3 && !memcmp(b, "nil", 3)) {
                Node *n = node_new(A_LIT, lo);
                n->lit = vnil();
                return n;
            }
            if (bn == 3 && !memcmp(b, "inf", 3)) {
                Node *n = node_new(A_LIT, lo);
                n->lit = vf64(1.0 / 0.0);
                return n;
            }
            if (bn == 3 && !memcmp(b, "nan", 3)) {
                Node *n = node_new(A_LIT, lo);
                n->lit = vf64(canon_f64(0.0 / 0.0));
                return n;
            }
            // sugar for the bit literals 1b / 0b
            if (bn == 4 && !memcmp(b, "true", 4)) {
                Node *n = node_new(A_LIT, lo);
                n->lit = vbit(true);
                return n;
            }
            if (bn == 5 && !memcmp(b, "false", 5)) {
                Node *n = node_new(A_LIT, lo);
                n->lit = vbit(false);
                return n;
            }
            if (bn == 2 && !memcmp(b, "do", 2)) {
                // `do … end` is a block, a synonym for `( … )`
                p->depth++;
                Node *first = p_decl(p);
                Node *ds = malloc(sizeof(Node));
                size_t n = 0, cap = 1;
                ds[n++] = *first;
                for (;;) {
                    if (take_kw(p, "end"))
                        break;
                    eat(p, ";");
                    skip_seps(p);
                    if (take_kw(p, "end"))
                        break; // trailing `;`
                    Node *d = p_decl(p);
                    if (n == cap) {
                        cap *= 2;
                        ds = realloc(ds, cap * sizeof(Node));
                    }
                    ds[n++] = *d;
                }
                p->depth--;
                if (n == 1 && !is_decl_node(&ds[0])) {
                    Node *r = malloc(sizeof(Node));
                    *r = ds[0];
                    return r;
                }
                Node *seq = node_new(A_SEQ, lo);
                seq->kids = ds;
                seq->nkids = n;
                return seq;
            }
            if (bn == 3 && !memcmp(b, "fun", 3)) {
                return p_fun_expr(p, lo);
            }
            if (bn == 2 && !memcmp(b, "if", 2)) {
                Node *n = node_new(A_IF, lo);
                n->a = p_expr(p);
                eat_kw(p, "then");
                n->b = p_expr(p);
                eat_kw(p, "else");
                n->c = p_expr(p);
                return n;
            }
            if (bn == 3 && !memcmp(b, "try", 3)) {
                Node *n = node_new(A_TRY, lo);
                n->a = p_expr(p);
                eat_kw(p, "else");
                n->b = p_expr(p);
                return n;
            }
            if (bn == 3 && !memcmp(b, "err", 3)) {
                Node *n = node_new(A_ERR, lo);
                n->a = p_expr(p);
                return n;
            }
            if (op_by_name(b, bn) >= 0) {
                Node *n = node_new(A_VAR, lo);
                n->name = bin_new(b, bn);
                return n;
            }
            if (is_kw_str(b, bn))
                perr(p, "unexpected keyword");
            Node *n = node_new(A_VAR, lo);
            n->name = bin_new(b, bn);
            return n;
        }
        default:
            perr(p, "unexpected token");
            return NULL;
    }
}

static bool is_pipe_hole(const Node *n) {
    return n->k == A_VAR && n->name.len == 1 && bin_bytes(&n->name)[0] == '_';
}

// Tacit pipe: `x |> f(a)` is `f(a, x)` — the left value is appended as the last
// argument, or substituted for each `_` placeholder if any are present. `x |> f`
// (a bare callee) is `f(x)`. Mirrors src/parse.rs desugar_pipe.
static Node *desugar_pipe(Node *lhs, Node *rhs, uint32_t lo) {
    if (rhs->k == A_APP) {
        size_t holes = 0;
        for (size_t i = 0; i < rhs->nkids; i++)
            if (is_pipe_hole(&rhs->kids[i]))
                holes++;
        if (holes == 0) {
            rhs->kids = realloc(rhs->kids, (rhs->nkids + 1) * sizeof(Node));
            rhs->kids[rhs->nkids++] = *lhs;
        } else {
            for (size_t i = 0; i < rhs->nkids; i++)
                if (is_pipe_hole(&rhs->kids[i]))
                    rhs->kids[i] = *lhs;
        }
        return rhs;
    }
    Node *app = node_new(A_APP, lo);
    app->a = rhs;
    app->kids = malloc(sizeof(Node));
    app->kids[0] = *lhs;
    app->nkids = 1;
    return app;
}

static Node *p_pipe(P *p) {
    uint32_t lo = at(p);
    Node *e = lvl_or(p);
    while (take_punct(p, "|>")) {
        Node *rhs = lvl_or(p);
        e = desugar_pipe(e, rhs, lo);
    }
    return e;
}

static Node *p_expr(P *p) {
    uint32_t lo = at(p);
    Node *e = p_pipe(p);
    if (take_kw(p, "is")) {
        Ty t = p_ty(p);
        Node *n = node_new(A_IS, lo);
        n->a = e;
        n->ty = t;
        n->has_ty = true;
        return n;
    }
    return e;
}

// fun type of a fun-literal node (for mod pub sigs)
static bool fun_sig(Node *e, Ty *out) {
    if (e->k != A_FUN)
        return false;
    Ty t;
    memset(&t, 0, sizeof t);
    t.k = T_FUN;
    t.n = e->nparams;
    t.elem = malloc((e->nparams ? e->nparams : 1) * sizeof(Ty));
    for (size_t i = 0; i < e->nparams; i++)
        t.elem[i] = e->ptypes[i];
    t.ret = malloc(sizeof(Ty));
    *t.ret = e->ty;
    *out = t;
    return true;
}

// always-true predicate node: fun(_: base) -> bit = 1b
static Node *always_true(uint32_t lo, Ty base) {
    Node *n = node_new(A_FUN, lo);
    n->params = malloc(sizeof(Bin));
    n->params[0] = bin_str("_");
    n->ptypes = malloc(sizeof(Ty));
    n->ptypes[0] = base;
    n->nparams = 1;
    n->ty.k = T_BIT;
    n->has_ty = true;
    Node *body = node_new(A_LIT, lo);
    body->lit = vbit(true);
    n->a = body;
    return n;
}

static Node *p_mod(P *p, uint32_t lo, bool has_doc, Bin doc, bool is_pub) {
    Bin x = p_name(p);
    bool parametric = is_punct(p, "(");
    Bin *pn = NULL;
    Ty *pt = NULL;
    size_t np = 0;
    if (parametric)
        p_params(p, &pn, &pt, &np);
    eat(p, "{");
    uint32_t saved = p->depth;
    p->depth = 0;
    size_t nds = 0;
    Node *ds = p_decls(p, "}", false, &nds);
    p->depth = saved;
    // pub names + declared types
    Bin pubs[64];
    Ty pubtys[64];
    bool pubhas[64];
    size_t npub = 0;
    for (size_t i = 0; i < nds; i++) {
        Node *d = &ds[i];
        if (d->k == A_LET && d->is_pub) {
            pubs[npub] = d->name;
            if (d->has_ty) {
                pubtys[npub] = d->ty;
                pubhas[npub] = true;
            } else if (fun_sig(d->a, &pubtys[npub]))
                pubhas[npub] = true;
            else
                pubhas[npub] = false;
            npub++;
        } else if (d->k == A_LET || d->k == A_TYP || d->k == A_USE) {
            // private / type decls allowed
        } else
            perr(p, "mod body must contain only declarations");
    }
    // build tab literal of pub names
    Node *tab = node_new(A_TAB, lo);
    tab->keys = malloc((npub ? npub : 1) * sizeof(Bin));
    tab->kids = malloc((npub ? npub : 1) * sizeof(Node));
    tab->nkeys = tab->nkids = npub;
    for (size_t i = 0; i < npub; i++) {
        tab->keys[i] = bin_clone(pubs[i]);
        Node *v = node_new(A_VAR, lo);
        v->name = bin_clone(pubs[i]);
        tab->kids[i] = *v;
    }
    // seq: decls ; tab
    Node *seq = node_new(A_SEQ, lo);
    seq->kids = malloc((nds + 1) * sizeof(Node));
    memcpy(seq->kids, ds, nds * sizeof(Node));
    seq->kids[nds] = *tab;
    seq->nkids = nds + 1;
    Node *e;
    if (!parametric)
        e = seq;
    else {
        // result type {pubs}
        Ty ret;
        memset(&ret, 0, sizeof ret);
        ret.k = T_TAB;
        ret.n = npub;
        ret.fields = malloc((npub ? npub : 1) * sizeof(Bin));
        ret.elem = malloc((npub ? npub : 1) * sizeof(Ty));
        for (size_t i = 0; i < npub; i++) {
            if (!pubhas[i])
                perr(p, "pub in parametric mod needs a type annotation");
            ret.fields[i] = bin_clone(pubs[i]);
            ret.elem[i] = pubtys[i];
        }
        Node *f = node_new(A_FUN, lo);
        f->params = pn;
        f->ptypes = pt;
        f->nparams = np;
        f->ty = ret;
        f->has_ty = true;
        f->a = seq;
        e = f;
    }
    Node *let = node_new(A_LET, lo);
    let->name = x;
    let->a = e;
    let->has_doc = has_doc;
    if (has_doc)
        let->doc = doc;
    let->is_pub = is_pub;
    return let;
}

static Node *p_decl(P *p) {
    bool has_doc = false;
    Bin doc;
    memset(&doc, 0, sizeof doc);
    peek(p);
    if (cur(p)->k == TK_DOC) {
        doc = bin_clone(cur(p)->bin);
        has_doc = true;
        p->pos++;
    }
    bool is_pub = take_kw(p, "pub");
    uint32_t lo = at(p);
    if (take_kw(p, "let")) {
        Bin x = p_name(p);
        Node *n = node_new(A_LET, lo);
        n->name = x;
        if (take_punct(p, ":")) {
            n->ty = p_ty(p);
            n->has_ty = true;
        }
        eat(p, "=");
        n->a = p_expr(p);
        n->has_doc = has_doc;
        if (has_doc)
            n->doc = doc;
        n->is_pub = is_pub;
        return n;
    }
    if (is_name(p, "fun") && p->L.t[p->pos + 1].k == TK_NAME) {
        p->pos++;
        Bin x = p_name(p);
        Node *f = p_fun_expr(p, lo);
        Node *n = node_new(A_LET, lo);
        n->name = x;
        n->a = f;
        n->has_doc = has_doc;
        if (has_doc)
            n->doc = doc;
        n->is_pub = is_pub;
        return n;
    }
    if (take_kw(p, "typ")) {
        Bin x = p_name(p);
        eat(p, "=");
        Ty base = p_ty(p);
        Node *pred;
        if (take_kw(p, "where"))
            pred = p_expr(p);
        else
            pred = always_true(lo, base);
        Node *n = node_new(A_TYP, lo);
        n->name = x;
        n->ty = base;
        n->has_ty = true;
        n->a = pred;
        n->has_doc = has_doc;
        if (has_doc)
            n->doc = doc;
        n->is_pub = is_pub;
        return n;
    }
    if (take_kw(p, "use")) {
        Bin x = p_name(p);
        Node *n = node_new(A_USE, lo);
        n->name = x;
        // `use x = "url"` names a remote unit (parsed here, refused at load)
        if (take_punct(p, "=")) {
            Tok *t = peek(p);
            if (t->k != TK_STR)
                perr(p, "expected a url string");
            n->url = bin_clone(t->bin);
            n->has_url = true;
            p->pos++;
        }
        n->has_doc = has_doc;
        if (has_doc)
            n->doc = doc;
        return n;
    }
    if (take_kw(p, "mod"))
        return p_mod(p, lo, has_doc, doc, is_pub);
    if (is_pub)
        perr(p, "pub must precede let/fun/typ/mod");
    if (has_doc)
        perr(p, "doc comment must precede a declaration");
    return p_expr(p);
}

Node *parse_unit(const char *src, size_t *ndecls, SnelErr *err) {
    P p;
    memset(&p, 0, sizeof p);
    if (!lex(src, &p.L, err))
        return NULL;
    if (setjmp(p.jb)) {
        *err = p.err;
        return NULL;
    }
    size_t n = 0;
    Node *ds = p_decls(&p, NULL, true, &n);
    *ndecls = n;
    return ds;
}

// The module doc comment: a `--` block at the very top of a unit, separated
// from the first declaration by a blank line. Returns false if there is none.
// (Mirrors src/parse.rs module_doc.) On success `out` is a fresh Bin.
bool module_doc(const char *src, Bin *out) {
    Lexed L;
    SnelErr e;
    if (!lex(src, &L, &e))
        return false;
    if (L.n >= 2 && L.t[0].k == TK_DOC && L.t[1].k == TK_NEWLINE) {
        *out = bin_clone(L.t[0].bin);
        return true;
    }
    return false;
}
