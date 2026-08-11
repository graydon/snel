// Canonical text form and the f64 <-> decimal routines. Must match the Rust
// print.rs byte for byte.
#include "snel.h"
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// ---------- growable string ----------
typedef struct {
    char *p;
    size_t len, cap;
} Str;
static void sput(Str *s, const char *t) {
    size_t n = strlen(t);
    if (s->len + n + 1 > s->cap) {
        s->cap = (s->len + n + 1) * 2;
        s->p = realloc(s->p, s->cap);
    }
    memcpy(s->p + s->len, t, n);
    s->len += n;
    s->p[s->len] = 0;
}
static void sputc(Str *s, char c) {
    char b[2] = {c, 0};
    sput(s, b);
}

// ---------- f64 ----------

double canon_f64(double x) {
    return isnan(x) ? NAN : x;
}

// digits (decimal string) * 10^(exp10 - len + 1), reparsed as f64.
static double decimal_to_f64(const char *digits, int exp10) {
    char buf[64];
    snprintf(buf, sizeof buf, "%se%d", digits, exp10 - (int)strlen(digits) + 1);
    return strtod(buf, NULL);
}

char *fmt_f64(double x) {
    Str s = {0};
    if (isnan(x)) {
        sput(&s, "nan");
        return s.p;
    }
    if (isinf(x)) {
        sput(&s, x < 0 ? "-inf" : "inf");
        return s.p;
    }
    if (x == 0.0) {
        sput(&s, signbit(x) ? "-0.0" : "0.0");
        return s.p;
    }
    bool neg = x < 0;
    double a = fabs(x);
    // find fewest significant digits (1..17) that reparse exactly
    char digits[32];
    int exp10 = 0;
    for (int p = 1; p <= 17; p++) {
        char tmp[64];
        snprintf(tmp, sizeof tmp, "%.*e", p - 1, a); // d.ddde±NN
        // split mantissa/exponent
        char *e = strchr(tmp, 'e');
        int ex = atoi(e + 1);
        // mantissa without '.'
        char m[32];
        int mi = 0;
        for (char *c = tmp; c < e; c++)
            if (*c != '.')
                m[mi++] = *c;
        m[mi] = 0;
        if (decimal_to_f64(m, ex) == a) {
            strcpy(digits, m);
            exp10 = ex;
            break;
        }
        if (p == 17) {
            strcpy(digits, m);
            exp10 = ex;
        }
    }
    // strip trailing zeros
    int nd = strlen(digits);
    while (nd > 1 && digits[nd - 1] == '0')
        digits[--nd] = 0;
    nd = strlen(digits);
    if (neg)
        sputc(&s, '-');
    char buf[64];
    if (exp10 < -4 || exp10 >= 17) {
        char frac[32];
        if (nd > 1)
            strcpy(frac, digits + 1);
        else
            strcpy(frac, "0");
        snprintf(buf, sizeof buf, "%c.%se%d", digits[0], frac, exp10);
        sput(&s, buf);
    } else if (exp10 >= nd - 1) {
        sput(&s, digits);
        for (int i = 0; i < exp10 - nd + 1; i++)
            sputc(&s, '0');
        sput(&s, ".0");
    } else if (exp10 >= 0) {
        for (int i = 0; i <= exp10; i++)
            sputc(&s, digits[i]);
        sputc(&s, '.');
        sput(&s, digits + exp10 + 1);
    } else {
        sput(&s, "0.");
        for (int i = 0; i < -exp10 - 1; i++)
            sputc(&s, '0');
        sput(&s, digits);
    }
    return s.p;
}

bool parse_f64(const char *str, double *out) {
    char *end;
    double v = strtod(str, &end);
    if (end == str)
        return false;
    *out = canon_f64(v);
    return true;
}

// ---------- [u8] strings ----------

// A u8 prints as a char literal: printable ASCII directly, else an escape.
static void fmt_u8_char(Str *s, uint8_t v) {
    char buf[8];
    switch (v) {
        case '\n':
            sput(s, "'\\n'");
            return;
        case '\t':
            sput(s, "'\\t'");
            return;
        case '\\':
            sput(s, "'\\\\'");
            return;
        case '\'':
            sput(s, "'\\''");
            return;
    }
    if (v >= 0x20 && v <= 0x7e)
        snprintf(buf, sizeof buf, "'%c'", v);
    else
        snprintf(buf, sizeof buf, "'\\x%02x'", v);
    sput(s, buf);
}

// A [u8] prints as a string literal when valid UTF-8, else as [char, ...].
static void fmt_u8s(Str *s, const uint8_t *p, size_t n) {
    if (!bin_is_utf8(p, n)) {
        sputc(s, '[');
        for (size_t i = 0; i < n; i++) {
            if (i)
                sput(s, ", ");
            fmt_u8_char(s, p[i]);
        }
        sputc(s, ']');
        return;
    }
    sputc(s, '"');
    for (size_t i = 0; i < n; i++) {
        uint8_t c = p[i];
        char buf[8];
        switch (c) {
            case '\\':
                sput(s, "\\\\");
                break;
            case '"':
                sput(s, "\\\"");
                break;
            case '\n':
                sput(s, "\\n");
                break;
            case '\t':
                sput(s, "\\t");
                break;
            default:
                if (c < 0x20) {
                    snprintf(buf, sizeof buf, "\\x%02x", c);
                    sput(s, buf);
                } else
                    sputc(s, c); // printable ascii and utf-8 continuation bytes pass through
        }
    }
    sputc(s, '"');
}

// ---------- col element / types ----------

Val col_elem(const Col *c, size_t i) {
    if (c->has_present && !bits_get(&c->present, i))
        return vnil();
    size_t cas = c->has_sel ? c->sel[i] : 0;
    const Payload *p = &c->cases[cas];
    switch (p->k) {
        case P_BITS:
            return vbit(bits_get(&p->u.bits, i));
        case P_I64S:
            return vi64(p->u.i64[i]);
        case P_F64S:
            return vf64(p->u.f64[i]);
        case P_U8S: {
            Val v;
            v.k = V_U8;
            v.u.i = bin_bytes(&p->u.u8s)[i];
            return v;
        }
        case P_VECS: {
            Val v;
            v.k = V_VEC;
            v.u.vec = col_retain(p->u.vecs[i]);
            return v;
        }
        case P_TABS: {
            Val v;
            v.k = V_TAB;
            v.u.tab = tab_retain(p->u.tab[i]);
            return v;
        }
    }
    return vnil();
}

static Ty ty_prim(TKind k) {
    Ty t;
    memset(&t, 0, sizeof t);
    t.k = k;
    return t;
}
static Ty *ty_box(Ty t) {
    Ty *p = malloc(sizeof(Ty));
    *p = t;
    return p;
}

Ty val_ty(const Val *v);

static Ty tab_elem_ty_at(Tab **v, size_t n, size_t at) {
    Ty t;
    memset(&t, 0, sizeof t);
    t.k = T_TAB;
    if (n == 0) {
        t.n = 0;
        return t;
    }
    Tab *first = v[at < n ? at : 0];
    t.n = first->len;
    t.fields = malloc(t.n * sizeof(Bin));
    t.elem = malloc(t.n * sizeof(Ty));
    for (size_t i = 0; i < first->len; i++) {
        t.fields[i] = bin_clone(first->keys[i]);
        t.elem[i] = val_ty(&first->vals[i]);
    }
    return t;
}

// The row a case actually owns: every case of a union column carries a
// full-length, aligned payload, but only the rows the selector points at hold
// real values — the rest is filler whose contents are unobservable. Returns -1
// for a case the selector never points at. (Mirrors src/print.rs col_ty.)
static long case_owner(const Col *c, int i) {
    if (!c->has_sel)
        return (i == 0 && c->len > 0) ? 0 : -1;
    for (size_t j = 0; j < c->len; j++)
        if (c->sel[j] == i)
            return (long)j;
    return -1;
}

static Ty case_ty(const Col *c, int i, size_t at) {
    switch (c->cases[i].k) {
        case P_BITS:
            return ty_prim(T_BIT);
        case P_I64S:
            return ty_prim(T_I64);
        case P_F64S:
            return ty_prim(T_F64);
        case P_U8S:
            return ty_prim(T_U8);
        case P_VECS: {
            Ty vt;
            memset(&vt, 0, sizeof vt);
            vt.k = T_VEC;
            vt.n = 1;
            vt.elem = ty_box(at < c->len ? col_ty(c->cases[i].u.vecs[at]) : ty_prim(T_I64));
            return vt;
        }
        default:
            return tab_elem_ty_at(c->cases[i].u.tab, c->len, at);
    }
}

Ty col_ty(const Col *c) {
    Ty ts[9];
    int n = 0;
    // Read each case's shape from a row it owns, and skip a case that owns no
    // row at all rather than describing its filler.
    for (int i = 0; i < c->ncases; i++) {
        long at = case_owner(c, i);
        if (at >= 0)
            ts[n++] = case_ty(c, i, (size_t)at);
    }
    if (n == 0) // empty, or all nil: describe the cases as declared
        for (int i = 0; i < c->ncases; i++)
            ts[n++] = case_ty(c, i, 0);
    if (c->has_present)
        ts[n++] = ty_prim(T_NIL);
    if (n == 1)
        return ts[0];
    Ty u;
    memset(&u, 0, sizeof u);
    u.k = T_UNION;
    u.n = n;
    u.elem = malloc(n * sizeof(Ty));
    for (int i = 0; i < n; i++)
        u.elem[i] = ts[i];
    return u;
}

static Ty ty_vec1(Ty inner) {
    Ty t;
    memset(&t, 0, sizeof t);
    t.k = T_VEC;
    t.n = 1;
    t.elem = ty_box(inner);
    return t;
}

Ty val_ty(const Val *v) {
    switch (v->k) {
        case V_NIL:
            return ty_prim(T_NIL);
        case V_BIT:
            return ty_prim(T_BIT);
        case V_I64:
            return ty_prim(T_I64);
        case V_F64:
            return ty_prim(T_F64);
        case V_U8:
            return ty_prim(T_U8);
        case V_VEC: {
            Ty t;
            memset(&t, 0, sizeof t);
            t.k = T_VEC;
            t.elem = ty_box(col_ty(v->u.vec));
            t.n = 1;
            return t;
        }
        case V_TAB: {
            Tab *tb = v->u.tab;
            Ty t;
            memset(&t, 0, sizeof t);
            t.k = T_TAB;
            t.n = tb->len;
            t.fields = malloc(tb->len * sizeof(Bin));
            t.elem = malloc(tb->len * sizeof(Ty));
            for (size_t i = 0; i < tb->len; i++) {
                t.fields[i] = bin_clone(tb->keys[i]);
                t.elem[i] = val_ty(&tb->vals[i]);
            }
            return t;
        }
        case V_FUN: {
            Clo *c = v->u.fun;
            Ty t;
            memset(&t, 0, sizeof t);
            t.k = T_FUN;
            t.n = c->nparams;
            t.elem = malloc((c->nparams ? c->nparams : 1) * sizeof(Ty));
            for (size_t i = 0; i < c->nparams; i++)
                t.elem[i] = c->ptypes[i]; // borrow ok for print
            t.ret = ty_box(c->ret);
            return t;
        }
        case V_PRIM: { // real io signatures (mirrors src/io.rs PRIMS); Str = [u8]
            const uint8_t *nm = bin_bytes(&v->u.bin);
            size_t nl = v->u.bin.len;
            Ty t;
            memset(&t, 0, sizeof t);
            t.k = T_FUN;
            if (nl == 4 && !memcmp(nm, "read", 4)) {
                t.n = 1;
                t.elem = malloc(sizeof(Ty));
                t.elem[0] = ty_vec1(ty_prim(T_U8));
                t.ret = ty_box(ty_vec1(ty_prim(T_U8)));
            } else if (nl == 5 && !memcmp(nm, "write", 5)) {
                t.n = 2;
                t.elem = malloc(2 * sizeof(Ty));
                t.elem[0] = ty_vec1(ty_prim(T_U8));
                t.elem[1] = ty_vec1(ty_prim(T_U8));
                t.ret = ty_box(ty_prim(T_NIL));
            } else if (nl == 4 && !memcmp(nm, "args", 4)) {
                t.n = 0;
                t.elem = NULL;
                t.ret = ty_box(ty_vec1(ty_vec1(ty_prim(T_U8))));
            } else if (nl == 3 && !memcmp(nm, "env", 3)) {
                t.n = 0;
                t.elem = NULL;
                Ty et;
                memset(&et, 0, sizeof et);
                et.k = T_TAB;
                et.n = 0;
                t.ret = ty_box(et);
            } else if (nl == 3 && !memcmp(nm, "exe", 3)) {
                t.n = 0;
                t.elem = NULL;
                t.ret = ty_box(ty_vec1(ty_prim(T_U8)));
            } else if (nl == 5 && !memcmp(nm, "spawn", 5)) {
                t.n = 4;
                t.elem = malloc(4 * sizeof(Ty));
                t.elem[0] = ty_vec1(ty_prim(T_U8));
                t.elem[1] = ty_vec1(ty_vec1(ty_prim(T_U8)));
                t.elem[2] = ty_vec1(ty_prim(T_U8));
                t.elem[3] = ty_vec1(ty_vec1(ty_prim(T_U8)));
                t.ret = ty_box(ty_vec1(ty_prim(T_U8)));
            } else if (nl == 4 && !memcmp(nm, "list", 4)) {
                t.n = 1;
                t.elem = malloc(sizeof(Ty));
                t.elem[0] = ty_vec1(ty_prim(T_U8));
                t.ret = ty_box(ty_vec1(ty_vec1(ty_prim(T_U8))));
            } else if (nl == 4 && !memcmp(nm, "stat", 4)) {
                t.n = 1;
                t.elem = malloc(sizeof(Ty));
                t.elem[0] = ty_vec1(ty_prim(T_U8));
                Ty st;
                memset(&st, 0, sizeof st);
                st.k = T_TAB;
                st.n = 3;
                st.fields = malloc(3 * sizeof(Bin));
                st.fields[0] = bin_str("size");
                st.fields[1] = bin_str("mtime");
                st.fields[2] = bin_str("isdir");
                st.elem = malloc(3 * sizeof(Ty));
                st.elem[0] = ty_prim(T_I64);
                st.elem[1] = ty_prim(T_I64);
                st.elem[2] = ty_prim(T_BIT);
                t.ret = ty_box(st);
            } else if (nl == 6 && !memcmp(nm, "exists", 6)) {
                t.n = 1;
                t.elem = malloc(sizeof(Ty));
                t.elem[0] = ty_vec1(ty_prim(T_U8));
                t.ret = ty_box(ty_prim(T_BIT));
            } else if (nl == 4 && !memcmp(nm, "time", 4)) {
                t.n = 0;
                t.elem = NULL;
                t.ret = ty_box(ty_prim(T_I64));
            } else if (nl == 5 && !memcmp(nm, "sleep", 5)) {
                t.n = 1;
                t.elem = malloc(sizeof(Ty));
                t.elem[0] = ty_prim(T_I64);
                t.ret = ty_box(ty_prim(T_NIL));
            } else if ((nl == 6 && (!memcmp(nm, "rename", 6) || !memcmp(nm, "unlink", 6))) ||
                       (nl == 4 && !memcmp(nm, "link", 4))) {
                size_t np =
                    (nl == 4) ? 2
                              : (!memcmp(nm, "rename", 6) ? 2 : 1); // rename/link take 2, unlink 1
                t.n = np;
                t.elem = malloc(np * sizeof(Ty));
                for (size_t i = 0; i < np; i++)
                    t.elem[i] = ty_vec1(ty_prim(T_U8));
                t.ret = ty_box(ty_prim(T_NIL));
            } else if (nl == 5 && (!memcmp(nm, "mkdir", 5) || !memcmp(nm, "rmdir", 5))) {
                t.n = 1;
                t.elem = malloc(sizeof(Ty));
                t.elem[0] = ty_vec1(ty_prim(T_U8));
                t.ret = ty_box(ty_prim(T_NIL));
            } else {
                t.n = 0;
                t.elem = NULL;
                t.ret = ty_box(ty_prim(T_NIL));
            }
            return t;
        }
    }
    return ty_prim(T_NIL);
}

// ---------- type printing ----------

char *fmt_ty(const Ty *t) {
    Str s = {0};
    switch (t->k) {
        case T_NIL:
            sput(&s, "nil");
            break;
        case T_BIT:
            sput(&s, "bit");
            break;
        case T_I64:
            sput(&s, "i64");
            break;
        case T_F64:
            sput(&s, "f64");
            break;
        case T_U8:
            sput(&s, "u8");
            break;
        case T_NAME: {
            char *t2 = malloc(t->name.len + 1);
            memcpy(t2, bin_bytes(&t->name), t->name.len);
            t2[t->name.len] = 0;
            sput(&s, t2);
            free(t2);
        } break;
        case T_VEC: {
            sputc(&s, '[');
            char *e = fmt_ty(&t->elem[0]);
            sput(&s, e);
            free(e);
            sputc(&s, ']');
        } break;
        case T_UNION:
            for (size_t i = 0; i < t->n; i++) {
                if (i)
                    sputc(&s, '|');
                char *e = fmt_ty(&t->elem[i]);
                sput(&s, e);
                free(e);
            }
            break;
        case T_TAB: {
            sputc(&s, '{');
            for (size_t i = 0; i < t->n; i++) {
                if (i)
                    sput(&s, ", ");
                char *k = malloc(t->fields[i].len + 1);
                memcpy(k, bin_bytes(&t->fields[i]), t->fields[i].len);
                k[t->fields[i].len] = 0;
                sput(&s, k);
                free(k);
                sput(&s, ": ");
                char *e = fmt_ty(&t->elem[i]);
                sput(&s, e);
                free(e);
            }
            sputc(&s, '}');
        } break;
        case T_FUN: {
            sput(&s, "fun(");
            for (size_t i = 0; i < t->n; i++) {
                if (i)
                    sput(&s, ", ");
                char *e = fmt_ty(&t->elem[i]);
                sput(&s, e);
                free(e);
            }
            sput(&s, ") -> ");
            char *r = fmt_ty(t->ret);
            sput(&s, r);
            free(r);
        } break;
    }
    return s.p;
}

// ---------- values ----------

static void fmt_val_into(Str *s, const Val *v);

// Insert `_` every 3 chars from the right of a run of `n` digit chars.
static void group3(Str *s, const char *d, size_t n) {
    for (size_t i = 0; i < n; i++) {
        if (i > 0 && (n - i) % 3 == 0)
            sputc(s, '_');
        sputc(s, d[i]);
    }
}
// Emit a number string, grouping the leading integer digits every 3.
static void group_number(Str *s, const char *num) {
    const char *p = num;
    if (*p == '-') {
        sputc(s, '-');
        p++;
    }
    size_t end = 0;
    while (p[end] >= '0' && p[end] <= '9')
        end++;
    if (end == 0) {
        sput(s, p); // inf / nan
        return;
    }
    group3(s, p, end);
    sput(s, p + end);
}
// A [bit] column renders as `:1011`, index 0 first, `_` every 4 bits.
static void fmt_bits_col(Str *s, const Bits *b) {
    sputc(s, ':');
    for (size_t i = 0; i < b->len; i++) {
        if (i > 0 && i % 4 == 0)
            sputc(s, '_');
        sputc(s, bits_get(b, i) ? '1' : '0');
    }
}

static void fmt_col(Str *s, const Col *c) {
    // A plain [u8] column prints as a string literal (or char-byte vector).
    if (!c->has_present && !c->has_sel && c->cases[0].k == P_U8S) {
        fmt_u8s(s, bin_bytes(&c->cases[0].u.u8s), c->cases[0].u.u8s.len);
        return;
    }
    // A plain [bit] column prints as :1011.
    if (!c->has_present && !c->has_sel && c->cases[0].k == P_BITS && c->len > 0) {
        fmt_bits_col(s, &c->cases[0].u.bits);
        return;
    }
    bool ascribe = (c->len == 0 || c->ncases > 1);
    if (ascribe)
        sputc(s, '(');
    sputc(s, '[');
    for (size_t i = 0; i < c->len; i++) {
        if (i)
            sput(s, ", ");
        Val e = col_elem(c, i);
        fmt_val_into(s, &e);
        val_drop(e);
    }
    sputc(s, ']');
    if (ascribe) {
        sput(s, " : [");
        Ty t = col_ty(c); // transient; leaked (process is short-lived)
        char *ts = fmt_ty(&t);
        sput(s, ts);
        free(ts);
        sputc(s, ']');
        sputc(s, ')');
    }
}

static void fmt_tab(Str *s, const Tab *t) {
    if (t->len == 0) {
        sput(s, "{}");
        return;
    }
    sput(s, "{ ");
    for (size_t i = 0; i < t->len; i++) {
        if (i)
            sput(s, ", ");
        Bin k = t->keys[i];
        char *ks = malloc(k.len + 1);
        memcpy(ks, bin_bytes(&k), k.len);
        ks[k.len] = 0;
        sput(s, ks);
        free(ks);
        sput(s, " = ");
        fmt_val_into(s, &t->vals[i]);
    }
    sput(s, " }");
}

char *fmt_node(const Node *n, int prec); // print.c below

static void fmt_val_into(Str *s, const Val *v) {
    char buf[64];
    switch (v->k) {
        case V_NIL:
            sput(s, "nil");
            break;
        case V_BIT:
            sput(s, v->u.i ? "true" : "false");
            break;
        case V_I64:
            snprintf(buf, sizeof buf, "%lld", (long long)v->u.i);
            group_number(s, buf);
            break;
        case V_F64: {
            char *f = fmt_f64(v->u.f);
            group_number(s, f);
            free(f);
        } break;
        case V_U8:
            fmt_u8_char(s, (uint8_t)(v->u.i & 0xff));
            break;
        case V_VEC:
            fmt_col(s, v->u.vec);
            break;
        case V_TAB:
            fmt_tab(s, v->u.tab);
            break;
        case V_FUN: {
            Clo *c = v->u.fun;
            // Non-empty captured env prints as a let-sequence, so the closure
            // re-reads to an identical closure (the fun recaptures these).
            if (c->env->len > 0) {
                sputc(s, '(');
                for (size_t i = 0; i < c->env->len; i++) {
                    sput(s, "let ");
                    Bin k = c->env->keys[i];
                    char *ks = malloc(k.len + 1);
                    memcpy(ks, bin_bytes(&k), k.len);
                    ks[k.len] = 0;
                    sput(s, ks);
                    free(ks);
                    sput(s, " = ");
                    fmt_val_into(s, &c->env->vals[i]);
                    sput(s, "; ");
                }
            }
            sput(s, "fun(");
            for (size_t i = 0; i < c->nparams; i++) {
                if (i)
                    sput(s, ", ");
                char *k = malloc(c->params[i].len + 1);
                memcpy(k, bin_bytes(&c->params[i]), c->params[i].len);
                k[c->params[i].len] = 0;
                sput(s, k);
                free(k);
                sput(s, ": ");
                char *pt = fmt_ty(&c->ptypes[i]);
                sput(s, pt);
                free(pt);
            }
            sput(s, ") -> ");
            char *rt = fmt_ty(&c->ret);
            sput(s, rt);
            free(rt);
            sput(s, " = ");
            char *b = fmt_node(c->body, 1);
            sput(s, b);
            free(b);
            if (c->env->len > 0)
                sputc(s, ')');
        } break;
        case V_PRIM: {
            // a builtin value prints as its bare name; an io prim as `io.name`
            if (op_by_name(bin_bytes(&v->u.bin), v->u.bin.len) < 0)
                sput(s, "io.");
            char *k = malloc(v->u.bin.len + 1);
            memcpy(k, bin_bytes(&v->u.bin), v->u.bin.len);
            k[v->u.bin.len] = 0;
            sput(s, k);
            free(k);
        } break;
    }
}

char *fmt_val(const Val *v) {
    Str s = {0};
    fmt_val_into(&s, v);
    if (!s.p) {
        s.p = malloc(1);
        s.p[0] = 0;
    }
    return s.p;
}

// ---------- code (AST) printing ----------

static const char *op_infix_c(int op) {
    switch (op) {
        case OP_ADD:
            return "+";
        case OP_SUB:
            return "-";
        case OP_MUL:
            return "*";
        case OP_DIV:
            return "/";
        case OP_REM:
            return "%";
        case OP_EQ:
            return "=";
        case OP_NE:
            return "<>";
        case OP_LT:
            return "<";
        case OP_LE:
            return "<=";
        case OP_GT:
            return ">";
        case OP_GE:
            return ">=";
        case OP_AND:
            return "and";
        case OP_OR:
            return "or";
        default:
            return NULL;
    }
}
static int op_prec_c(int op) {
    switch (op) {
        case OP_OR:
            return 2;
        case OP_AND:
            return 3;
        case OP_EQ:
        case OP_NE:
        case OP_LT:
        case OP_LE:
        case OP_GT:
        case OP_GE:
            return 4;
        case OP_ADD:
        case OP_SUB:
            return 5;
        case OP_MUL:
        case OP_DIV:
        case OP_REM:
            return 6;
        default:
            return 9;
    }
}

static void bin_raw(Str *s, const Bin *b) {
    char *k = malloc(b->len + 1);
    memcpy(k, bin_bytes(b), b->len);
    k[b->len] = 0;
    sput(s, k);
    free(k);
}
static void doc_prefix(Str *s, const Node *n) {
    if (!n->has_doc)
        return;
    const uint8_t *p = bin_bytes(&n->doc);
    size_t len = n->doc.len, i = 0;
    while (i <= len) {
        size_t j = i;
        while (j < len && p[j] != '\n')
            j++;
        sput(s, "-- ");
        char *line = malloc(j - i + 1);
        memcpy(line, p + i, j - i);
        line[j - i] = 0;
        sput(s, line);
        free(line);
        sputc(s, '\n');
        if (j >= len)
            break;
        i = j + 1;
    }
}

static void fmt_ast(Str *s, const Node *n, int *prec);

char *fmt_node(const Node *n, int prec) {
    Str s = {0};
    int my;
    Str inner = {0};
    fmt_ast(&inner, n, &my);
    if (my < prec) {
        sputc(&s, '(');
        sput(&s, inner.p ? inner.p : "");
        sputc(&s, ')');
    } else
        sput(&s, inner.p ? inner.p : "");
    free(inner.p);
    return s.p;
}

static void put_params(Str *s, const Node *n) {
    for (size_t i = 0; i < n->nparams; i++) {
        if (i)
            sput(s, ", ");
        bin_raw(s, &n->params[i]);
        sput(s, ": ");
        char *t = fmt_ty(&n->ptypes[i]);
        sput(s, t);
        free(t);
    }
}

bool ty_eq(const Ty *a, const Ty *b); // check.c: structural type equality

// Does this predicate look like the one `typ x = T` (no `where`) desugars to —
// `fun(_: T) -> bit = true`? Matched structurally, so no AST/format change is
// needed to remember that the source omitted the clause.
static bool is_always_true(const Node *pred, const Ty *base) {
    return pred->k == A_FUN && pred->nparams == 1 && pred->has_ty &&
           pred->ty.k == T_BIT && pred->params[0].len == 1 &&
           bin_bytes(&pred->params[0])[0] == '_' && ty_eq(&pred->ptypes[0], base) &&
           pred->a->k == A_LIT && pred->a->lit.k == V_BIT && pred->a->lit.u.i != 0;
}

static void fmt_ast(Str *s, const Node *n, int *prec) {
    *prec = 10;
    char buf[64];
    switch (n->k) {
        case A_LIT: {
            // A negative numeric literal renders with a leading `-`, which binds
            // like the prefix operator, not like an atom: without that, `(-1)[i]`
            // would print as `-1[i]` and re-read as `neg(1[i])`.
            char *v = fmt_val(&n->lit);
            if (v[0] == '-')
                *prec = 7;
            sput(s, v);
            free(v);
        } break;
        case A_VAR:
            bin_raw(s, &n->name);
            break;
        case A_PROJ: {
            char *e = fmt_node(n->a, 8);
            sput(s, e);
            free(e);
            sputc(s, '.');
            bin_raw(s, &n->name);
            *prec = 8;
        } break;
        case A_IDX: {
            char *e = fmt_node(n->a, 8);
            char *i = fmt_node(n->b, 0);
            sput(s, e);
            sputc(s, '[');
            sput(s, i);
            sputc(s, ']');
            free(e);
            free(i);
            *prec = 8;
        } break;
        case A_APP: {
            if (n->a->k == A_VAR) {
                int op = op_by_name(bin_bytes(&n->a->name), n->a->name.len);
                if (op >= 0) {
                    const char *sym = op_infix_c(op);
                    if (sym && n->nkids == 2) {
                        int p = op_prec_c(op);
                        char *l = fmt_node(&n->kids[0], p), *r = fmt_node(&n->kids[1], p + 1);
                        sput(s, l);
                        sputc(s, ' ');
                        sput(s, sym);
                        sputc(s, ' ');
                        sput(s, r);
                        free(l);
                        free(r);
                        *prec = p;
                        return;
                    }
                    if (op == OP_NEG && n->nkids == 1) {
                        // Two ways a prefix `-` fails to re-read as this node,
                        // decided on the operand's *rendered text* (which is
                        // what the parser will see):
                        //   - text already starting with `-` would give `--`,
                        //     which does not lex;
                        //   - a numeric literal absorbs the `-` at parse time,
                        //     turning this node into a plain literal — and `-0`
                        //     and `-nan` lose the negation entirely.
                        // Both fall back to the call form. Everywhere else (a
                        // variable, a call, a vector literal) `-x` is exact. A
                        // `-` written in source is folded while parsing, so a
                        // negative literal still prints bare as `-1`.
                        char *e = fmt_node(&n->kids[0], 7);
                        bool absorbs = (e[0] >= '0' && e[0] <= '9') || !strcmp(e, "inf") ||
                                       !strcmp(e, "nan");
                        if (e[0] == '-' || absorbs) {
                            sput(s, "neg(");
                            sput(s, e);
                            sputc(s, ')');
                            *prec = 8;
                        } else {
                            sputc(s, '-');
                            sput(s, e);
                            *prec = 7;
                        }
                        free(e);
                        return;
                    }
                    if (op == OP_NOT && n->nkids == 1) {
                        char *e = fmt_node(&n->kids[0], 7);
                        sput(s, "not ");
                        sput(s, e);
                        free(e);
                        *prec = 7;
                        return;
                    }
                    sput(s, op_name(op));
                    sputc(s, '(');
                    for (size_t i = 0; i < n->nkids; i++) {
                        if (i)
                            sput(s, ", ");
                        char *a = fmt_node(&n->kids[i], 0);
                        sput(s, a);
                        free(a);
                    }
                    sputc(s, ')');
                    *prec = 8;
                    return;
                }
            }
            char *f = fmt_node(n->a, 8);
            sput(s, f);
            free(f);
            sputc(s, '(');
            for (size_t i = 0; i < n->nkids; i++) {
                if (i)
                    sput(s, ", ");
                char *a = fmt_node(&n->kids[i], 0);
                sput(s, a);
                free(a);
            }
            sputc(s, ')');
            *prec = 8;
        } break;
        case A_VEC:
            sputc(s, '[');
            for (size_t i = 0; i < n->nkids; i++) {
                if (i)
                    sput(s, ", ");
                char *e = fmt_node(&n->kids[i], 0);
                sput(s, e);
                free(e);
            }
            sputc(s, ']');
            break;
        case A_TAB:
            if (n->nkeys == 0) {
                sput(s, "{}");
                break;
            }
            sput(s, "{ ");
            for (size_t i = 0; i < n->nkeys; i++) {
                if (i)
                    sput(s, ", ");
                bin_raw(s, &n->keys[i]);
                sput(s, " = ");
                char *e = fmt_node(&n->kids[i], 0);
                sput(s, e);
                free(e);
            }
            sput(s, " }");
            break;
        case A_FUN:
            sput(s, "fun(");
            put_params(s, n);
            sput(s, ") -> ");
            {
                char *r = fmt_ty(&n->ty);
                sput(s, r);
                free(r);
            }
            sput(s, " = ");
            {
                char *b = fmt_node(n->a, 1);
                sput(s, b);
                free(b);
            }
            *prec = 1;
            break;
        case A_IF: {
            char *c = fmt_node(n->a, 1), *t = fmt_node(n->b, 1), *e = fmt_node(n->c, 1);
            sput(s, "if ");
            sput(s, c);
            sput(s, " then ");
            sput(s, t);
            sput(s, " else ");
            sput(s, e);
            free(c);
            free(t);
            free(e);
            *prec = 1;
        } break;
        case A_TRY: {
            char *e = fmt_node(n->a, 1), *f = fmt_node(n->b, 1);
            sput(s, "try ");
            sput(s, e);
            sput(s, " else ");
            sput(s, f);
            free(e);
            free(f);
            *prec = 1;
        } break;
        case A_ERR: {
            char *e = fmt_node(n->a, 1);
            sput(s, "err ");
            sput(s, e);
            free(e);
            *prec = 1;
        } break;
        case A_IS: {
            char *e = fmt_node(n->a, 2);
            sput(s, e);
            sput(s, " is ");
            char *t = fmt_ty(&n->ty);
            sput(s, t);
            free(e);
            free(t);
            *prec = 1;
        } break;
        case A_AS: {
            sputc(s, '(');
            char *e = fmt_node(n->a, 0);
            sput(s, e);
            sput(s, " : ");
            char *t = fmt_ty(&n->ty);
            sput(s, t);
            sputc(s, ')');
            free(e);
            free(t);
        } break;
        case A_SEQ:
            sputc(s, '(');
            for (size_t i = 0; i < n->nkids; i++) {
                if (i)
                    sput(s, "; ");
                char *d = fmt_node(&n->kids[i], 0);
                sput(s, d);
                free(d);
            }
            sputc(s, ')');
            break;
        case A_LET:
            doc_prefix(s, n);
            if (n->is_pub)
                sput(s, "pub ");
            sput(s, "let ");
            bin_raw(s, &n->name);
            if (n->has_ty) {
                sput(s, ": ");
                char *t = fmt_ty(&n->ty);
                sput(s, t);
                free(t);
            }
            sput(s, " = ");
            {
                char *e = fmt_node(n->a, 1);
                sput(s, e);
                free(e);
            }
            *prec = 0;
            break;
        case A_TYP:
            doc_prefix(s, n);
            if (n->is_pub)
                sput(s, "pub ");
            sput(s, "typ ");
            bin_raw(s, &n->name);
            sput(s, " = ");
            {
                char *t = fmt_ty(&n->ty);
                sput(s, t);
                free(t);
            }
            // A bare alias carries the always-true predicate the parser
            // synthesizes for it; print it back as the alias it was written as,
            // not as the desugaring. (Mirrors is_always_true in src/print.rs.)
            if (!is_always_true(n->a, &n->ty)) {
                sput(s, " where ");
                char *p = fmt_node(n->a, 1);
                sput(s, p);
                free(p);
            }
            *prec = 0;
            break;
        case A_USE:
            doc_prefix(s, n);
            sput(s, "use ");
            bin_raw(s, &n->name);
            if (n->has_url) {
                sput(s, " = ");
                fmt_u8s(s, bin_bytes(&n->url), n->url.len);
            }
            *prec = 0;
            break;
    }
    (void)buf;
}

char *fmt_program(const Node *ds, size_t n) {
    Str s = {0};
    for (size_t i = 0; i < n; i++) {
        char *d = fmt_node(&ds[i], 0);
        sput(&s, d);
        free(d);
        sput(&s, ";\n"); // `;` terminates each declaration
    }
    if (!s.p) {
        s.p = malloc(1);
        s.p[0] = 0;
    }
    return s.p;
}
