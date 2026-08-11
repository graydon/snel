// Static type checker (mirrors src/check.rs). Infers a type per expression as
// an optional Ty (unknown = permissive), enforces: names resolve to earlier
// bindings (no recursion), calls are arity-correct, and every application is
// type-correct (callee is a function, each argument a subtype of its
// parameter). The application rule makes self-application untypeable, so
// evaluation terminates. Exact ascription/parameter conformance stays at the
// runtime coercion, as in the Rust reference.
#include "snel.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

Ty union_of_pub(Ty *parts, size_t n); // ast.c: flatten + dedup a union

// optional type: known ? ty : unknown
typedef struct {
    bool known;
    Ty ty;
} CT;
static CT ct_none(void) {
    CT c;
    c.known = false;
    memset(&c.ty, 0, sizeof c.ty);
    return c;
}
static CT ct(Ty t) {
    CT c;
    c.known = true;
    c.ty = t;
    return c;
}

typedef struct {
    Bin *vn;
    CT *vt;
    size_t nv, cv; // term name -> type
    Bin *tn;
    Ty *tb;
    size_t nt, ct; // type name -> base
    char *eb;
    size_t el;              // error buffer
    const Bin *imp_names;   // `use` unit name -> interface type
    const Ty *imp_tys;      // (parallel arrays, nimp entries)
    size_t nimp;
} Scope;

// the most recent check error, for callers that want the raw position/message
// (the language server); the CLI keeps using the formatted string in `eb`.
static uint32_t g_last_span;
static char g_last_msg[256];
uint32_t check_last_span(void) {
    return g_last_span;
}
const char *check_last_msg(void) {
    return g_last_msg;
}

static bool cfail(Scope *s, uint32_t sp, const char *msg) {
    g_last_span = sp;
    snprintf(g_last_msg, sizeof g_last_msg, "%s", msg);
    snprintf(s->eb, s->el, "check error (line %u): %s", err_line(sp), msg);
    return false;
}

static void push_var(Scope *s, Bin name, CT t) {
    if (s->nv == s->cv) {
        s->cv = s->cv ? s->cv * 2 : 16;
        s->vn = realloc(s->vn, s->cv * sizeof(Bin));
        s->vt = realloc(s->vt, s->cv * sizeof(CT));
    }
    s->vn[s->nv] = name;
    s->vt[s->nv] = t;
    s->nv++;
}
static void push_typ(Scope *s, Bin name, Ty base) {
    if (s->nt == s->ct) {
        s->ct = s->ct ? s->ct * 2 : 16;
        s->tn = realloc(s->tn, s->ct * sizeof(Bin));
        s->tb = realloc(s->tb, s->ct * sizeof(Ty));
    }
    s->tn[s->nt] = name;
    s->tb[s->nt] = base;
    s->nt++;
}

static bool is_builtin_type(const Bin *n) {
    return (n->len == 3 && !memcmp(bin_bytes(n), "str", 3)) ||
           (n->len == 3 && !memcmp(bin_bytes(n), "sym", 3));
}

// ---------- types ----------

bool ty_eq(const Ty *a, const Ty *b) {
    if (a->k != b->k)
        return false;
    switch (a->k) {
        case T_NIL:
        case T_BIT:
        case T_I64:
        case T_F64:
        case T_U8:
            return true;
        case T_VEC:
            return ty_eq(&a->elem[0], &b->elem[0]);
        case T_UNION:
            if (a->n != b->n)
                return false;
            for (size_t i = 0; i < a->n; i++)
                if (!ty_eq(&a->elem[i], &b->elem[i]))
                    return false;
            return true;
        case T_FUN:
            if (a->n != b->n)
                return false;
            for (size_t i = 0; i < a->n; i++)
                if (!ty_eq(&a->elem[i], &b->elem[i]))
                    return false;
            return ty_eq(a->ret, b->ret);
        case T_TAB:
            if (a->n != b->n)
                return false;
            for (size_t i = 0; i < a->n; i++)
                if (!bin_eq(&a->fields[i], &b->fields[i]) || !ty_eq(&a->elem[i], &b->elem[i]))
                    return false;
            return true;
        case T_NAME:
            return bin_eq(&a->name, &b->name);
    }
    return false;
}

static Ty *ty_box(Ty t) {
    Ty *p = malloc(sizeof(Ty));
    *p = t;
    return p;
}
static Ty ty_u8vec(void) {
    Ty t;
    memset(&t, 0, sizeof t);
    t.k = T_VEC;
    t.n = 1;
    t.elem = calloc(1, sizeof(Ty));
    t.elem[0].k = T_U8;
    return t;
}

static bool resolve_base(Scope *s, const Bin *n, Ty *out) {
    if (is_builtin_type(n)) {
        *out = ty_u8vec();
        return true;
    }
    for (size_t i = s->nt; i-- > 0;)
        if (bin_eq(&s->tn[i], n)) {
            *out = s->tb[i];
            return true;
        }
    return false;
}

// Follow a chain of `typ` names down to the type underneath. Bounded, so a
// pathological alias that names itself cannot spin.
static bool deref_name(Scope *s, const Ty *t, Ty *out) {
    Ty cur = *t;
    for (int i = 0; i < 16; i++) {
        if (cur.k != T_NAME) {
            *out = cur;
            return true;
        }
        Ty base;
        if (!resolve_base(s, &cur.name, &base))
            return false;
        cur = base;
    }
    return false;
}

static bool sub(Scope *s, const Ty *a, const Ty *b) {
    if (ty_eq(a, b))
        return true;
    if (b->k == T_UNION) {
        for (size_t i = 0; i < b->n; i++)
            if (sub(s, a, &b->elem[i]))
                return true;
    }
    if (a->k == T_UNION) {
        for (size_t i = 0; i < a->n; i++)
            if (!sub(s, &a->elem[i], b))
                return false;
        return true;
    }
    // Unresolvable name rejects (check_ty proves annotated names resolve, so
    // this cannot fire for real programs; rejecting keeps recursion out).
    if (a->k == T_NAME) {
        Ty base;
        if (resolve_base(s, &a->name, &base))
            return sub(s, &base, b);
        return false;
    }
    if (b->k == T_NAME) {
        Ty base;
        if (resolve_base(s, &b->name, &base))
            return sub(s, a, &base);
        return false;
    }
    if (a->k == T_VEC && b->k == T_VEC)
        return sub(s, &a->elem[0], &b->elem[0]);
    if (a->k == T_TAB && b->k == T_TAB) {
        for (size_t i = 0; i < b->n; i++) {
            bool found = false;
            for (size_t j = 0; j < a->n; j++)
                if (bin_eq(&a->fields[j], &b->fields[i])) {
                    if (!sub(s, &a->elem[j], &b->elem[i]))
                        return false;
                    found = true;
                    break;
                }
            if (!found)
                return false;
        }
        return true;
    }
    if (a->k == T_FUN && b->k == T_FUN) {
        if (a->n != b->n)
            return false;
        for (size_t i = 0; i < a->n; i++)
            if (!sub(s, &b->elem[i], &a->elem[i]))
                return false;
        return sub(s, a->ret, b->ret);
    }
    return false;
}

static bool as_tab(Scope *s, const Ty *t, Ty *out) {
    if (t->k == T_TAB) {
        *out = *t;
        return true;
    }
    if (t->k == T_NAME) {
        Ty base;
        if (resolve_base(s, &t->name, &base))
            return as_tab(s, &base, out);
    }
    return false;
}

static bool is_vec_ty(Scope *s, const Ty *t) {
    if (t->k == T_VEC)
        return true;
    if (t->k == T_NAME) {
        if (is_builtin_type(&t->name))
            return true;
        Ty base;
        if (resolve_base(s, &t->name, &base))
            return is_vec_ty(s, &base);
    }
    return false;
}

static CT join(CT a, CT b) {
    if (a.known && b.known && ty_eq(&a.ty, &b.ty))
        return a;
    return ct_none();
}

// `if`/`try` arms: the result is the arms' common type — the same type if they
// agree, or the wider one when one refines/subtypes the other (so `pos`/`i64`
// join to `i64`). Two incompatible known types are a hard error; ascribe both
// arms to a union to opt in. One unknown arm stays gradual. Mirrors check.rs.
static bool branch_join(Scope *s, uint32_t sp, CT a, CT b, CT *out) {
    if (!a.known || !b.known) {
        *out = ct_none();
        return true;
    }
    if (ty_eq(&a.ty, &b.ty) || sub(s, &a.ty, &b.ty))
        *out = b;
    else if (sub(s, &b.ty, &a.ty))
        *out = a;
    else
        return cfail(s, sp,
                     "branches have incompatible types; ascribe both arms to a union if intended");
    return true;
}

static bool check_ty(Scope *s, const Ty *t, uint32_t sp) {
    switch (t->k) {
        case T_NAME:
            if (is_builtin_type(&t->name))
                return true;
            for (size_t i = 0; i < s->nt; i++)
                if (bin_eq(&s->tn[i], &t->name))
                    return true;
            return cfail(s, sp, "unknown type");
        case T_VEC:
            return check_ty(s, &t->elem[0], sp);
        case T_UNION:
            for (size_t i = 0; i < t->n; i++)
                if (!check_ty(s, &t->elem[i], sp))
                    return false;
            return true;
        case T_TAB:
            for (size_t i = 0; i < t->n; i++)
                if (!check_ty(s, &t->elem[i], sp))
                    return false;
            return true;
        case T_FUN:
            for (size_t i = 0; i < t->n; i++)
                if (!check_ty(s, &t->elem[i], sp))
                    return false;
            return check_ty(s, t->ret, sp);
        default:
            return true;
    }
}

int op_arity(int op);
int op_arity(int op) {
    switch (op) {
        case OP_ENV:
            return 0;
        case OP_NEG:
        case OP_ABS:
        case OP_ITOF:
        case OP_FTOI:
        case OP_SQRT:
        case OP_FLOOR:
        case OP_CEIL:
        case OP_SIGN:
        case OP_ORD:
        case OP_CHR:
        case OP_NOT:
        case OP_LEN:
        case OP_IOTA:
        case OP_GRADE:
        case OP_SUM:
        case OP_PROD:
        case OP_MIN:
        case OP_MAX:
        case OP_ISNIL:
        case OP_ALL:
        case OP_ANY:
        case OP_REV:
        case OP_FIRST:
        case OP_LAST:
        case OP_WHICH:
        case OP_DISTINCT:
        case OP_REFLECT:
        case OP_SHOW:
        case OP_ENCODE:
        case OP_DECODE:
        case OP_PARSE:
        case OP_UNPARSE:
            return 1;
        case OP_FOLD:
        case OP_SCAN:
        case OP_MAP2:
        case OP_SELECT:
        case OP_SCATTER:
        case OP_SHIFT:
            return 3;
        case OP_SUMS:
        case OP_PRODS:
        case OP_RUNS:
        case OP_TOJSON:
        case OP_FROMJSON:
        case OP_TOCSV:
        case OP_FROMCSV:
            return 1;
        default:
            return 2; // incl. member/matches/partition/windows
    }
}

// Elementwise typing (mirrors src/check.rs): a scalar op lifted over `[·]`
// (broadcast) and `·?` (nil-propagation). Precise on monomorphic and nil cases;
// a genuine multi-case union operand yields unknown (gradual).
typedef enum { SH_SCALAR, SH_VEC, SH_UNKNOWN } Shape;

static Shape shape(Scope *s, const Ty *t) {
    switch (t->k) {
        case T_VEC:
            return SH_VEC;
        case T_NIL:
        case T_BIT:
        case T_I64:
        case T_F64:
        case T_U8:
            return SH_SCALAR;
        case T_UNION: {
            bool all_sc = true, all_vec = true;
            for (size_t i = 0; i < t->n; i++) {
                Shape sh = shape(s, &t->elem[i]);
                if (sh != SH_SCALAR)
                    all_sc = false;
                if (sh != SH_VEC)
                    all_vec = false;
            }
            return all_sc ? SH_SCALAR : all_vec ? SH_VEC : SH_UNKNOWN;
        }
        case T_NAME: {
            Ty base;
            if (resolve_base(s, &t->name, &base))
                return shape(s, &base);
            return SH_UNKNOWN;
        }
        default:
            return SH_UNKNOWN;
    }
}

static Ty mk_scalar(TKind k) {
    Ty t;
    memset(&t, 0, sizeof t);
    t.k = k;
    return t;
}

// A named type is resolved to its base first, so arithmetic and the numeric
// reductions see through a `typ` alias over a numeric base (mirrors check.rs).
static bool peel_scalar_num(Scope *s, const Ty *t, Ty *base, bool *nil) {
    if (t->k == T_I64 || t->k == T_F64) {
        *base = mk_scalar(t->k);
        *nil = false;
        return true;
    }
    if (t->k == T_UNION && t->n == 2) {
        const Ty *a = &t->elem[0], *b = &t->elem[1];
        if ((a->k == T_I64 || a->k == T_F64) && b->k == T_NIL) {
            *base = mk_scalar(a->k);
            *nil = true;
            return true;
        }
        if (a->k == T_NIL && (b->k == T_I64 || b->k == T_F64)) {
            *base = mk_scalar(b->k);
            *nil = true;
            return true;
        }
    }
    if (t->k == T_NAME) {
        Ty b;
        if (resolve_base(s, &t->name, &b))
            return peel_scalar_num(s, &b, base, nil);
    }
    return false;
}
static bool peel_num(Scope *s, const Ty *t, Ty *base, bool *is_vec, bool *nil) {
    if (t->k == T_VEC) {
        *is_vec = true;
        return peel_scalar_num(s, &t->elem[0], base, nil);
    }
    if (t->k == T_NAME) {
        Ty b;
        if (resolve_base(s, &t->name, &b))
            return peel_num(s, &b, base, is_vec, nil);
        return false;
    }
    *is_vec = false;
    return peel_scalar_num(s, t, base, nil);
}

static Ty recompose(Ty base, bool is_vec, bool nil) {
    Ty elem = base;
    if (nil) {
        Ty u;
        memset(&u, 0, sizeof u);
        u.k = T_UNION;
        u.n = 2;
        u.elem = malloc(2 * sizeof(Ty));
        u.elem[0] = base;
        u.elem[1] = mk_scalar(T_NIL);
        elem = u;
    }
    if (is_vec) {
        Ty v;
        memset(&v, 0, sizeof v);
        v.k = T_VEC;
        v.n = 1;
        v.elem = ty_box(elem);
        return v;
    }
    return elem;
}

static CT num_binop(Scope *s, CT a, CT b) {
    if (!a.known || !b.known)
        return ct_none();
    Ty ba, bb;
    bool va, vb, na, nb;
    if (!peel_num(s, &a.ty, &ba, &va, &na) || !peel_num(s, &b.ty, &bb, &vb, &nb))
        return ct_none();
    if (ba.k != bb.k)
        return ct_none();
    return ct(recompose(ba, va || vb, na || nb));
}

static CT bit_result(Scope *s, CT *args, size_t na) {
    bool is_vec = false;
    for (size_t i = 0; i < na; i++) {
        if (!args[i].known)
            return ct_none();
        Shape sh = shape(s, &args[i].ty);
        if (sh == SH_UNKNOWN)
            return ct_none();
        if (sh == SH_VEC)
            is_vec = true;
    }
    return ct(recompose(mk_scalar(T_BIT), is_vec, false));
}

static Ty wrap_vec(Ty e) {
    Ty v;
    memset(&v, 0, sizeof v);
    v.k = T_VEC;
    v.n = 1;
    v.elem = ty_box(e);
    return v;
}
static CT as_vec_ct(CT t) {
    return (t.known && t.ty.k == T_VEC) ? t : ct_none();
}
static CT vec_elem_ct(CT t) {
    return (t.known && t.ty.k == T_VEC) ? ct(t.ty.elem[0]) : ct_none();
}

static CT builtin_result(Scope *s, int op, CT *args, size_t na) {
    switch (op) {
        case OP_ADD:
        case OP_SUB:
        case OP_MUL:
        case OP_DIV:
        case OP_REM:
            return num_binop(s, args[0], args[1]);
        case OP_NEG:
        case OP_ABS:
        case OP_SIGN: {
            if (!args[0].known)
                return ct_none();
            Ty b;
            bool v, n;
            if (!peel_num(s, &args[0].ty, &b, &v, &n))
                return ct_none();
            return ct(recompose(b, v, n));
        }
        case OP_ITOF: {
            if (!args[0].known)
                return ct_none();
            Ty b;
            bool v, n;
            if (!peel_num(s, &args[0].ty, &b, &v, &n) || b.k != T_I64)
                return ct_none();
            return ct(recompose(mk_scalar(T_F64), v, n));
        }
        case OP_FTOI:
        case OP_SQRT:
        case OP_FLOOR:
        case OP_CEIL: {
            if (!args[0].known)
                return ct_none();
            Ty b;
            bool v, n;
            if (!peel_num(s, &args[0].ty, &b, &v, &n) || b.k != T_F64)
                return ct_none();
            return ct(recompose(mk_scalar(op == OP_FTOI ? T_I64 : T_F64), v, n));
        }
        // sum/prod reduce a numeric vector to its scalar base (nils dropped, so
        // never nil); min/max reduce to an element (like first/last).
        case OP_SUM:
        case OP_PROD: {
            if (!args[0].known)
                return ct_none();
            Ty b;
            bool v, n;
            if (!peel_num(s, &args[0].ty, &b, &v, &n) || !v)
                return ct_none();
            return ct(b);
        }
        case OP_MIN:
        case OP_MAX:
            return vec_elem_ct(args[0]);
        // cat concatenates two vectors; its elements are the union of the inputs'
        case OP_CAT: {
            if (!args[0].known || !args[1].known || args[0].ty.k != T_VEC ||
                args[1].ty.k != T_VEC)
                return ct_none();
            Ty parts[2] = {args[0].ty.elem[0], args[1].ty.elem[0]};
            return ct(wrap_vec(union_of_pub(parts, 2)));
        }
        case OP_FIND: { // position or nil
            Ty parts[2] = {mk_scalar(T_I64), mk_scalar(T_NIL)};
            return ct(union_of_pub(parts, 2));
        }
        case OP_EQ:
        case OP_NE:
        case OP_LT:
        case OP_LE:
        case OP_GT:
        case OP_GE:
        case OP_AND:
        case OP_OR:
        case OP_NOT:
        case OP_ISNIL:
            return bit_result(s, args, na);
        case OP_ALL:
        case OP_ANY:
        case OP_IN:
            return ct(mk_scalar(T_BIT));
        case OP_LEN:
            return ct(mk_scalar(T_I64));
        case OP_IOTA:
        case OP_GRADE:
        case OP_WHICH:
            return ct(wrap_vec(mk_scalar(T_I64)));
        case OP_REV:
        case OP_DISTINCT:
            return as_vec_ct(args[0]);
        case OP_TAKE:
        case OP_DROP:
        case OP_FILTER:
            return as_vec_ct(args[1]);
        case OP_FIRST:
        case OP_LAST:
            return vec_elem_ct(args[0]);
        // map/map2/fold/scan/filter are typed in check_app (fn_result), which
        // sees the function-argument node so a bare builtin peels precisely
        case OP_SELECT: {
            CT a = args[1], b = args[2];
            if (args[0].known && args[0].ty.k == T_BIT)
                return join(a, b); // scalar-bit: pick a whole branch
            CT ea = a.known ? ct(a.ty.k == T_VEC ? a.ty.elem[0] : a.ty) : ct_none();
            CT eb = b.known ? ct(b.ty.k == T_VEC ? b.ty.elem[0] : b.ty) : ct_none();
            CT e = join(ea, eb);
            return e.known ? ct(wrap_vec(e.ty)) : ct_none();
        }
        case OP_SPLIT:
            return ct(wrap_vec(ty_u8vec()));
        case OP_JOIN:
        case OP_SHOW:
        case OP_ENCODE:
        case OP_UNPARSE:
        case OP_TOJSON:
        case OP_TOCSV:
            return ct(ty_u8vec());
        // fromjson/fromcsv are shaped by their input data -> gradual (default)
        case OP_AT:
            return vec_elem_ct(args[1]); // at(i, v): element of the vector
        case OP_REP:
            return args[1].known ? ct(wrap_vec(args[1].ty)) : ct_none();
        case OP_SCATTER: // scatter(idx, vals, base): the base vector
        case OP_SHIFT:   // shift(k, fill, v): the shifted vector
            return as_vec_ct(args[2]);
        case OP_SUMS:
        case OP_PRODS:
            return as_vec_ct(args[0]);
        // sequence analysis: classify/locate/edges -> [bit]; cut/window -> [[T]]
        case OP_MEMBER:
        case OP_MATCHES:
        case OP_RUNS:
            return ct(wrap_vec(mk_scalar(T_BIT)));
        case OP_PARTITION:
        case OP_WINDOWS: {
            CT vt = as_vec_ct(args[1]);
            return vt.known ? ct(wrap_vec(vt.ty)) : ct_none();
        }
        default:
            return ct_none();
    }
}

static bool infer(Scope *s, const Node *n, CT *out);

static bool check_decl(Scope *s, const Node *d, CT *out) {
    switch (d->k) {
        case A_LET: {
            CT et;
            if (!infer(s, d->a, &et))
                return false; // RHS sees only earlier names
            CT bound = et;
            if (d->has_ty) {
                if (!check_ty(s, &d->ty, d->lo))
                    return false;
                bound = ct(d->ty);
            }
            push_var(s, d->name, bound);
            *out = bound;
            return true;
        }
        case A_TYP: {
            if (!check_ty(s, &d->ty, d->lo))
                return false;
            CT pt;
            if (!infer(s, d->a, &pt))
                return false;
            push_typ(s, d->name, d->ty);
            *out = ct_none();
            return true;
        }
        case A_USE: {
            // a `use`d name gets the imported unit's interface type, if resolved
            CT u = ct_none();
            for (size_t i = 0; i < s->nimp; i++)
                if (bin_eq(&s->imp_names[i], &d->name)) {
                    u = ct(s->imp_tys[i]);
                    break;
                }
            push_var(s, d->name, u);
            *out = ct_none();
            return true;
        }
        default:
            return infer(s, d, out);
    }
}

// result type of applying a function-argument (of a higher-order builtin) to
// args of the given types: a bare builtin peels like a direct call
// (builtin_result, arity-checked), else its declared return type. Mirrors
// src/check.rs fn_result.
static bool fn_result(Scope *s, const Node *fnode, CT fty, CT *arg_tys, size_t na, CT *out) {
    if (fnode->k == A_VAR) {
        int op = op_by_name(bin_bytes(&fnode->name), fnode->name.len);
        if (op >= 0) {
            if ((size_t)op_arity(op) != na)
                return cfail(s, fnode->lo, "wrong builtin arity");
            *out = builtin_result(s, op, arg_tys, na);
            return true;
        }
    }
    // a closure (or any fun value): checked like a direct call — arity, then
    // each element type against the corresponding parameter type.
    if (fty.known && fty.ty.k == T_FUN) {
        if (fty.ty.n != na)
            return cfail(s, fnode->lo, "wrong number of arguments");
        for (size_t i = 0; i < na; i++)
            if (arg_tys[i].known && !sub(s, &arg_tys[i].ty, &fty.ty.elem[i]))
                return cfail(s, fnode->lo, "argument type mismatch");
        *out = ct(*fty.ty.ret);
        return true;
    }
    *out = ct_none(); // a gradual function value
    return true;
}

static bool check_app(Scope *s, const Node *n, CT *out) {
    const Node *f = n->a;
    if (f->k == A_VAR) {
        int op = op_by_name(bin_bytes(&f->name), f->name.len);
        if (op >= 0) {
            if ((int)n->nkids != op_arity(op))
                return cfail(s, n->lo, "wrong builtin arity");
            CT *ats = malloc((n->nkids ? n->nkids : 1) * sizeof(CT));
            for (size_t i = 0; i < n->nkids; i++)
                if (!infer(s, &n->kids[i], &ats[i])) {
                    free(ats);
                    return false;
                }
            // higher-order ops apply their function argument to the elements of
            // their data argument(s); peel it there (mirrors check.rs check_app)
            CT res;
            bool handled = true, ok = true;
            if (op == OP_MAP) {
                CT e = vec_elem_ct(ats[1]), r;
                ok = fn_result(s, &n->kids[0], ats[0], &e, 1, &r);
                res = (ok && r.known) ? ct(wrap_vec(r.ty)) : ct_none();
            } else if (op == OP_MAP2) {
                CT e[2] = {vec_elem_ct(ats[1]), vec_elem_ct(ats[2])}, r;
                ok = fn_result(s, &n->kids[0], ats[0], e, 2, &r);
                res = (ok && r.known) ? ct(wrap_vec(r.ty)) : ct_none();
            } else if (op == OP_SCAN) {
                CT e[2] = {ats[1], vec_elem_ct(ats[2])}, r;
                ok = fn_result(s, &n->kids[0], ats[0], e, 2, &r);
                res = (ok && r.known) ? ct(wrap_vec(r.ty)) : ct_none();
            } else if (op == OP_FOLD) {
                CT e[2] = {ats[1], vec_elem_ct(ats[2])};
                ok = fn_result(s, &n->kids[0], ats[0], e, 2, &res);
            } else if (op == OP_FILTER) {
                CT e = vec_elem_ct(ats[1]), r;
                ok = fn_result(s, &n->kids[0], ats[0], &e, 1, &r); // arity-check predicate
                res = as_vec_ct(ats[1]);
            } else {
                handled = false;
            }
            if (!ok) {
                free(ats);
                return false;
            }
            *out = handled ? res : builtin_result(s, op, ats, n->nkids);
            free(ats);
            return true;
        }
    }
    CT ft;
    if (!infer(s, f, &ft))
        return false;
    // a `typ` alias over a function type is callable as that function type
    if (ft.known && ft.ty.k == T_NAME) {
        Ty base;
        if (deref_name(s, &ft.ty, &base))
            ft.ty = base;
        else
            ft = ct_none();
    }
    CT *ats = malloc((n->nkids ? n->nkids : 1) * sizeof(CT));
    for (size_t i = 0; i < n->nkids; i++)
        if (!infer(s, &n->kids[i], &ats[i])) {
            free(ats);
            return false;
        }
    if (!ft.known) {
        free(ats);
        *out = ct_none();
        return true;
    }
    if (ft.ty.k != T_FUN) {
        free(ats);
        return cfail(s, n->lo, "cannot call a non-function");
    }
    if (n->nkids != ft.ty.n) {
        free(ats);
        return cfail(s, n->lo, "wrong number of arguments");
    }
    for (size_t i = 0; i < n->nkids; i++)
        if (ats[i].known && !sub(s, &ats[i].ty, &ft.ty.elem[i])) {
            free(ats);
            return cfail(s, n->kids[i].lo, "argument type mismatch");
        }
    Ty ret = *ft.ty.ret;
    free(ats);
    *out = ct(ret);
    return true;
}

static bool infer(Scope *s, const Node *n, CT *out) {
    switch (n->k) {
        case A_LIT:
            *out = ct(val_ty(&n->lit));
            return true;
        case A_VAR: {
            // a builtin used as a first-class value is gradually typed (a direct
            // call is still typed precisely, in check_app)
            if (op_by_name(bin_bytes(&n->name), n->name.len) >= 0) {
                *out = ct_none();
                return true;
            }
            for (size_t i = s->nv; i-- > 0;)
                if (bin_eq(&s->vn[i], &n->name)) {
                    *out = s->vt[i];
                    return true;
                }
            {
                char m[128];
                snprintf(m, sizeof m, "unbound name `%.*s`", (int)n->name.len,
                         bin_bytes(&n->name));
                return cfail(s, n->lo, m);
            }
        }
        case A_PROJ: {
            CT e;
            if (!infer(s, n->a, &e))
                return false;
            if (!e.known) {
                *out = ct_none();
                return true;
            }
            Ty tab;
            if (!as_tab(s, &e.ty, &tab))
                return cfail(s, n->lo, "cannot project from non-record");
            for (size_t i = 0; i < tab.n; i++)
                if (bin_eq(&tab.fields[i], &n->name)) {
                    *out = ct(tab.elem[i]);
                    return true;
                }
            return cfail(s, n->lo, "record has no such field");
        }
        case A_IDX: {
            CT e;
            if (!infer(s, n->a, &e))
                return false;
            CT i;
            if (!infer(s, n->b, &i))
                return false;
            // A `typ` name indexes as whatever it names — but the *result* is the
            // base type, not the name: indexing need not preserve a refinement
            // (a slice of a `str` need not be valid UTF-8).
            if (e.known && e.ty.k == T_NAME) {
                Ty base;
                if (deref_name(s, &e.ty, &base))
                    e.ty = base;
                else
                    e = ct_none();
            }
            if (!e.known || e.ty.k == T_VEC || e.ty.k == T_TAB) {
                *out = e;
                return true;
            }
            return cfail(s, n->lo, "cannot index a non-vector/record");
        }
        case A_APP:
            return check_app(s, n, out);
        case A_VEC: {
            if (n->nkids == 0) {
                *out = ct_none();
                return true;
            }
            // all elements known: element type is their union (a single case if
            // they agree), matching the column the value builds. Infer every
            // element (so element errors surface); pre-dedup structurally to keep
            // the parts array bounded before union_of_pub (mirrors check.rs).
            Ty parts[64];
            size_t np = 0;
            bool all_known = true;
            for (size_t i = 0; i < n->nkids; i++) {
                CT e;
                if (!infer(s, &n->kids[i], &e))
                    return false;
                if (!e.known) {
                    all_known = false;
                    continue;
                }
                bool dup = false;
                for (size_t j = 0; j < np; j++)
                    if (ty_eq(&parts[j], &e.ty)) {
                        dup = true;
                        break;
                    }
                if (!dup && np < 64)
                    parts[np++] = e.ty;
            }
            if (!all_known) {
                *out = ct_none();
                return true;
            }
            *out = ct(wrap_vec(union_of_pub(parts, np)));
            return true;
        }
        case A_TAB: {
            Ty t;
            memset(&t, 0, sizeof t);
            t.k = T_TAB;
            t.n = n->nkids;
            t.fields = malloc((n->nkids ? n->nkids : 1) * sizeof(Bin));
            t.elem = malloc((n->nkids ? n->nkids : 1) * sizeof(Ty));
            bool known = true;
            for (size_t i = 0; i < n->nkids; i++) {
                CT e;
                if (!infer(s, &n->kids[i], &e))
                    return false;
                t.fields[i] = n->keys[i];
                if (e.known)
                    t.elem[i] = e.ty;
                else
                    known = false;
            }
            *out = known ? ct(t) : ct_none();
            return true;
        }
        case A_FUN: {
            for (size_t i = 0; i < n->nparams; i++)
                if (!check_ty(s, &n->ptypes[i], n->lo))
                    return false;
            if (!check_ty(s, &n->ty, n->lo))
                return false;
            size_t depth = s->nv;
            for (size_t i = 0; i < n->nparams; i++)
                push_var(s, n->params[i], ct(n->ptypes[i]));
            CT body;
            if (!infer(s, n->a, &body))
                return false;
            s->nv = depth;
            if (body.known && !sub(s, &body.ty, &n->ty))
                // point at the body, not at the `fun` keyword (mirrors src/check.rs)
                return cfail(s, n->a->lo, "body type does not match declared return");
            Ty ft;
            memset(&ft, 0, sizeof ft);
            ft.k = T_FUN;
            ft.n = n->nparams;
            ft.elem = malloc((n->nparams ? n->nparams : 1) * sizeof(Ty));
            for (size_t i = 0; i < n->nparams; i++)
                ft.elem[i] = n->ptypes[i];
            ft.ret = ty_box(n->ty);
            *out = ct(ft);
            return true;
        }
        case A_IF: {
            CT c;
            if (!infer(s, n->a, &c))
                return false;
            CT a;
            if (!infer(s, n->b, &a))
                return false;
            CT b;
            if (!infer(s, n->c, &b))
                return false;
            if (c.known && c.ty.k != T_BIT)
                return cfail(s, n->lo,
                             "if condition must be a scalar bit (use select for a [bit] mask)");
            return branch_join(s, n->lo, a, b, out); // scalar condition: pick one branch
        }
        case A_TRY: {
            CT a;
            if (!infer(s, n->a, &a))
                return false;
            CT b;
            if (!infer(s, n->b, &b))
                return false;
            return branch_join(s, n->lo, a, b, out);
        }
        case A_ERR: {
            CT e;
            if (!infer(s, n->a, &e))
                return false;
            *out = ct_none();
            return true;
        }
        case A_IS: {
            CT e;
            if (!infer(s, n->a, &e))
                return false;
            if (!check_ty(s, &n->ty, n->lo))
                return false;
            if (e.known && e.ty.k == T_VEC && !is_vec_ty(s, &n->ty)) {
                Ty b;
                memset(&b, 0, sizeof b);
                b.k = T_BIT;
                Ty v;
                memset(&v, 0, sizeof v);
                v.k = T_VEC;
                v.n = 1;
                v.elem = ty_box(b);
                *out = ct(v);
            } else {
                Ty b;
                memset(&b, 0, sizeof b);
                b.k = T_BIT;
                *out = ct(b);
            }
            return true;
        }
        case A_AS: {
            CT e;
            if (!infer(s, n->a, &e))
                return false;
            if (!check_ty(s, &n->ty, n->lo))
                return false;
            *out = ct(n->ty);
            return true; // conformance enforced at runtime coercion
        }
        case A_SEQ: {
            size_t vd = s->nv, td = s->nt;
            CT last = ct_none();
            for (size_t i = 0; i < n->nkids; i++)
                if (!check_decl(s, &n->kids[i], &last))
                    return false;
            s->nv = vd;
            s->nt = td;
            *out = last;
            return true;
        }
        case A_LET:
        case A_TYP:
        case A_USE: {
            CT c;
            if (!check_decl(s, n, &c))
                return false;
            *out = ct_none();
            return true;
        }
    }
    return cfail(s, n->lo, "cannot type expression");
}

bool check_unit(Node *ds, size_t nds, const Bin *toplevel, size_t ntop, const Bin *imp_names,
                const Ty *imp_tys, size_t nimp, char *errbuf, size_t errlen) {
    Scope s;
    memset(&s, 0, sizeof s);
    s.eb = errbuf;
    s.el = errlen;
    s.imp_names = imp_names;
    s.imp_tys = imp_tys;
    s.nimp = nimp;
    for (size_t i = 0; i < ntop; i++)
        push_var(&s, toplevel[i], ct_none());
    for (size_t i = 0; i < nds; i++) {
        CT c;
        if (!check_decl(&s, &ds[i], &c))
            return false;
    }
    return true;
}
