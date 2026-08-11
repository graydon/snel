// Tree-walking evaluator. Mirrors src/eval.rs. Errors propagate as
// `false` + a SnelErr (no longjmp): `try` just re-evaluates the else branch,
// exactly like the Rust Result match. Values are immutable; buffers leak.
#include "snel.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

Ty union_of_pub(Ty *parts, size_t n);
bool ty_eq(const Ty *a, const Ty *b); // check.c: structural type equality
int op_arity(int op);                 // check.c: builtin argument count

struct Cx {
    Loader *loader;
    SnelErr err;
};

static bool eval(Cx *cx, Tab *env, const Node *n, Val *out);
static bool apply(Cx *cx, const Val *f, Val *args, size_t na, uint32_t sp, Val *out);
static bool coerce(Cx *cx, Tab *env, Val v, const Ty *t, uint32_t sp, Val *out);
static bool scalar_is(Cx *cx, Tab *env, const Val *v, const Ty *t, uint32_t sp, bool *out);

static bool efail(Cx *cx, uint32_t sp, const char *msg) {
    snprintf(cx->err.msg, sizeof cx->err.msg, "%s", msg);
    cx->err.span = sp;
    return false;
}

// ---------- free variables (closure capture) ----------
typedef struct {
    Bin *v;
    size_t n, cap;
} Syms;
static void syms_push(Syms *s, Bin b) {
    if (s->n == s->cap) {
        s->cap = s->cap ? s->cap * 2 : 8;
        s->v = realloc(s->v, s->cap * sizeof(Bin));
    }
    s->v[s->n++] = b;
}
static bool syms_has(Syms *s, const Bin *b) {
    for (size_t i = 0; i < s->n; i++)
        if (bin_eq(&s->v[i], b))
            return true;
    return false;
}

static void note(const Bin *x, Syms *bound, Syms *out) {
    if (op_by_name(bin_bytes(x), x->len) >= 0)
        return;
    if (syms_has(bound, x) || syms_has(out, x))
        return;
    syms_push(out, bin_clone(*x));
}
static void ty_names(const Ty *t, Syms *bound, Syms *out) {
    switch (t->k) {
        case T_NAME:
            note(&t->name, bound, out);
            break;
        case T_VEC:
            ty_names(&t->elem[0], bound, out);
            break;
        case T_UNION:
            for (size_t i = 0; i < t->n; i++)
                ty_names(&t->elem[i], bound, out);
            break;
        case T_TAB:
            for (size_t i = 0; i < t->n; i++)
                ty_names(&t->elem[i], bound, out);
            break;
        case T_FUN:
            for (size_t i = 0; i < t->n; i++)
                ty_names(&t->elem[i], bound, out);
            ty_names(t->ret, bound, out);
            break;
        default:
            break;
    }
}
static void walk(const Node *n, Syms *bound, Syms *out);
static void walk_seq(const Node *n, Syms *bound, Syms *out) {
    size_t depth = bound->n;
    for (size_t i = 0; i < n->nkids; i++) {
        const Node *d = &n->kids[i];
        if (d->k == A_LET) {
            if (d->has_ty)
                ty_names(&d->ty, bound, out);
            walk(d->a, bound, out);
            syms_push(bound, bin_clone(d->name));
        } else if (d->k == A_TYP) {
            ty_names(&d->ty, bound, out);
            walk(d->a, bound, out);
            syms_push(bound, bin_clone(d->name));
        } else if (d->k == A_USE) {
            syms_push(bound, bin_clone(d->name));
        } else
            walk(d, bound, out);
    }
    bound->n = depth;
}
static void walk(const Node *n, Syms *bound, Syms *out) {
    switch (n->k) {
        case A_LIT:
            break;
        case A_VAR:
            note(&n->name, bound, out);
            break;
        case A_PROJ:
        case A_ERR:
            walk(n->a, bound, out);
            break;
        case A_IDX:
        case A_TRY:
            walk(n->a, bound, out);
            walk(n->b, bound, out);
            break;
        case A_APP:
            walk(n->a, bound, out);
            for (size_t i = 0; i < n->nkids; i++)
                walk(&n->kids[i], bound, out);
            break;
        case A_VEC:
            for (size_t i = 0; i < n->nkids; i++)
                walk(&n->kids[i], bound, out);
            break;
        case A_TAB:
            for (size_t i = 0; i < n->nkids; i++)
                walk(&n->kids[i], bound, out);
            break;
        case A_FUN: {
            size_t d = bound->n;
            for (size_t i = 0; i < n->nparams; i++) {
                ty_names(&n->ptypes[i], bound, out);
                syms_push(bound, bin_clone(n->params[i]));
            }
            ty_names(&n->ty, bound, out);
            walk(n->a, bound, out);
            bound->n = d;
        } break;
        case A_IF:
            walk(n->a, bound, out);
            walk(n->b, bound, out);
            walk(n->c, bound, out);
            break;
        case A_IS:
        case A_AS:
            walk(n->a, bound, out);
            ty_names(&n->ty, bound, out);
            break;
        case A_SEQ:
            walk_seq(n, bound, out);
            break;
        case A_LET:
            if (n->has_ty)
                ty_names(&n->ty, bound, out);
            walk(n->a, bound, out);
            break;
        case A_TYP:
            ty_names(&n->ty, bound, out);
            walk(n->a, bound, out);
            break;
        case A_USE:
            break;
    }
}
static void free_vars(const Node *fun, Syms *out) {
    Syms bound = {0};
    for (size_t i = 0; i < fun->nparams; i++) {
        ty_names(&fun->ptypes[i], &bound, out);
        syms_push(&bound, bin_clone(fun->params[i]));
    }
    ty_names(&fun->ty, &bound, out);
    walk(fun->a, &bound, out);
}

// The type names a `typ` value's base refers to (nothing, for anything else).
// A `typ` evaluates to a tab of its base type and its predicate; that base may
// name other `typ`s, and those have to travel with it into a closure.
static void typ_deps(const Val *v, Syms *out) {
    if (v->k != V_TAB)
        return;
    Val *b = tab_get(v->u.tab, (const uint8_t *)"typ", 3);
    Val *p = tab_get(v->u.tab, (const uint8_t *)"pred", 4);
    Ty base;
    if (!b || !p || !val_to_ty(b, &base))
        return;
    Syms bound = {0};
    ty_names(&base, &bound, out); // `note` already dedupes against `out`
}

// ---------- decl step ----------
Val ty_to_val(const Ty *t);
bool op_sum(const Col *, Val *, SnelErr *);
bool op_minmax(const Col *, bool, Val *, SnelErr *);
Val op_grade(const Col *);
bool op_iota(int64_t, Val *, SnelErr *);
bool op_cat(const Val *, const Val *, Val *, SnelErr *);
bool op_group(Tab *, const uint8_t *, size_t, Val *, SnelErr *);
bool op_prod(const Col *, Val *, SnelErr *);
bool op_rev(const Val *, Val *, SnelErr *);
bool op_take(int64_t, const Val *, Val *, SnelErr *);
bool op_drop(int64_t, const Val *, Val *, SnelErr *);
bool op_first(const Val *, Val *, SnelErr *);
bool op_last(const Val *, Val *, SnelErr *);
bool op_which(const Val *, Val *, SnelErr *);
bool op_distinct(const Val *, Val *, SnelErr *);
bool op_contains(const Val *, const Val *, Val *, SnelErr *);
bool op_member(const Val *, const Val *, Val *, SnelErr *);
bool op_matches(const Val *, const Val *, Val *, SnelErr *);
bool op_runs(const Val *, Val *, SnelErr *);
bool op_partition(const Val *, const Val *, Val *, SnelErr *);
bool op_windows(int64_t, const Val *, Val *, SnelErr *);
bool op_tojson(const Val *, Val *, SnelErr *);
bool op_fromjson(const Val *, Val *, SnelErr *);
bool op_tocsv(const Val *, Val *, SnelErr *);
bool op_fromcsv(const Val *, Val *, SnelErr *);
bool op_all(const Val *, Val *, SnelErr *);
bool op_any(const Val *, Val *, SnelErr *);
bool op_at(const Val *, int64_t, Val *, SnelErr *);
bool op_rep(int64_t, const Val *, Val *, SnelErr *);
bool op_scatter(const Val *, const Val *, const Val *, Val *, SnelErr *);
bool op_shift(const Val *, int64_t, const Val *, Val *, SnelErr *);
bool op_sums(const Val *, Val *, SnelErr *);
bool op_prods(const Val *, Val *, SnelErr *);
static Val vvec(Col *c) {
    Val v;
    v.k = V_VEC;
    v.u.vec = c;
    return v;
}

static bool decl_step(Cx *cx, Tab **env, const Node *d, Val *out) {
    switch (d->k) {
        case A_LET: {
            Val v;
            if (!eval(cx, *env, d->a, &v))
                return false;
            if (d->has_ty) {
                Val cv;
                if (!coerce(cx, *env, v, &d->ty, d->lo, &cv))
                    return false;
                v = cv;
            }
            Tab *e2 = tab_clone(*env);
            tab_bind(e2, bin_clone(d->name), val_clone(v), d->has_doc ? &d->doc : NULL);
            *env = e2;
            *out = v;
            return true;
        }
        case A_TYP: {
            Val p;
            if (!eval(cx, *env, d->a, &p))
                return false;
            Tab *tt = tab_new();
            Bin kb = bin_str("typ");
            tab_bind(tt, kb, ty_to_val(&d->ty), NULL);
            Bin pb = bin_str("pred");
            tab_bind(tt, pb, p, NULL);
            Val v;
            v.k = V_TAB;
            v.u.tab = tt;
            Tab *e2 = tab_clone(*env);
            tab_bind(e2, bin_clone(d->name), val_clone(v), d->has_doc ? &d->doc : NULL);
            *env = e2;
            *out = v;
            return true;
        }
        case A_USE: {
            if (!cx->loader)
                return efail(cx, d->lo, "no unit loader");
            bool ok;
            Val v;
            if (d->has_url) {
                if (!cx->loader->load_url)
                    return efail(cx, d->lo, "remote units are not supported here");
                v = cx->loader->load_url(cx->loader, &d->name, &d->url, &ok, cx->err.msg,
                                         sizeof cx->err.msg);
            } else
                v = cx->loader->load(cx->loader, &d->name, &ok, cx->err.msg, sizeof cx->err.msg);
            if (!ok) {
                cx->err.span = d->lo;
                return false;
            }
            Tab *e2 = tab_clone(*env);
            tab_bind(e2, bin_clone(d->name), val_clone(v), d->has_doc ? &d->doc : NULL);
            *env = e2;
            *out = v;
            return true;
        }
        default:
            return eval(cx, *env, d, out);
    }
}

// ---------- type resolution & tests ----------
bool val_to_ty(const Val *v, Ty *out);
bool is_u8_col(const Col *c);
uint8_t *col_bytes(const Col *c, size_t *len);

// The two built-in refinement types the spec names. Native because str's utf8
// test can't be written loop-lessly. Returns -1 if name is a user type.
static bool builtin_type_c(const Bin *n) {
    return (n->len == 3 && !memcmp(bin_bytes(n), "str", 3)) ||
           (n->len == 3 && !memcmp(bin_bytes(n), "sym", 3));
}
// str/sym are refinements over [u8]. returns 0=no/1=yes/-1=not a builtin type.
static int native_refinement(const Bin *n, const Val *v) {
    if (!builtin_type_c(n))
        return -1;
    if (v->k != V_VEC || !is_u8_col(v->u.vec))
        return 0;
    size_t bn;
    uint8_t *b = col_bytes(v->u.vec, &bn);
    int r;
    if (!memcmp(bin_bytes(n), "str", 3))
        r = bin_is_utf8(b, bn) ? 1 : 0;
    else {
        Bin tmp = bin_new(b, bn);
        r = bin_is_ident(&tmp) ? 1 : 0;
        bin_drop(&tmp);
    }
    free(b);
    return r;
}
static bool resolve_typ(Cx *cx, Tab *env, const Bin *n, Ty *base, Val *pred, uint32_t sp);

// Does T denote a vector type (so `is` applies to the whole value)?
static bool is_vec_type(Cx *cx, Tab *env, const Ty *t, uint32_t sp, bool *out) {
    if (t->k == T_VEC) {
        *out = true;
        return true;
    }
    if (t->k == T_NAME && builtin_type_c(&t->name)) {
        *out = true;
        return true;
    } // str/sym = [u8]
    if (t->k == T_NAME) {
        Ty base;
        Val pred;
        if (!resolve_typ(cx, env, &t->name, &base, &pred, sp))
            return false;
        return is_vec_type(cx, env, &base, sp, out);
    }
    *out = false;
    return true;
}
static bool resolve_typ(Cx *cx, Tab *env, const Bin *n, Ty *base, Val *pred, uint32_t sp) {
    Val *tv = tab_get(env, bin_bytes(n), n->len);
    if (!tv || tv->k != V_TAB)
        return efail(cx, sp, "unbound type");
    Val *b = tab_get(tv->u.tab, (const uint8_t *)"typ", 3);
    Val *p = tab_get(tv->u.tab, (const uint8_t *)"pred", 4);
    if (!b || !p || !val_to_ty(b, base))
        return efail(cx, sp, "not a type");
    *pred = *p;
    return true;
}

// Structural subtyping (mirrors src/eval.rs subtype): width/depth-covariant
// records, contravariant-arg/covariant-result funs, named refinement below its
// base. Makes a function's signature part of its type, so `x(x)` is untypeable.
static bool subtype(Cx *cx, Tab *env, const Ty *a, const Ty *b, uint32_t sp, bool *out) {
    if (ty_eq(a, b)) { // structurally identical types (incl. named); mirrors Rust
        *out = true;
        return true;
    }
    if (b->k == T_UNION) {
        for (size_t i = 0; i < b->n; i++) {
            bool r;
            if (!subtype(cx, env, a, &b->elem[i], sp, &r))
                return false;
            if (r) {
                *out = true;
                return true;
            }
        }
    }
    if (a->k == T_UNION) {
        for (size_t i = 0; i < a->n; i++) {
            bool r;
            if (!subtype(cx, env, &a->elem[i], b, sp, &r))
                return false;
            if (!r) {
                *out = false;
                return true;
            }
        }
        *out = true;
        return true;
    }
    if (a->k == T_NAME) {
        Ty base;
        Val pred;
        if (builtin_type_c(&a->name)) {
            memset(&base, 0, sizeof base);
            base.k = T_VEC;
            base.n = 1;
            base.elem = calloc(1, sizeof(Ty));
            base.elem[0].k = T_U8;
        } else if (!resolve_typ(cx, env, &a->name, &base, &pred, sp))
            return false;
        return subtype(cx, env, &base, b, sp, out);
    }
    if (a->k == b->k) {
        switch (a->k) {
            case T_NIL:
            case T_BIT:
            case T_I64:
            case T_F64:
            case T_U8:
                *out = true;
                return true;
            case T_VEC:
                return subtype(cx, env, &a->elem[0], &b->elem[0], sp, out);
            case T_TAB:
                for (size_t i = 0; i < b->n; i++) {
                    bool found = false;
                    size_t j;
                    for (j = 0; j < a->n; j++)
                        if (a->fields[j].len == b->fields[i].len &&
                            !memcmp(bin_bytes(&a->fields[j]), bin_bytes(&b->fields[i]),
                                    b->fields[i].len)) {
                            found = true;
                            break;
                        }
                    if (!found) {
                        *out = false;
                        return true;
                    }
                    bool r;
                    if (!subtype(cx, env, &a->elem[j], &b->elem[i], sp, &r))
                        return false;
                    if (!r) {
                        *out = false;
                        return true;
                    }
                }
                *out = true;
                return true;
            case T_FUN:
                if (a->n != b->n) {
                    *out = false;
                    return true;
                }
                for (size_t i = 0; i < a->n; i++) {
                    bool r;
                    if (!subtype(cx, env, &b->elem[i], &a->elem[i], sp, &r))
                        return false;
                    if (!r) {
                        *out = false;
                        return true;
                    }
                }
                return subtype(cx, env, a->ret, b->ret, sp, out);
            default:
                break;
        }
    }
    *out = false;
    return true;
}

static bool scalar_is(Cx *cx, Tab *env, const Val *v, const Ty *t, uint32_t sp, bool *out) {
    switch (t->k) {
        case T_NIL:
            *out = v->k == V_NIL;
            return true;
        case T_BIT:
            *out = v->k == V_BIT;
            return true;
        case T_I64:
            *out = v->k == V_I64;
            return true;
        case T_F64:
            *out = v->k == V_F64;
            return true;
        case T_U8:
            *out = v->k == V_U8;
            return true;
        case T_TAB:
            *out = v->k == V_TAB;
            return true;
        case T_FUN: {
            if (v->k != V_FUN && v->k != V_PRIM) {
                *out = false;
                return true;
            }
            Ty vt = val_ty(v);
            return subtype(cx, env, &vt, t, sp, out);
        }
        case T_VEC:
            *out = v->k == V_VEC;
            return true;
        case T_UNION:
            for (size_t i = 0; i < t->n; i++) {
                bool r;
                if (!scalar_is(cx, env, v, &t->elem[i], sp, &r))
                    return false;
                if (r) {
                    *out = true;
                    return true;
                }
            }
            *out = false;
            return true;
        case T_NAME: {
            int nr = native_refinement(&t->name, v);
            if (nr >= 0) {
                *out = nr != 0;
                return true;
            }
            Ty base;
            Val pred;
            if (!resolve_typ(cx, env, &t->name, &base, &pred, sp))
                return false;
            bool r;
            if (!scalar_is(cx, env, v, &base, sp, &r))
                return false;
            if (!r) {
                *out = false;
                return true;
            }
            Val arg = val_clone(*v), res;
            if (!apply(cx, &pred, &arg, 1, sp, &res))
                return false;
            if (res.k != V_BIT)
                return efail(cx, sp, "predicate must return bit");
            *out = res.u.i != 0;
            return true;
        }
    }
    *out = false;
    return true;
}

// ---------- coercion ----------
bool coerce_col(const Col *, const Ty *, Col **, SnelErr *);
static bool contains_name(const Ty *t) {
    if (t->k == T_NAME)
        return true;
    if (t->k == T_UNION) {
        for (size_t i = 0; i < t->n; i++)
            if (contains_name(&t->elem[i]))
                return true;
    }
    if (t->k == T_VEC)
        return contains_name(&t->elem[0]);
    return false;
}
static bool strip_names(Cx *cx, Tab *env, const Ty *t, uint32_t sp, Ty *out) {
    if (t->k == T_NAME && builtin_type_c(&t->name)) {
        memset(out, 0, sizeof(Ty));
        out->k = T_VEC;
        out->n = 1;
        out->elem = calloc(1, sizeof(Ty));
        out->elem[0].k = T_U8;
        return true;
    } // str/sym represent as [u8]
    if (t->k == T_NAME) {
        Ty base;
        Val pred;
        if (!resolve_typ(cx, env, &t->name, &base, &pred, sp))
            return false;
        return strip_names(cx, env, &base, sp, out);
    }
    if (t->k == T_UNION) {
        Ty parts[64];
        for (size_t i = 0; i < t->n; i++)
            if (!strip_names(cx, env, &t->elem[i], sp, &parts[i]))
                return false;
        *out = union_of_pub(parts, t->n);
        return true;
    }
    if (t->k == T_VEC) {
        Ty *e = malloc(sizeof(Ty));
        if (!strip_names(cx, env, &t->elem[0], sp, e))
            return false;
        Ty r;
        memset(&r, 0, sizeof r);
        r.k = T_VEC;
        r.elem = e;
        r.n = 1;
        *out = r;
        return true;
    }
    *out = *t;
    return true;
}
static bool coerce(Cx *cx, Tab *env, Val v, const Ty *t, uint32_t sp, Val *out) {
    // fast path: a scalar already of the exact prim type needs no coercion
    switch (t->k) {
        case T_I64:
            if (v.k == V_I64) {
                *out = v;
                return true;
            }
            break;
        case T_F64:
            if (v.k == V_F64) {
                *out = v;
                return true;
            }
            break;
        case T_BIT:
            if (v.k == V_BIT) {
                *out = v;
                return true;
            }
            break;
        case T_U8:
            if (v.k == V_U8) {
                *out = v;
                return true;
            }
            break;
        case T_NIL:
            if (v.k == V_NIL) {
                *out = v;
                return true;
            }
            break;
        default:
            break;
    }
    if (t->k == T_NAME) {
        int nr = native_refinement(&t->name, &v);
        if (nr >= 0) {
            if (nr) {
                *out = v;
                return true;
            }
            return efail(cx, sp, "value fails type");
        }
        Ty base;
        Val pred;
        if (!resolve_typ(cx, env, &t->name, &base, &pred, sp))
            return false;
        Val cv;
        if (!coerce(cx, env, v, &base, sp, &cv))
            return false;
        Val arg = val_clone(cv), res;
        if (!apply(cx, &pred, &arg, 1, sp, &res))
            return false;
        if (res.k != V_BIT)
            return efail(cx, sp, "predicate must return bit");
        if (!res.u.i)
            return efail(cx, sp, "value fails predicate");
        *out = cv;
        return true;
    }
    if (t->k == T_VEC && v.k == V_VEC) {
        // coerce_col takes the ELEMENT type, so strip names on the element only.
        Ty rep;
        if (!strip_names(cx, env, &t->elem[0], sp, &rep))
            return false;
        Col *r;
        if (!coerce_col(v.u.vec, &rep, &r, &cx->err)) {
            cx->err.span = sp;
            return false;
        }
        if (contains_name(&t->elem[0])) {
            for (size_t i = 0; i < r->len; i++) {
                Val e = col_elem(r, i);
                if (e.k != V_NIL) {
                    bool ok;
                    if (!scalar_is(cx, env, &e, &t->elem[0], sp, &ok))
                        return false;
                    if (!ok)
                        return efail(cx, sp, "element fails type");
                }
                val_drop(e);
            }
        }
        val_drop(v); // coerce_col built a fresh column; the input is done with
        Val rv;
        rv.k = V_VEC;
        rv.u.vec = r;
        *out = rv;
        return true;
    }
    if (t->k == T_TAB && v.k == V_TAB) {
        Tab *o = tab_clone(v.u.tab);
        for (size_t i = 0; i < t->n; i++) {
            Val *fv = tab_get(v.u.tab, bin_bytes(&t->fields[i]), t->fields[i].len);
            if (!fv) {
                val_drop(v);
                tab_release(o);
                return efail(cx, sp, "missing field");
            }
            Val cv;
            if (!coerce(cx, env, val_clone(*fv), &t->elem[i], sp, &cv)) {
                val_drop(v);
                tab_release(o);
                return false;
            }
            tab_bind(o, bin_clone(t->fields[i]), cv, NULL);
        }
        val_drop(v); // the clone `o` holds its own refs
        Val rv;
        rv.k = V_TAB;
        rv.u.tab = o;
        *out = rv;
        return true;
    }
    if (t->k == T_UNION) {
        for (size_t i = 0; i < t->n; i++) {
            bool ok;
            if (!scalar_is(cx, env, &v, &t->elem[i], sp, &ok))
                return false;
            if (ok)
                return coerce(cx, env, v, &t->elem[i], sp, out);
        }
        return efail(cx, sp, "value fails type");
    }
    bool ok;
    if (!scalar_is(cx, env, &v, t, sp, &ok))
        return false;
    if (ok) {
        *out = v;
        return true;
    }
    return efail(cx, sp, "value fails type");
}

// ---------- builtins ----------
bool op_arith(int, Val, Val, Val *, SnelErr *);
bool op_unary(int, Val, Val *, SnelErr *);
bool op_compare(int, Val, Val, Val *, SnelErr *);
bool op_boolean(int, Val *, size_t, Val *, SnelErr *);
bool op_index(const Val *, const Val *, Val *, SnelErr *);
Val op_isnil(const Val *);
bool col_from_vals(Val *, size_t, Col **, SnelErr *);
bool is_u8_col(const Col *);
uint8_t *col_bytes(const Col *, size_t *);
bool op_find(const Val *, const Val *, Val *, SnelErr *);
bool op_split(const Val *, const Val *, Val *, SnelErr *);
bool op_join(const Val *, const Val *, Val *, SnelErr *);

Val ast_to_val(const Node *n);

// A closure reified as a tab: its code and captured environment as data.
static Val reflect_closure(const Clo *c) {
    Tab *params = tab_new();
    for (size_t i = 0; i < c->nparams; i++)
        tab_bind(params, bin_clone(c->params[i]), ty_to_val(&c->ptypes[i]), NULL);
    Tab *t = tab_new();
    Val pv;
    pv.k = V_TAB;
    pv.u.tab = params;
    tab_bind(t, bin_str("params"), pv, NULL);
    tab_bind(t, bin_str("ret"), ty_to_val(&c->ret), NULL);
    tab_bind(t, bin_str("body"), ast_to_val(c->body), NULL);
    Val ev;
    ev.k = V_TAB;
    ev.u.tab = tab_retain(c->env);
    tab_bind(t, bin_str("env"), ev, NULL);
    Val v;
    v.k = V_TAB;
    v.u.tab = t;
    return v;
}

static bool builtin(Cx *cx, Tab *env, int op, Val *args, size_t na, uint32_t sp, Val *out) {
    SnelErr *e = &cx->err;
    e->span = sp;
    switch (op) {
        case OP_ADD:
        case OP_SUB:
        case OP_MUL:
        case OP_DIV:
        case OP_REM:
            return op_arith(op, args[0], args[1], out, e) || (e->span = sp, false);
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
            return op_unary(op, args[0], out, e);
        case OP_EQ:
        case OP_NE:
        case OP_LT:
        case OP_LE:
        case OP_GT:
        case OP_GE:
            return op_compare(op, args[0], args[1], out, e);
        case OP_AND:
        case OP_OR:
            return op_boolean(op, args, 2, out, e);
        case OP_NOT:
            return op_boolean(op, args, 1, out, e);
        case OP_LEN:
            if (args[0].k != V_VEC)
                return efail(cx, sp, "len of non-vec");
            *out = vi64((int64_t)args[0].u.vec->len);
            return true;
        case OP_CAT:
            return op_cat(&args[0], &args[1], out, e);
        case OP_IOTA:
            if (args[0].k != V_I64)
                return efail(cx, sp, "iota needs an i64");
            return op_iota(args[0].u.i, out, e);
        case OP_GRADE:
            if (args[0].k != V_VEC)
                return efail(cx, sp, "grade needs a vec");
            *out = op_grade(args[0].u.vec);
            return true;
        case OP_SUM:
            if (args[0].k != V_VEC)
                return efail(cx, sp, "sum needs a vec");
            return op_sum(args[0].u.vec, out, e);
        case OP_PROD:
            if (args[0].k != V_VEC)
                return efail(cx, sp, "prod needs a vec");
            return op_prod(args[0].u.vec, out, e);
        case OP_MIN:
        case OP_MAX:
            if (args[0].k != V_VEC)
                return efail(cx, sp, "min/max needs a vec");
            return op_minmax(args[0].u.vec, op == OP_MIN, out, e);
        case OP_ISNIL:
            *out = op_isnil(&args[0]);
            return true;
        case OP_ALL:
            return op_all(&args[0], out, e);
        case OP_ANY:
            return op_any(&args[0], out, e);
        case OP_REV:
            return op_rev(&args[0], out, e);
        case OP_FIRST:
            return op_first(&args[0], out, e);
        case OP_LAST:
            return op_last(&args[0], out, e);
        case OP_WHICH:
            return op_which(&args[0], out, e);
        case OP_DISTINCT:
            return op_distinct(&args[0], out, e);
        case OP_TAKE:
            if (args[0].k != V_I64)
                return efail(cx, sp, "take needs (i64, vec)");
            return op_take(args[0].u.i, &args[1], out, e);
        case OP_DROP:
            if (args[0].k != V_I64)
                return efail(cx, sp, "drop needs (i64, vec)");
            return op_drop(args[0].u.i, &args[1], out, e);
        case OP_IN:
            return op_contains(&args[0], &args[1], out, e);
        case OP_AT:
            if (args[0].k != V_I64)
                return efail(cx, sp, "at needs (i64, vec)");
            return op_at(&args[1], args[0].u.i, out, e); // at(i, vec)
        case OP_REP:
            if (args[0].k != V_I64)
                return efail(cx, sp, "rep needs (i64, scalar)");
            return op_rep(args[0].u.i, &args[1], out, e);
        case OP_SCATTER:
            return op_scatter(&args[2], &args[0], &args[1], out, e); // scatter(idx, vals, base)
        case OP_SHIFT:
            if (args[0].k != V_I64)
                return efail(cx, sp, "shift needs (i64, fill, vec)");
            return op_shift(&args[2], args[0].u.i, &args[1], out, e); // shift(k, fill, vec)
        case OP_SUMS:
            return op_sums(&args[0], out, e);
        case OP_PRODS:
            return op_prods(&args[0], out, e);
        case OP_TOJSON:
            return op_tojson(&args[0], out, e);
        case OP_FROMJSON:
            return op_fromjson(&args[0], out, e);
        case OP_TOCSV:
            return op_tocsv(&args[0], out, e);
        case OP_FROMCSV:
            return op_fromcsv(&args[0], out, e);
        case OP_MEMBER:
            return op_member(&args[0], &args[1], out, e);
        case OP_MATCHES:
            return op_matches(&args[0], &args[1], out, e);
        case OP_RUNS:
            return op_runs(&args[0], out, e);
        case OP_PARTITION:
            return op_partition(&args[0], &args[1], out, e);
        case OP_WINDOWS:
            if (args[0].k != V_I64)
                return efail(cx, sp, "windows needs (i64, vec)");
            return op_windows(args[0].u.i, &args[1], out, e);
        case OP_MAP: {
            if (args[1].k != V_VEC)
                return efail(cx, sp, "map needs (fun, vec)");
            Col *c = args[1].u.vec;
            Val *outs = malloc((c->len ? c->len : 1) * sizeof(Val));
            for (size_t i = 0; i < c->len; i++) {
                Val a = col_elem(c, i);
                bool ok = apply(cx, &args[0], &a, 1, sp, &outs[i]);
                val_drop(a);
                if (!ok) {
                    free(outs);
                    return false;
                }
            }
            Col *r;
            bool ok = col_from_vals(outs, c->len, &r, e); // consumes the elements
            free(outs);
            if (!ok)
                return false;
            *out = vvec(r);
            return true;
        }
        case OP_MAP2: {
            if (args[1].k != V_VEC || args[2].k != V_VEC)
                return efail(cx, sp, "map2 needs (fun, vec, vec)");
            Col *ca = args[1].u.vec, *cb = args[2].u.vec;
            if (ca->len != cb->len)
                return efail(cx, sp, "map2 length mismatch");
            Val *outs = malloc((ca->len ? ca->len : 1) * sizeof(Val));
            for (size_t i = 0; i < ca->len; i++) {
                Val a[2] = {col_elem(ca, i), col_elem(cb, i)};
                bool ok = apply(cx, &args[0], a, 2, sp, &outs[i]);
                val_drop(a[0]);
                val_drop(a[1]);
                if (!ok) {
                    free(outs);
                    return false;
                }
            }
            Col *r;
            bool ok = col_from_vals(outs, ca->len, &r, e);
            free(outs);
            if (!ok)
                return false;
            *out = vvec(r);
            return true;
        }
        case OP_FOLD: {
            if (args[2].k != V_VEC)
                return efail(cx, sp, "fold needs (fun, init, vec)");
            Col *c = args[2].u.vec;
            Val acc = val_clone(args[1]);
            for (size_t i = 0; i < c->len; i++) {
                Val a[2] = {acc, col_elem(c, i)};
                Val r;
                bool ok = apply(cx, &args[0], a, 2, sp, &r);
                val_drop(a[0]); // the previous accumulator
                val_drop(a[1]); // the element
                if (!ok)
                    return false;
                acc = r;
            }
            *out = acc;
            return true;
        }
        case OP_SCAN: {
            if (args[2].k != V_VEC)
                return efail(cx, sp, "scan needs (fun, init, vec)");
            Col *c = args[2].u.vec;
            Val acc = val_clone(args[1]);
            Val *outs = malloc((c->len ? c->len : 1) * sizeof(Val));
            for (size_t i = 0; i < c->len; i++) {
                Val a[2] = {acc, col_elem(c, i)};
                Val r;
                bool ok = apply(cx, &args[0], a, 2, sp, &r);
                val_drop(a[0]);
                val_drop(a[1]);
                if (!ok) {
                    free(outs);
                    return false;
                }
                acc = r;
                outs[i] = val_clone(acc);
            }
            val_drop(acc);
            Col *rc;
            bool ok = col_from_vals(outs, c->len, &rc, e);
            free(outs);
            if (!ok)
                return false;
            *out = vvec(rc);
            return true;
        }
        case OP_FILTER: {
            if (args[1].k != V_VEC)
                return efail(cx, sp, "filter needs (fun, vec)");
            Col *c = args[1].u.vec;
            Val *kept = malloc((c->len ? c->len : 1) * sizeof(Val));
            size_t nk = 0;
            for (size_t i = 0; i < c->len; i++) {
                Val ev = col_elem(c, i);
                Val a = val_clone(ev);
                Val r;
                bool ok = apply(cx, &args[0], &a, 1, sp, &r);
                val_drop(a);
                if (!ok) {
                    val_drop(ev);
                    for (size_t j = 0; j < nk; j++)
                        val_drop(kept[j]);
                    free(kept);
                    return false;
                }
                if (r.k == V_BIT && r.u.i)
                    kept[nk++] = ev;
                else
                    val_drop(ev);
            }
            Col *rc;
            bool ok = col_from_vals(kept, nk, &rc, e);
            free(kept);
            if (!ok)
                return false;
            *out = vvec(rc);
            return true;
        }
        case OP_GROUP: {
            if (args[0].k != V_TAB || !(args[1].k == V_VEC && is_u8_col(args[1].u.vec)))
                return efail(cx, sp, "group needs (tab, 'key)");
            size_t kn;
            uint8_t *kb = col_bytes(args[1].u.vec, &kn);
            bool ok = op_group(args[0].u.tab, kb, kn, out, e);
            free(kb);
            return ok;
        }
        case OP_FIND:
            return op_find(&args[1], &args[0], out, e); // find(needle, haystack)
        case OP_SPLIT:
            return op_split(&args[1], &args[0], out, e); // split(sep, s)
        case OP_JOIN:
            return op_join(&args[0], &args[1], out, e);
        case OP_SELECT: {
            if (args[0].k == V_VEC)
                return op_select(args[0].u.vec, val_clone(args[1]), val_clone(args[2]), out, e);
            if (args[0].k == V_BIT) {
                *out = val_clone(args[0].u.i ? args[1] : args[2]);
                return true;
            }
            if (args[0].k == V_NIL) {
                *out = val_clone(args[2]);
                return true;
            }
            return efail(cx, sp, "select needs (bit or [bit], a, b)");
        }
        case OP_GET: {
            if (args[0].k != V_TAB || !(args[1].k == V_VEC && is_u8_col(args[1].u.vec)))
                return efail(cx, sp, "get needs (tab, key)");
            size_t kn;
            uint8_t *kb = col_bytes(args[1].u.vec, &kn);
            Val *v = tab_get(args[0].u.tab, kb, kn);
            free(kb);
            *out = v ? val_clone(*v) : vnil();
            return true;
        }
        case OP_ENV: {
            Val v;
            v.k = V_TAB;
            v.u.tab = tab_retain(env);
            *out = v;
            return true;
        }
        case OP_REFLECT:
            if (args[0].k != V_FUN)
                return efail(cx, sp, "reflect needs a fun");
            *out = reflect_closure(args[0].u.fun);
            return true;
        case OP_SHOW: {
            char *s = fmt_val(&args[0]);
            *out = vvec(col_u8s((const uint8_t *)s, strlen(s)));
            free(s);
            return true;
        }
        case OP_ENCODE: {
            uint8_t *buf = NULL;
            size_t len = 0, cap = 0;
            encode_val(&args[0], &buf, &len, &cap);
            *out = vvec(col_u8s(buf, len));
            free(buf);
            return true;
        }
        case OP_DECODE: {
            if (args[0].k != V_VEC || !is_u8_col(args[0].u.vec))
                return efail(cx, sp, "decode needs a [u8]");
            size_t n;
            uint8_t *b = col_bytes(args[0].u.vec, &n);
            size_t pos = 0;
            SnelErr de;
            memset(&de, 0, sizeof de);
            bool ok = decode_val(b, n, &pos, out, &de);
            free(b);
            if (!ok)
                return efail(cx, sp, de.msg);
            return true;
        }
        case OP_PARSE: {
            if (args[0].k != V_VEC || !is_u8_col(args[0].u.vec))
                return efail(cx, sp, "parse needs a [u8]");
            size_t n;
            uint8_t *b = col_bytes(args[0].u.vec, &n);
            char *src = malloc(n + 1);
            memcpy(src, b, n);
            src[n] = 0;
            free(b);
            size_t nds;
            SnelErr pe;
            memset(&pe, 0, sizeof pe);
            Node *ds = parse_unit(src, &nds, &pe);
            if (!ds)
                return efail(cx, sp, pe.msg);
            Val *vals = malloc((nds ? nds : 1) * sizeof(Val));
            for (size_t i = 0; i < nds; i++)
                vals[i] = ast_to_val(&ds[i]);
            Col *c;
            if (!col_from_vals(vals, nds, &c, e))
                return false;
            *out = vvec(c);
            return true;
        }
        case OP_UNPARSE: {
            if (args[0].k == V_VEC) {
                Col *c = args[0].u.vec;
                Node *ds = malloc((c->len ? c->len : 1) * sizeof(Node));
                for (size_t i = 0; i < c->len; i++) {
                    Val ev = col_elem(c, i);
                    Node *nd;
                    SnelErr de;
                    memset(&de, 0, sizeof de);
                    if (!val_to_ast(&ev, &nd, &de))
                        return efail(cx, sp, de.msg);
                    ds[i] = *nd;
                    val_drop(ev);
                }
                char *s = fmt_program(ds, c->len);
                *out = vvec(col_u8s((const uint8_t *)s, strlen(s)));
                free(s);
                return true;
            }
            if (args[0].k == V_TAB) {
                Node *nd;
                SnelErr de;
                memset(&de, 0, sizeof de);
                if (!val_to_ast(&args[0], &nd, &de))
                    return efail(cx, sp, de.msg);
                char *s = fmt_node(nd, 0);
                *out = vvec(col_u8s((const uint8_t *)s, strlen(s)));
                free(s);
                return true;
            }
            return efail(cx, sp, "unparse needs an AST tab or [tab]");
        }
    }
    return efail(cx, sp, "unknown builtin");
}

// ---------- call-frame pool ----------
// A closure call's environment does not escape — closures capture a trimmed
// *copy*, so the frame dies with the call — except when the body reflects via
// env(), which shows up afterwards as rc > 1. So reuse frame tabs across calls
// instead of a malloc/free per application (the hot path in fold/map).
#define FRAME_POOL_MAX 512
static Tab *g_frames[FRAME_POOL_MAX];
static int g_nframes = 0;
static Tab *frame_get(void) {
    return g_nframes > 0 ? g_frames[--g_nframes] : tab_new();
}
static void frame_put(Tab *t) {
    for (size_t i = 0; i < t->len; i++) {
        bin_drop(&t->keys[i]);
        val_drop(t->vals[i]);
        if (t->has_doc[i])
            bin_drop(&t->docs[i]);
    }
    t->len = 0; // keep the arrays for the next call
    if (g_nframes < FRAME_POOL_MAX)
        g_frames[g_nframes++] = t;
    else {
        free(t->keys);
        free(t->vals);
        free(t->docs);
        free(t->has_doc);
        free(t);
    }
}

// ---------- apply ----------
Val call_prim(const Bin *name, Val *args, size_t na, bool *ok, char *err, size_t errlen);
static bool apply(Cx *cx, const Val *f, Val *args, size_t na, uint32_t sp, Val *out) {
    if (f->k == V_FUN) {
        Clo *clo = f->u.fun;
        if (na != clo->nparams)
            return efail(cx, sp, "arity mismatch");
        Tab *env = frame_get();
        Tab *cap = clo->env; // copy the captured bindings into the reused frame
        for (size_t i = 0; i < cap->len; i++)
            tab_bind(env, bin_clone(cap->keys[i]), val_clone(cap->vals[i]),
                     cap->has_doc[i] ? &cap->docs[i] : NULL);
        for (size_t i = 0; i < clo->nparams; i++) {
            Val cv;
            if (!coerce(cx, clo->env, val_clone(args[i]), &clo->ptypes[i], sp, &cv)) {
                env->rc == 1 ? frame_put(env) : tab_release(env);
                return false;
            }
            tab_bind(env, bin_clone(clo->params[i]), cv, NULL);
        }
        Val r;
        bool ok = eval(cx, env, clo->body, &r);
        // reuse the frame unless the body captured it (env() -> rc > 1)
        env->rc == 1 ? frame_put(env) : tab_release(env);
        if (!ok)
            return false;
        return coerce(cx, clo->env, r, &clo->ret, sp,
                      out); // the declared return type is enforced too
    }
    if (f->k == V_PRIM) {
        // a first-class builtin routes straight to the builtin dispatch (no
        // closure, no AST); its arity isn't statically guaranteed here, so check
        // it. `locals` sees an empty env as a value (degenerate).
        int op = op_by_name(bin_bytes(&f->u.bin), f->u.bin.len);
        if (op >= 0) {
            if ((int)na != op_arity(op))
                return efail(cx, sp, "builtin arity mismatch");
            Tab *empty = tab_new();
            bool ok = builtin(cx, empty, op, args, na, sp, out);
            tab_release(empty);
            return ok;
        }
        bool ok;
        Val v = call_prim(&f->u.bin, args, na, &ok, cx->err.msg, sizeof cx->err.msg);
        if (!ok) {
            cx->err.span = sp;
            return false;
        }
        *out = v;
        return true;
    }
    return efail(cx, sp, "cannot call non-function");
}

// ---------- eval ----------
static bool eval(Cx *cx, Tab *env, const Node *n, Val *out) {
    uint32_t sp = n->lo;
    switch (n->k) {
        case A_LIT:
            *out = val_clone(n->lit);
            return true;
        case A_VAR: {
            const uint8_t *nm = bin_bytes(&n->name);
            size_t nl = n->name.len;
            // inline cache: this node is always evaluated under one env layout,
            // so its slot is invariant — trust it after a cheap revalidation.
            int s = n->var_slot;
            if (s >= 0 && (size_t)s < env->len && env->keys[s].len == nl &&
                memcmp(bin_bytes(&env->keys[s]), nm, nl) == 0) {
                *out = val_clone(env->vals[s]);
                return true;
            }
            for (size_t i = env->len; i-- > 0;) // rightmost binding wins
                if (env->keys[i].len == nl && memcmp(bin_bytes(&env->keys[i]), nm, nl) == 0) {
                    ((Node *)n)->var_slot = (int)i;
                    *out = val_clone(env->vals[i]);
                    return true;
                }
            if (op_by_name(nm, nl) >= 0) { // a builtin as a first-class value
                Val v;
                v.k = V_PRIM;
                v.u.bin = bin_clone(n->name);
                *out = v;
                return true;
            }
            return efail(cx, sp, "unbound name");
        }
        case A_PROJ: {
            Val e;
            if (!eval(cx, env, n->a, &e))
                return false;
            if (e.k != V_TAB) {
                val_drop(e);
                return efail(cx, sp, "cannot project from non-tab");
            }
            Val *v = tab_get(e.u.tab, bin_bytes(&n->name), n->name.len);
            if (!v) {
                val_drop(e);
                return efail(cx, sp, "no such field");
            }
            *out = val_clone(*v);
            val_drop(e);
            return true;
        }
        case A_IDX: {
            Val t, i;
            if (!eval(cx, env, n->a, &t))
                return false;
            if (!eval(cx, env, n->b, &i)) {
                val_drop(t);
                return false;
            }
            bool ok = op_index(&t, &i, out, &cx->err);
            if (!ok)
                cx->err.span = sp;
            val_drop(t);
            val_drop(i);
            return ok;
        }
        case A_APP: {
            // builtins and apply *borrow* their args; we own them and drop them
            // here once the call returns (freeing the per-op transients).
            if (n->a->k == A_VAR) {
                int op = n->op_cache; // resolve the builtin op once, then cache it
                if (op == -2)
                    op = ((Node *)n)->op_cache = op_by_name(bin_bytes(&n->a->name), n->a->name.len);
                if (op >= 0) {
                    Val stackbuf[4]; // avoid a heap alloc for the common low arity
                    Val *args = n->nkids <= 4 ? stackbuf : malloc(n->nkids * sizeof(Val));
                    for (size_t i = 0; i < n->nkids; i++)
                        if (!eval(cx, env, &n->kids[i], &args[i])) {
                            for (size_t j = 0; j < i; j++)
                                val_drop(args[j]);
                            if (args != stackbuf)
                                free(args);
                            return false;
                        }
                    bool ok = builtin(cx, env, op, args, n->nkids, sp, out);
                    for (size_t i = 0; i < n->nkids; i++)
                        val_drop(args[i]);
                    if (args != stackbuf)
                        free(args);
                    return ok;
                }
            }
            Val f;
            if (!eval(cx, env, n->a, &f))
                return false;
            Val stackbuf[4];
            Val *args = n->nkids <= 4 ? stackbuf : malloc(n->nkids * sizeof(Val));
            for (size_t i = 0; i < n->nkids; i++)
                if (!eval(cx, env, &n->kids[i], &args[i])) {
                    for (size_t j = 0; j < i; j++)
                        val_drop(args[j]);
                    if (args != stackbuf)
                        free(args);
                    val_drop(f);
                    return false;
                }
            bool ok = apply(cx, &f, args, n->nkids, sp, out);
            for (size_t i = 0; i < n->nkids; i++)
                val_drop(args[i]);
            if (args != stackbuf)
                free(args);
            val_drop(f);
            return ok;
        }
        case A_VEC: {
            Val *vals = malloc((n->nkids ? n->nkids : 1) * sizeof(Val));
            for (size_t i = 0; i < n->nkids; i++)
                if (!eval(cx, env, &n->kids[i], &vals[i])) {
                    for (size_t j = 0; j < i; j++)
                        val_drop(vals[j]);
                    free(vals);
                    return false;
                }
            Col *c;
            bool ok = col_from_vals(vals, n->nkids, &c, &cx->err); // consumes the elements
            free(vals);
            if (!ok) {
                cx->err.span = sp;
                return false;
            }
            Val v;
            v.k = V_VEC;
            v.u.vec = c;
            *out = v;
            return true;
        }
        case A_TAB: {
            Tab *t = tab_new();
            for (size_t i = 0; i < n->nkeys; i++) {
                Val v;
                if (!eval(cx, env, &n->kids[i], &v))
                    return false;
                tab_bind(t, bin_clone(n->keys[i]), v, NULL);
            }
            Val v;
            v.k = V_TAB;
            v.u.tab = t;
            *out = v;
            return true;
        }
        case A_FUN: {
            // Capture the body's free names — and, transitively, the type names a
            // captured `typ` refers to in its own base, so that resolving (and
            // coercing against) that type still works inside the closure. `fv`
            // grows as those deps are found, so the loop re-reads `fv.n`.
            Syms fv = {0};
            free_vars(n, &fv);
            Tab *cap = tab_new();
            for (size_t i = 0; i < fv.n; i++) {
                Val *v = tab_get(env, bin_bytes(&fv.v[i]), fv.v[i].len);
                if (!v)
                    continue;
                tab_bind(cap, bin_clone(fv.v[i]), val_clone(*v), NULL);
                typ_deps(v, &fv);
            }
            Clo *c = malloc(sizeof(Clo));
            c->rc = 1;
            c->nparams = n->nparams;
            c->params = malloc((n->nparams ? n->nparams : 1) * sizeof(Bin));
            c->ptypes = malloc((n->nparams ? n->nparams : 1) * sizeof(Ty));
            for (size_t i = 0; i < n->nparams; i++) {
                c->params[i] = bin_clone(n->params[i]);
                c->ptypes[i] = n->ptypes[i];
            }
            c->ret = n->ty;
            c->body = n->a;
            c->env = cap;
            Val v;
            v.k = V_FUN;
            v.u.fun = c;
            *out = v;
            return true;
        }
        case A_IF: {
            Val c;
            if (!eval(cx, env, n->a, &c))
                return false;
            if (c.k == V_BIT)
                return eval(cx, env, c.u.i ? n->b : n->c, out);
            val_drop(c);
            return efail(cx, sp, "if condition must be a scalar bit (use select for a [bit] mask)");
        }
        case A_TRY: {
            if (eval(cx, env, n->a, out))
                return true;
            return eval(cx, env, n->b, out);
        }
        case A_ERR: {
            Val v;
            if (!eval(cx, env, n->a, &v))
                return false;
            if (v.k == V_VEC && is_u8_col(v.u.vec)) {
                size_t l;
                uint8_t *b = col_bytes(v.u.vec, &l);
                if (l > 255)
                    l = 255;
                char m[256];
                memcpy(m, b, l);
                m[l] = 0;
                free(b);
                return efail(cx, sp, m);
            }
            char *s = fmt_val(&v);
            bool r = efail(cx, sp, s);
            free(s);
            return r;
        }
        case A_IS: {
            Val v;
            if (!eval(cx, env, n->a, &v))
                return false;
            // a vec tested against a scalar element type -> elementwise;
            // against a vector type (e.g. str) -> whole-value
            bool wholevec;
            if (!is_vec_type(cx, env, &n->ty, sp, &wholevec))
                return false;
            if (v.k == V_VEC && !wholevec) {
                Col *c = v.u.vec;
                Bits b = bits_new(0, false);
                for (size_t i = 0; i < c->len; i++) {
                    Val e = col_elem(c, i);
                    bool r;
                    if (!scalar_is(cx, env, &e, &n->ty, sp, &r))
                        return false;
                    bits_push(&b, r);
                    val_drop(e);
                }
                Payload p;
                p.k = P_BITS;
                p.u.bits = b;
                Val rv;
                rv.k = V_VEC;
                rv.u.vec = col_simple(p);
                *out = rv;
                return true;
            }
            bool r;
            if (!scalar_is(cx, env, &v, &n->ty, sp, &r))
                return false;
            *out = vbit(r);
            return true;
        }
        case A_AS: {
            Val v;
            if (!eval(cx, env, n->a, &v))
                return false;
            return coerce(cx, env, v, &n->ty, sp, out);
        }
        case A_SEQ: {
            Tab *cur = tab_retain(env);
            Val last = vnil();
            for (size_t i = 0; i < n->nkids; i++) {
                Val v;
                if (!decl_step(cx, &cur, &n->kids[i], &v))
                    return false;
                last = v;
            }
            *out = last;
            return true;
        }
        case A_LET:
        case A_TYP:
        case A_USE: {
            Tab *cur = tab_retain(env);
            return decl_step(cx, &cur, n, out);
        }
    }
    return efail(cx, sp, "unhandled node");
}

// ---------- public entry ----------

// Evaluate a unit *pure* (no ambient io). Its value is the tab of its `pub`
// names (all names if none are pub).
bool eval_program(Node *ds, size_t nds, Loader *loader, Val *out, char *errbuf, size_t errlen) {
    // Resolve top-level `use` imports to their interface types, at check time:
    // a missing file or an import cycle is a compile error here, not a deferred
    // eval error, and imported names then type precisely (mirrors src/lib.rs).
    Bin imp_names[128] = {0};
    Ty imp_tys[128] = {0};
    size_t nimp = 0;
    for (size_t i = 0; i < nds; i++) {
        if (ds[i].k != A_USE)
            continue;
        if (!loader) {
            snprintf(errbuf, errlen, "check error: cannot resolve `use %.*s` (no loader)",
                     (int)ds[i].name.len, bin_bytes(&ds[i].name));
            return false;
        }
        bool ok = false;
        Val v;
        if (ds[i].has_url) {
            if (!loader->load_url) {
                snprintf(errbuf, errlen, "check error: remote units are not supported here");
                return false;
            }
            v = loader->load_url(loader, &ds[i].name, &ds[i].url, &ok, errbuf, errlen);
        } else
            v = loader->load(loader, &ds[i].name, &ok, errbuf, errlen);
        if (!ok)
            return false; // loader filled errbuf (missing file / cycle / dep error)
        if (nimp < 128) {
            imp_names[nimp] = ds[i].name;
            imp_tys[nimp] = val_ty(&v);
            nimp++;
        }
        val_drop(v);
    }
    if (!check_unit(ds, nds, NULL, 0, imp_names, imp_tys, nimp, errbuf, errlen))
        return false; // static check precedes eval
    Cx cx;
    cx.loader = loader;
    memset(&cx.err, 0, sizeof cx.err);
    Tab *env = tab_new();
    Bin *pubs = NULL;
    size_t npub = 0, pcap = 0;
    for (size_t i = 0; i < nds; i++) {
        Val v;
        if (!decl_step(&cx, &env, &ds[i], &v)) {
            snprintf(errbuf, errlen, "eval error (line %u): %s", err_line(cx.err.span), cx.err.msg);
            tab_release(env);
            free(pubs);
            return false;
        }
        if ((ds[i].k == A_LET || ds[i].k == A_TYP) && ds[i].is_pub) {
            if (npub == pcap) {
                pcap = pcap ? pcap * 2 : 8;
                pubs = realloc(pubs, pcap * sizeof(Bin));
            }
            pubs[npub++] = ds[i].name;
        }
    }
    Tab *o = tab_new();
    if (npub == 0) {
        for (size_t i = 0; i < env->len; i++)
            tab_bind(o, bin_clone(env->keys[i]), val_clone(env->vals[i]),
                     env->has_doc[i] ? &env->docs[i] : NULL);
    } else {
        for (size_t j = 0; j < npub; j++) {
            int idx = -1;
            for (size_t i = env->len; i-- > 0;)
                if (bin_eq(&env->keys[i], &pubs[j])) {
                    idx = (int)i;
                    break;
                }
            if (idx >= 0)
                tab_bind(o, bin_clone(pubs[j]), val_clone(env->vals[idx]),
                         env->has_doc[idx] ? &env->docs[idx] : NULL);
        }
    }
    tab_release(env);
    free(pubs);
    Val v;
    v.k = V_TAB;
    v.u.tab = o;
    *out = v;
    return true;
}

// Run a unit as a program: evaluate it pure, then if it exports `main`, call
// main(io) with the io capability. This is the only place io enters.
// Apply a decoded closure to a fresh `io` and return its result. The child side
// of subprocess eval (`snel apply`); mirrors src/lib.rs apply_bin's core.
bool run_closure(const Val *f, Loader *loader, Val *out, char *errbuf, size_t errlen) {
    Cx cx;
    cx.loader = loader;
    memset(&cx.err, 0, sizeof cx.err);
    Val io = io_tab(), fn = val_clone(*f);
    if (!apply(&cx, &fn, &io, 1, 0, out)) {
        snprintf(errbuf, errlen, "eval error: %s", cx.err.msg);
        return false;
    }
    return true;
}

bool run_program(Node *ds, size_t nds, Loader *loader, Val *out, char *errbuf, size_t errlen) {
    Val unit;
    if (!eval_program(ds, nds, loader, &unit, errbuf, errlen))
        return false;
    if (unit.k == V_TAB) {
        Val *m = tab_get(unit.u.tab, (const uint8_t *)"main", 4);
        if (m && (m->k == V_FUN || m->k == V_PRIM)) {
            Cx cx;
            cx.loader = loader;
            memset(&cx.err, 0, sizeof cx.err);
            Val io = io_tab(), main = val_clone(*m);
            if (!apply(&cx, &main, &io, 1, 0, out)) {
                snprintf(errbuf, errlen, "eval error: %s", cx.err.msg);
                return false;
            }
            return true;
        }
    }
    *out = unit;
    return true;
}

void clo_release(Clo *c) {
    if (!c || --c->rc)
        return;
    tab_release(c->env);
    free(c);
}
