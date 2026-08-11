// Vectorized builtins. Mirrors src/ops.rs. Columns are produced fresh
// (immutable semantics; COW-in-place is an unobservable optimization omitted
// in this port). Buffers are leaked (short-lived process).
#include "snel.h"
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void seterr(SnelErr *e, const char *m) {
    snprintf(e->msg, sizeof e->msg, "%s", m);
}

// ---------- total order ----------
// case kinds: 1 bit, 2 i64, 3 f64, 4 bytes([u8]), 5 vecs([[T]]), 6 tab.
static int rank(const Val *v) {
    switch (v->k) {
        case V_NIL:
            return 0;
        case V_BIT:
            return 1;
        case V_I64:
            return 2;
        case V_F64:
            return 3;
        case V_U8:
            return 4;
        case V_VEC:
            return 6;
        case V_TAB:
            return 7;
        case V_FUN:
            return 8;
        case V_PRIM:
            return 9;
    }
    return 10;
}
static int cmp_f64_total(double a, double b) {
    uint64_t ua, ub;
    memcpy(&ua, &a, 8);
    memcpy(&ub, &b, 8);
    int64_t ia = (int64_t)ua, ib = (int64_t)ub;
    ia ^= (int64_t)((uint64_t)(ia >> 63) >> 1);
    ib ^= (int64_t)((uint64_t)(ib >> 63) >> 1);
    return ia < ib ? -1 : ia > ib ? 1 : 0;
}
int cmp_val(const Val *a, const Val *b) {
    if (a->k != b->k)
        return rank(a) < rank(b) ? -1 : 1;
    switch (a->k) {
        case V_NIL:
            return 0;
        case V_BIT:
        case V_I64:
        case V_U8:
            return a->u.i < b->u.i ? -1 : a->u.i > b->u.i ? 1 : 0;
        case V_F64:
            return cmp_f64_total(a->u.f, b->u.f);
        case V_VEC: { // lexicographic by element (so strings / nested cols sort)
            Col *x = a->u.vec, *y = b->u.vec;
            size_t m = x->len < y->len ? x->len : y->len;
            for (size_t i = 0; i < m; i++) {
                Val xe = col_elem(x, i), ye = col_elem(y, i);
                int o = cmp_val(&xe, &ye);
                val_drop(xe);
                val_drop(ye);
                if (o)
                    return o;
            }
            return x->len < y->len ? -1 : x->len > y->len ? 1 : 0;
        }
        default:
            return 0;
    }
}

// True iff c is a plain [u8] column (one Bytes payload, no nils, no union).
bool is_u8_col(const Col *c) {
    return !c->has_present && !c->has_sel && c->ncases == 1 && c->cases[0].k == P_U8S;
}
// Bytes of a plain [u8] column into a fresh malloc'd buffer (caller frees).
uint8_t *col_bytes(const Col *c, size_t *len) {
    if (is_u8_col(c)) {
        *len = c->cases[0].u.u8s.len;
        uint8_t *b = malloc(*len ? *len : 1);
        memcpy(b, bin_bytes(&c->cases[0].u.u8s), *len);
        return b;
    }
    *len = c->len;
    uint8_t *b = malloc(c->len ? c->len : 1);
    for (size_t i = 0; i < c->len; i++) {
        Val e = col_elem(c, i);
        b[i] = e.k == V_U8 ? (uint8_t)e.u.i : 0;
        val_drop(e);
    }
    return b;
}

// ---------- column construction ----------
static int kind_of(const Val *v) {
    switch (v->k) {
        case V_BIT:
            return 1;
        case V_I64:
            return 2;
        case V_F64:
            return 3;
        case V_U8:
            return 4;
        case V_VEC:
            return 5;
        case V_TAB:
            return 6;
        default:
            return 0;
    }
}

// Build one case payload by gathering the matching-kind elements of `vals`.
static Payload build_case(int kind, Val *vals, size_t n) {
    Payload p;
    switch (kind) {
        case 1:
            p.k = P_BITS;
            p.u.bits = bits_new(n, false);
            for (size_t i = 0; i < n; i++)
                if (vals[i].k == V_BIT)
                    bits_set(&p.u.bits, i, vals[i].u.i != 0);
            break;
        case 2:
            p.k = P_I64S;
            p.u.i64 = calloc(n ? n : 1, sizeof(int64_t));
            for (size_t i = 0; i < n; i++)
                if (vals[i].k == V_I64)
                    p.u.i64[i] = vals[i].u.i;
            break;
        case 3:
            p.k = P_F64S;
            p.u.f64 = calloc(n ? n : 1, sizeof(double));
            for (size_t i = 0; i < n; i++)
                if (vals[i].k == V_F64)
                    p.u.f64[i] = canon_f64(vals[i].u.f);
            break;
        case 4: {
            uint8_t *buf = calloc(n ? n : 1, 1);
            for (size_t i = 0; i < n; i++)
                if (vals[i].k == V_U8)
                    buf[i] = (uint8_t)vals[i].u.i;
            p.k = P_U8S;
            p.u.u8s = bin_new(buf, n);
            free(buf);
        } break;
        case 5:
            p.k = P_VECS;
            p.u.vecs = calloc(n ? n : 1, sizeof(Col *));
            for (size_t i = 0; i < n; i++)
                p.u.vecs[i] = vals[i].k == V_VEC ? col_retain(vals[i].u.vec) : col_u8s(NULL, 0);
            break;
        default:
            p.k = P_TABS;
            p.u.tab = calloc(n ? n : 1, sizeof(Tab *));
            for (size_t i = 0; i < n; i++)
                p.u.tab[i] = vals[i].k == V_TAB ? tab_retain(vals[i].u.tab) : tab_new();
            break;
    }
    return p;
}

bool col_from_vals(Val *vals, size_t n, Col **out, SnelErr *e) {
    int kinds[8];
    int nk = 0;
    bool has_nil = false;
    for (size_t i = 0; i < n; i++) {
        if (vals[i].k == V_NIL) {
            has_nil = true;
            continue;
        }
        int k = kind_of(&vals[i]);
        if (k == 0) {
            seterr(e, "vec elements must be prims, strings, vecs, or tabs");
            return false;
        }
        bool found = false;
        for (int j = 0; j < nk; j++)
            if (kinds[j] == k)
                found = true;
        if (!found)
            kinds[nk++] = k;
    }
    if (nk == 0)
        kinds[nk++] = 2;
    Col *c = malloc(sizeof(Col));
    c->rc = 1;
    c->len = n;
    c->ncases = nk;
    for (int j = 0; j < nk; j++)
        c->cases[j] = build_case(kinds[j], vals, n);
    Bits present = bits_new(n, true);
    uint8_t *sel = calloc(n ? n : 1, 1);
    for (size_t i = 0; i < n; i++) {
        if (vals[i].k == V_NIL) {
            bits_set(&present, i, false);
            continue;
        }
        int k = kind_of(&vals[i]);
        int cix = 0;
        for (int j = 0; j < nk; j++)
            if (kinds[j] == k)
                cix = j;
        sel[i] = (uint8_t)cix;
    }
    c->has_present = has_nil;
    c->present = present;
    c->has_sel = nk > 1;
    c->sel = sel;
    if (!has_nil)
        bits_free(&present);
    if (nk <= 1)
        free(sel), c->sel = NULL;
    // consume the inputs: build_case retained nested vecs/tabs into the column,
    // so the source values are done with (the caller still owns the array).
    for (size_t i = 0; i < n; i++)
        val_drop(vals[i]);
    *out = c;
    return true;
}

// ty kind for coercion representation
static int ty_kind(const Ty *t) {
    switch (t->k) {
        case T_BIT:
            return 1;
        case T_I64:
            return 2;
        case T_F64:
            return 3;
        case T_U8:
            return 4;
        case T_VEC:
            return 5;
        case T_TAB:
            return 6;
        default:
            return 0;
    }
}
static bool ty_admits_nil(const Ty *t) {
    if (t->k == T_NIL)
        return true;
    if (t->k == T_UNION)
        for (size_t i = 0; i < t->n; i++)
            if (t->elem[i].k == T_NIL)
                return true;
    return false;
}

bool coerce_col(const Col *c, const Ty *t, Col **out, SnelErr *e) {
    // gather non-nil member kinds in order
    int kinds[8];
    int nk = 0;
    if (t->k == T_UNION) {
        for (size_t i = 0; i < t->n; i++) {
            if (t->elem[i].k == T_NIL)
                continue;
            int k = ty_kind(&t->elem[i]);
            if (k == 0) {
                seterr(e, "bad vec element type");
                return false;
            }
            kinds[nk++] = k;
        }
    } else {
        int k = ty_kind(t);
        if (k == 0) {
            seterr(e, "bad vec element type");
            return false;
        }
        kinds[nk++] = k;
    }
    bool admits = ty_admits_nil(t);
    size_t n = c->len;
    Val *vals = malloc((n ? n : 1) * sizeof(Val));
    Bits present = bits_new(n, true);
    uint8_t *sel = calloc(n ? n : 1, 1);
    for (size_t i = 0; i < n; i++) {
        Val v = col_elem(c, i);
        vals[i] = v;
        if (v.k == V_NIL) {
            if (!admits) {
                seterr(e, "nil element under non-nil type");
                return false;
            }
            bits_set(&present, i, false);
        } else {
            int k = kind_of(&v);
            int cix = -1;
            for (int j = 0; j < nk; j++)
                if (kinds[j] == k)
                    cix = j;
            if (cix < 0) {
                seterr(e, "element does not fit type");
                return false;
            }
            sel[i] = (uint8_t)cix;
        }
    }
    Col *r = malloc(sizeof(Col));
    r->rc = 1;
    r->len = n;
    r->ncases = nk;
    for (int j = 0; j < nk; j++)
        r->cases[j] = build_case(kinds[j], vals, n);
    r->has_present = admits;
    r->present = present;
    r->has_sel = nk > 1;
    r->sel = sel;
    if (!admits)
        bits_free(&present);
    if (nk <= 1)
        free(sel), r->sel = NULL;
    // build_case retained what it needs; release the col_elem refs and the array
    for (size_t i = 0; i < n; i++)
        val_drop(vals[i]);
    free(vals);
    *out = r;
    return true;
}

static Val vvec(Col *c) {
    Val v;
    v.k = V_VEC;
    v.u.vec = c;
    return v;
}

// ---------- arithmetic ----------
static bool is_simple(const Col *c) {
    return !c->has_sel && c->ncases == 1;
}

bool arith2(int op, const Val *a, const Val *b, Val *out, SnelErr *e) {
    if (a->k == V_NIL || b->k == V_NIL) {
        *out = vnil();
        return true;
    }
    if (a->k == V_I64 && b->k == V_I64) {
        int64_t x = a->u.i, y = b->u.i, r;
        switch (op) {
            case OP_ADD:
                r = (int64_t)((uint64_t)x + (uint64_t)y);
                break;
            case OP_SUB:
                r = (int64_t)((uint64_t)x - (uint64_t)y);
                break;
            case OP_MUL:
                r = (int64_t)((uint64_t)x * (uint64_t)y);
                break;
            case OP_DIV:
                if (y == 0 || (x == INT64_MIN && y == -1)) {
                    seterr(e, "division overflow");
                    return false;
                }
                r = x / y;
                break;
            case OP_REM:
                if (y == 0 || (x == INT64_MIN && y == -1)) {
                    seterr(e, "division overflow");
                    return false;
                }
                r = x % y;
                break;
            default:
                seterr(e, "bad op");
                return false;
        }
        *out = vi64(r);
        return true;
    }
    if (a->k == V_F64 && b->k == V_F64) {
        double x = a->u.f, y = b->u.f, r;
        switch (op) {
            case OP_ADD:
                r = x + y;
                break;
            case OP_SUB:
                r = x - y;
                break;
            case OP_MUL:
                r = x * y;
                break;
            case OP_DIV:
                r = x / y;
                break;
            case OP_REM:
                r = fmod(x, y);
                break;
            default:
                seterr(e, "bad op");
                return false;
        }
        *out = vf64(canon_f64(r));
        return true;
    }
    seterr(e, "type mismatch in arithmetic");
    return false;
}

// Broadcast a scalar to match `like`'s length; nil takes the peer's payload
// kind so nil propagates against any numeric column. Returns NULL for
// fun/prim scalars (no elementwise arithmetic).
static Col *broadcast(const Val *v, const Col *like) {
    size_t n = like->len;
    Col *c = malloc(sizeof(Col));
    c->rc = 1;
    c->len = n;
    c->has_sel = false;
    c->sel = NULL;
    c->ncases = 1;
    c->has_present = false;
    switch (v->k) {
        case V_NIL: {
            c->has_present = true;
            c->present = bits_new(n, false);
            Payload p;
            PKind pk = like->cases[0].k;
            if (pk == P_F64S) {
                p.k = P_F64S;
                p.u.f64 = calloc(n ? n : 1, sizeof(double));
            } else if (pk == P_BITS) {
                p.k = P_BITS;
                p.u.bits = bits_new(n, false);
            } else {
                p.k = P_I64S;
                p.u.i64 = calloc(n ? n : 1, sizeof(int64_t));
            }
            c->cases[0] = p;
        } break;
        case V_BIT:
            c->cases[0].k = P_BITS;
            c->cases[0].u.bits = bits_new(n, v->u.i != 0);
            break;
        case V_I64: {
            c->cases[0].k = P_I64S;
            c->cases[0].u.i64 = malloc((n ? n : 1) * sizeof(int64_t));
            for (size_t i = 0; i < n; i++)
                c->cases[0].u.i64[i] = v->u.i;
        } break;
        case V_F64: {
            c->cases[0].k = P_F64S;
            c->cases[0].u.f64 = malloc((n ? n : 1) * sizeof(double));
            for (size_t i = 0; i < n; i++)
                c->cases[0].u.f64[i] = v->u.f;
        } break;
        case V_TAB: {
            c->cases[0].k = P_TABS;
            c->cases[0].u.tab = malloc((n ? n : 1) * sizeof(Tab *));
            for (size_t i = 0; i < n; i++)
                c->cases[0].u.tab[i] = tab_retain(v->u.tab);
        } break;
        default:
            free(c);
            return NULL;
    }
    return c;
}

// Elementwise arithmetic, functional-but-in-place: if either operand column is
// uniquely referenced (rc == 1, simple, matching kind) its buffer is mutated in
// place and a fresh reference to it is handed back, instead of allocating a new
// column — mirrors Rust's Rc::make_mut. The inner loop is direct (no per-element
// boxing through arith2).
static bool vec_arith(int op, const Col *a, const Col *b, Val *out, SnelErr *e) {
    if (!is_simple(a) || !is_simple(b)) {
        seterr(e, "no elementwise arithmetic on union columns");
        return false;
    }
    PKind k = a->cases[0].k;
    if (k != b->cases[0].k || (k != P_I64S && k != P_F64S)) {
        seterr(e, "type mismatch in arithmetic");
        return false;
    }
    size_t n = a->len;
    bool hp = a->has_present || b->has_present;
    Bits present;
    if (hp) {
        present = bits_new(n, true);
        for (size_t i = 0; i < n; i++) {
            bool pa = a->has_present ? bits_get(&a->present, i) : true;
            bool pb = b->has_present ? bits_get(&b->present, i) : true;
            bits_set(&present, i, pa && pb);
        }
    }
    // reuse a uniquely-referenced operand's buffer, else allocate a fresh one
    Col *c;
    if (a->rc == 1)
        c = col_retain((Col *)a);
    else if (b->rc == 1)
        c = col_retain((Col *)b);
    else {
        c = malloc(sizeof(Col));
        c->rc = 1;
        c->len = n;
        c->ncases = 1;
        c->has_sel = false;
        c->sel = NULL;
        c->has_present = false;
        c->cases[0].k = k;
        if (k == P_I64S)
            c->cases[0].u.i64 = malloc((n ? n : 1) * sizeof(int64_t));
        else
            c->cases[0].u.f64 = malloc((n ? n : 1) * sizeof(double));
    }
    if (k == P_I64S) {
        const int64_t *x = a->cases[0].u.i64, *y = b->cases[0].u.i64;
        int64_t *o = c->cases[0].u.i64;
        for (size_t i = 0; i < n; i++) {
            if (hp && !bits_get(&present, i)) {
                o[i] = 0;
                continue;
            }
            if (op == OP_DIV || op == OP_REM) {
                if (y[i] == 0 || (x[i] == INT64_MIN && y[i] == -1)) {
                    seterr(e, "division overflow");
                    if (hp)
                        bits_free(&present);
                    col_release(c);
                    return false;
                }
                o[i] = op == OP_DIV ? x[i] / y[i] : x[i] % y[i];
            } else {
                uint64_t ux = (uint64_t)x[i], uy = (uint64_t)y[i];
                o[i] = (int64_t)(op == OP_ADD ? ux + uy : op == OP_SUB ? ux - uy : ux * uy);
            }
        }
    } else {
        const double *x = a->cases[0].u.f64, *y = b->cases[0].u.f64;
        double *o = c->cases[0].u.f64;
        for (size_t i = 0; i < n; i++) {
            if (hp && !bits_get(&present, i)) {
                o[i] = 0;
                continue;
            }
            double r = op == OP_ADD   ? x[i] + y[i]
                       : op == OP_SUB ? x[i] - y[i]
                       : op == OP_MUL ? x[i] * y[i]
                       : op == OP_DIV ? x[i] / y[i]
                                      : fmod(x[i], y[i]);
            o[i] = canon_f64(r);
        }
    }
    if (c->has_present)
        bits_free(&c->present);
    c->has_present = hp;
    if (hp)
        c->present = present;
    *out = vvec(c);
    return true;
}

bool op_arith(int op, Val a, Val b, Val *out, SnelErr *e) {
    if (a.k == V_VEC && b.k == V_VEC) {
        if (a.u.vec->len != b.u.vec->len) {
            seterr(e, "length mismatch");
            return false;
        }
        return vec_arith(op, a.u.vec, b.u.vec, out, e);
    }
    if (a.k == V_VEC) {
        Col *bb = broadcast(&b, a.u.vec);
        if (!bb) {
            seterr(e, "type mismatch in arithmetic");
            return false;
        }
        bool ok = vec_arith(op, a.u.vec, bb, out, e);
        col_release(bb);
        return ok;
    }
    if (b.k == V_VEC) {
        Col *aa = broadcast(&a, b.u.vec);
        if (!aa) {
            seterr(e, "type mismatch in arithmetic");
            return false;
        }
        bool ok = vec_arith(op, aa, b.u.vec, out, e);
        col_release(aa);
        return ok;
    }
    return arith2(op, &a, &b, out, e);
}

// ---------- unary ----------
static bool unary_scalar(int op, const Val *v, Val *out, SnelErr *e) {
    if (v->k == V_NIL) {
        *out = vnil();
        return true;
    }
    switch (op) {
        case OP_NEG:
            if (v->k == V_I64) {
                *out = vi64((int64_t)(0 - (uint64_t)v->u.i));
                return true;
            }
            if (v->k == V_F64) {
                *out = vf64(-v->u.f);
                return true;
            }
            break;
        case OP_ABS:
            if (v->k == V_I64) {
                *out = vi64(v->u.i < 0 ? (int64_t)(0 - (uint64_t)v->u.i) : v->u.i);
                return true;
            }
            if (v->k == V_F64) {
                *out = vf64(fabs(v->u.f));
                return true;
            }
            break;
        case OP_ITOF:
            if (v->k == V_I64) {
                *out = vf64((double)v->u.i);
                return true;
            }
            break;
        case OP_FTOI:
            if (v->k == V_F64) {
                double x = v->u.f;
                if (isnan(x) || x < -9223372036854775808.0 || x >= 9223372036854775808.0) {
                    seterr(e, "ftoi out of range");
                    return false;
                }
                *out = vi64((int64_t)x);
                return true;
            }
            break;
        case OP_SQRT:
            if (v->k == V_F64) {
                *out = vf64(canon_f64(sqrt(v->u.f)));
                return true;
            }
            break;
        case OP_FLOOR:
            if (v->k == V_F64) {
                *out = vf64(canon_f64(floor(v->u.f)));
                return true;
            }
            break;
        case OP_CEIL:
            if (v->k == V_F64) {
                *out = vf64(canon_f64(ceil(v->u.f)));
                return true;
            }
            break;
        case OP_SIGN:
            if (v->k == V_I64) {
                int64_t x = v->u.i;
                *out = vi64(x > 0 ? 1 : x < 0 ? -1 : 0);
                return true;
            }
            if (v->k == V_F64) {
                double x = v->u.f;
                *out = vf64(isnan(x) ? canon_f64(x) : (x > 0 ? 1.0 : x < 0 ? -1.0 : 0.0));
                return true;
            }
            break;
        case OP_ORD:
            if (v->k == V_U8) {
                *out = vi64((int64_t)(v->u.i & 0xff));
                return true;
            }
            break;
        case OP_CHR:
            if (v->k == V_I64) {
                Val r;
                r.k = V_U8;
                r.u.i = (int64_t)(v->u.i & 0xff);
                *out = r;
                return true;
            }
            break;
    }
    seterr(e, "bad unary operand");
    return false;
}
bool op_unary(int op, Val a, Val *out, SnelErr *e) {
    if (a.k == V_VEC) {
        Col *c = a.u.vec;
        if (!is_simple(c)) {
            seterr(e, "no elementwise arithmetic on union columns");
            return false;
        }
        Val *vals = malloc((c->len ? c->len : 1) * sizeof(Val));
        for (size_t i = 0; i < c->len; i++) {
            Val ev = col_elem(c, i);
            if (!unary_scalar(op, &ev, &vals[i], e))
                return false;
            val_drop(ev);
        }
        Col *r;
        if (!col_from_vals(vals, c->len, &r, e))
            return false;
        *out = vvec(r);
        return true;
    }
    return unary_scalar(op, &a, out, e);
}

// ---------- comparison ----------
static bool decide(int op, int o) {
    switch (op) {
        case OP_EQ:
            return o == 0;
        case OP_NE:
            return o != 0;
        case OP_LT:
            return o < 0;
        case OP_LE:
            return o <= 0;
        case OP_GT:
            return o > 0;
        case OP_GE:
            return o >= 0;
    }
    return false;
}
bool op_compare(int op, Val a, Val b, Val *out, SnelErr *e) {
    if (a.k == V_VEC && b.k == V_VEC) {
        if (a.u.vec->len != b.u.vec->len) {
            seterr(e, "length mismatch");
            return false;
        }
        size_t n = a.u.vec->len;
        Bits bits = bits_new(0, false);
        for (size_t i = 0; i < n; i++) {
            Val x = col_elem(a.u.vec, i), y = col_elem(b.u.vec, i);
            bits_push(&bits, decide(op, cmp_val(&x, &y)));
            val_drop(x);
            val_drop(y);
        }
        Payload p;
        p.k = P_BITS;
        p.u.bits = bits;
        *out = vvec(col_simple(p));
        return true;
    }
    if (a.k == V_VEC) {
        size_t n = a.u.vec->len;
        Bits bits = bits_new(0, false);
        for (size_t i = 0; i < n; i++) {
            Val x = col_elem(a.u.vec, i);
            bits_push(&bits, decide(op, cmp_val(&x, &b)));
            val_drop(x);
        }
        Payload p;
        p.k = P_BITS;
        p.u.bits = bits;
        *out = vvec(col_simple(p));
        return true;
    }
    if (b.k == V_VEC) {
        size_t n = b.u.vec->len;
        Bits bits = bits_new(0, false);
        for (size_t i = 0; i < n; i++) {
            Val y = col_elem(b.u.vec, i);
            bits_push(&bits, decide(op, cmp_val(&a, &y)));
            val_drop(y);
        }
        Payload p;
        p.k = P_BITS;
        p.u.bits = bits;
        *out = vvec(col_simple(p));
        return true;
    }
    *out = vbit(decide(op, cmp_val(&a, &b)));
    return true;
}

// ---------- boolean ----------
static bool as_bits(const Val *v, const Bits **b, size_t *n) {
    if (v->k != V_VEC)
        return false;
    Col *c = v->u.vec;
    if (c->cases[0].k == P_BITS && !c->has_sel && !c->has_present) {
        *b = &c->cases[0].u.bits;
        *n = c->len;
        return true;
    }
    return false;
}
bool op_boolean(int op, Val *args, size_t na, Val *out, SnelErr *e) {
    if (op == OP_NOT) {
        if (args[0].k == V_BIT) {
            *out = vbit(!args[0].u.i);
            return true;
        }
        const Bits *b;
        size_t n;
        if (!as_bits(&args[0], &b, &n)) {
            seterr(e, "not: expected bit or [bit]");
            return false;
        }
        Bits o = bits_clone(b);
        for (size_t i = 0; i < (n + 63) / 64; i++)
            o.w[i] = ~o.w[i];
        if (n % 64)
            o.w[n / 64] &= ((uint64_t)1 << (n % 64)) - 1;
        Payload p;
        p.k = P_BITS;
        p.u.bits = o;
        *out = vvec(col_simple(p));
        return true;
    }
    if (args[0].k == V_BIT && args[1].k == V_BIT) {
        *out = vbit(op == OP_AND ? (args[0].u.i && args[1].u.i) : (args[0].u.i || args[1].u.i));
        return true;
    }
    const Bits *ba = NULL, *bb = NULL;
    size_t na2 = 0, nb2 = 0;
    bool ha = as_bits(&args[0], &ba, &na2), hb = as_bits(&args[1], &bb, &nb2);
    size_t n = ha ? na2 : (hb ? nb2 : 0);
    if (!ha && !hb) {
        seterr(e, "expected [bit]");
        return false;
    }
    if (ha && hb && na2 != nb2) {
        seterr(e, "length mismatch");
        return false;
    }
    // An operand that is not a bit column has to be a scalar bit, broadcast
    // across the column. Anything else is an error: reading `u.i` regardless of
    // kind would reinterpret a pointer or a double's bit pattern as a truth
    // value, and silently answer instead of rejecting.
    if ((!ha && args[0].k != V_BIT) || (!hb && args[1].k != V_BIT)) {
        seterr(e, "expected bit or [bit]");
        return false;
    }
    Bits x = ha ? bits_clone(ba) : bits_new(n, args[0].u.i != 0);
    Bits y = hb ? bits_clone(bb) : bits_new(n, args[1].u.i != 0);
    for (size_t i = 0; i < (n + 63) / 64; i++)
        x.w[i] = op == OP_AND ? (x.w[i] & y.w[i]) : (x.w[i] | y.w[i]);
    Payload p;
    p.k = P_BITS;
    p.u.bits = x;
    *out = vvec(col_simple(p));
    return true;
}

// ---------- indexing ----------
static bool index_col(const Col *c, const Val *ix, Col **out, SnelErr *e) {
    size_t *picks = NULL;
    size_t np = 0, cap = 0;
    if (ix->k != V_VEC) {
        seterr(e, "index must be [i64] or [bit]");
        return false;
    }
    Col *ic = ix->u.vec;
    if (ic->cases[0].k == P_BITS && !ic->has_sel) {
        if (ic->len != c->len) {
            seterr(e, "mask length vs vec length");
            return false;
        }
        for (size_t i = 0; i < ic->len; i++) {
            bool on = bits_get(&ic->cases[0].u.bits, i) &&
                      (!ic->has_present || bits_get(&ic->present, i));
            if (on) {
                if (np == cap) {
                    cap = cap ? cap * 2 : 8;
                    picks = realloc(picks, cap * sizeof(size_t));
                }
                picks[np++] = i;
            }
        }
    } else if (ic->cases[0].k == P_I64S && !ic->has_sel) {
        if (ic->has_present) {
            seterr(e, "index vector may not contain nil");
            return false;
        }
        for (size_t i = 0; i < ic->len; i++) {
            int64_t k = ic->cases[0].u.i64[i];
            if (k < 0 || (size_t)k >= c->len) {
                seterr(e, "index out of bounds");
                return false;
            }
            if (np == cap) {
                cap = cap ? cap * 2 : 8;
                picks = realloc(picks, cap * sizeof(size_t));
            }
            picks[np++] = (size_t)k;
        }
    } else {
        seterr(e, "index must be [i64] or [bit]");
        return false;
    }
    Val *vals = malloc((np ? np : 1) * sizeof(Val));
    for (size_t i = 0; i < np; i++)
        vals[i] = col_elem(c, picks[i]);
    free(picks);
    Col *tmp;
    bool ok = col_from_vals(vals, np, &tmp, e);
    free(vals);
    if (!ok)
        return false;
    Ty ct = col_ty(c);
    ok = coerce_col(tmp, &ct, out, e);
    col_release(tmp);
    return ok;
}
bool op_index(const Val *target, const Val *ix, Val *out, SnelErr *e) {
    if (target->k == V_VEC) {
        Col *r;
        if (!index_col(target->u.vec, ix, &r, e))
            return false;
        *out = vvec(r);
        return true;
    }
    if (target->k == V_TAB) {
        Tab *t = target->u.tab;
        Tab *o = tab_new();
        size_t rowlen = 0;
        bool set = false;
        for (size_t i = 0; i < t->len; i++) {
            if (t->vals[i].k != V_VEC) {
                seterr(e, "row selection needs a tab of equal-length vecs");
                return false;
            }
            Col *r;
            if (!index_col(t->vals[i].u.vec, ix, &r, e))
                return false;
            if (set && r->len != rowlen) {
                seterr(e, "row selection needs equal-length vecs");
                return false;
            }
            rowlen = r->len;
            set = true;
            tab_bind(o, bin_clone(t->keys[i]), vvec(r), t->has_doc[i] ? &t->docs[i] : NULL);
        }
        Val v;
        v.k = V_TAB;
        v.u.tab = o;
        *out = v;
        return true;
    }
    seterr(e, "only vecs and tabs can be indexed");
    return false;
}

// ---------- string ops on [u8] ----------
// Strings are [u8], so len/cat/index/grade already work via the vector ops.
static bool as_u8s(const Val *v, uint8_t **b, size_t *n, SnelErr *e) {
    if (v->k == V_VEC && is_u8_col(v->u.vec)) {
        *b = col_bytes(v->u.vec, n);
        return true;
    }
    seterr(e, "expected a string ([u8])");
    return false;
}
static Val u8s_val(const uint8_t *b, size_t n) {
    Val v;
    v.k = V_VEC;
    v.u.vec = col_u8s(b, n);
    return v;
}

// `find` is a string op: both operands must be [u8]. A non-string operand is
// an error, not a miss — returning nil for it would make `isnil(find(...))`
// answer "not found" for something that was never searchable.
bool op_find(const Val *hay, const Val *needle, Val *out, SnelErr *e) {
    uint8_t *h, *n;
    size_t hl, nl;
    if (!as_u8s(hay, &h, &hl, e) || !as_u8s(needle, &n, &nl, e))
        return false;
    if (nl == 0) {
        *out = vi64(0);
        return true;
    }
    if (nl <= hl)
        for (size_t i = 0; i + nl <= hl; i++)
            if (!memcmp(h + i, n, nl)) {
                *out = vi64((int64_t)i);
                return true;
            }
    *out = vnil();
    return true;
}
bool op_split(const Val *s, const Val *sep, Val *out, SnelErr *e) {
    uint8_t *h, *d;
    size_t hl, dl;
    if (!as_u8s(s, &h, &hl, e) || !as_u8s(sep, &d, &dl, e))
        return false;
    if (dl == 0) {
        seterr(e, "split: empty separator");
        return false;
    }
    Val *parts = NULL;
    size_t np = 0, cap = 0;
    size_t start = 0, i = 0;
    while (i + dl <= hl) {
        if (!memcmp(h + i, d, dl)) {
            if (np == cap) {
                cap = cap ? cap * 2 : 8;
                parts = realloc(parts, cap * sizeof(Val));
            }
            parts[np++] = u8s_val(h + start, i - start);
            i += dl;
            start = i;
        } else
            i++;
    }
    if (np == cap) {
        cap = cap ? cap * 2 : 8;
        parts = realloc(parts, cap * sizeof(Val));
    }
    parts[np++] = u8s_val(h + start, hl - start);
    Col *c;
    bool ok = col_from_vals(parts, np, &c, e);
    free(parts);
    if (!ok)
        return false;
    Val v;
    v.k = V_VEC;
    v.u.vec = c;
    *out = v;
    return true;
}
bool op_join(const Val *sep, const Val *parts_v, Val *out, SnelErr *e) {
    uint8_t *d;
    size_t dl;
    if (!as_u8s(sep, &d, &dl, e))
        return false;
    if (parts_v->k != V_VEC) {
        seterr(e, "join needs (str, [str])");
        return false;
    }
    const Col *parts = parts_v->u.vec;
    uint8_t *o = NULL;
    size_t on = 0, cap = 0;
    for (size_t i = 0; i < parts->len; i++) {
        Val el = col_elem(parts, i);
        uint8_t *eb;
        size_t el_n;
        if (!as_u8s(&el, &eb, &el_n, e)) {
            val_drop(el);
            return false;
        }
        size_t need = on + (i > 0 ? dl : 0) + el_n;
        if (need > cap) {
            cap = need * 2 + 8;
            o = realloc(o, cap);
        }
        if (i > 0) {
            memcpy(o + on, d, dl);
            on += dl;
        }
        memcpy(o + on, eb, el_n);
        on += el_n;
        free(eb);
        val_drop(el);
    }
    *out = u8s_val(o, on);
    return true;
}

// ---------- aggregates ----------
bool op_sum(const Col *c, Val *out, SnelErr *e) {
    if (!is_simple(c)) {
        seterr(e, "sum needs a numeric or bit vec");
        return false;
    }
    if (c->cases[0].k == P_BITS) {
        size_t s = 0;
        for (size_t i = 0; i < c->len; i++)
            if ((!c->has_present || bits_get(&c->present, i)) && bits_get(&c->cases[0].u.bits, i))
                s++;
        *out = vi64((int64_t)s);
        return true;
    }
    if (c->cases[0].k == P_I64S) {
        int64_t s = 0;
        for (size_t i = 0; i < c->len; i++)
            if (!c->has_present || bits_get(&c->present, i))
                s = (int64_t)((uint64_t)s + (uint64_t)c->cases[0].u.i64[i]);
        *out = vi64(s);
        return true;
    }
    if (c->cases[0].k == P_F64S) {
        double s = 0;
        for (size_t i = 0; i < c->len; i++)
            if (!c->has_present || bits_get(&c->present, i))
                s += c->cases[0].u.f64[i];
        *out = vf64(canon_f64(s));
        return true;
    }
    seterr(e, "sum needs a numeric or bit vec");
    return false;
}
bool op_minmax(const Col *c, bool want_min, Val *out, SnelErr *e) {
    (void)e;
    bool have = false;
    Val best = vnil();
    for (size_t i = 0; i < c->len; i++) {
        Val v = col_elem(c, i);
        if (v.k == V_NIL) {
            continue;
        }
        if (!have) {
            best = v;
            have = true;
        } else {
            int o = cmp_val(&v, &best);
            if ((want_min && o < 0) || (!want_min && o > 0)) {
                val_drop(best);
                best = v;
            } else
                val_drop(v);
        }
    }
    *out = best;
    return true;
}
// qsort context: the column being graded (the interpreter is single-threaded)
static const Col *g_grade_col;
static int grade_cmp(const void *pa, const void *pb) {
    int64_t ia = *(const int64_t *)pa, ib = *(const int64_t *)pb;
    Val a = col_elem(g_grade_col, (size_t)ia), b = col_elem(g_grade_col, (size_t)ib);
    int o = cmp_val(&a, &b);
    val_drop(a);
    val_drop(b);
    // tie-break on the original index -> a total order, so the result is a
    // stable sort (identical to Rust's sort_by on a stable sort)
    return o ? o : (ia < ib ? -1 : ia > ib ? 1 : 0);
}
Val op_grade(const Col *c) {
    size_t n = c->len;
    int64_t *ix = malloc((n ? n : 1) * sizeof(int64_t));
    for (size_t i = 0; i < n; i++)
        ix[i] = (int64_t)i;
    g_grade_col = c;
    qsort(ix, n, sizeof(int64_t), grade_cmp);
    Payload p;
    p.k = P_I64S;
    p.u.i64 = ix;
    Col *col = malloc(sizeof(Col));
    col->rc = 1;
    col->len = n;
    col->ncases = 1;
    col->cases[0] = p;
    col->has_present = false;
    col->has_sel = false;
    col->sel = NULL;
    return vvec(col);
}
Val op_isnil(const Val *v) {
    if (v->k == V_VEC) {
        Col *c = v->u.vec;
        Bits b = bits_new(0, false);
        for (size_t i = 0; i < c->len; i++)
            bits_push(&b, c->has_present && !bits_get(&c->present, i));
        Payload p;
        p.k = P_BITS;
        p.u.bits = b;
        return vvec(col_simple(p));
    }
    return vbit(v->k == V_NIL);
}
bool op_cat(const Val *a, const Val *b, Val *out, SnelErr *e) {
    if (a->k != V_VEC || b->k != V_VEC) {
        seterr(e, "cat needs two vecs");
        return false;
    }
    Col *x = a->u.vec, *y = b->u.vec;
    size_t n = x->len + y->len;
    Val *vals = malloc((n ? n : 1) * sizeof(Val));
    for (size_t i = 0; i < x->len; i++)
        vals[i] = col_elem(x, i);
    for (size_t i = 0; i < y->len; i++)
        vals[x->len + i] = col_elem(y, i);
    Col *tmp;
    bool ok = col_from_vals(vals, n, &tmp, e); // consumes the element values
    free(vals);
    if (!ok)
        return false;
    // union of the two element types
    Ty tx = col_ty(x), ty = col_ty(y);
    Ty parts[2] = {tx, ty};
    extern Ty union_of_pub(Ty *, size_t);
    Ty u = union_of_pub(parts, 2);
    Col *r;
    ok = coerce_col(tmp, &u, &r, e);
    col_release(tmp);
    if (!ok)
        return false;
    *out = vvec(r);
    return true;
}
static Col *i64_col(int64_t *v, size_t n) {
    Payload p;
    p.k = P_I64S;
    p.u.i64 = v;
    Col *c = malloc(sizeof(Col));
    c->rc = 1;
    c->len = n;
    c->ncases = 1;
    c->cases[0] = p;
    c->has_present = false;
    c->has_sel = false;
    c->sel = NULL;
    return c;
}
static Col *f64_col(double *v, size_t n) {
    Payload p;
    p.k = P_F64S;
    p.u.f64 = v;
    Col *c = malloc(sizeof(Col));
    c->rc = 1;
    c->len = n;
    c->ncases = 1;
    c->cases[0] = p;
    c->has_present = false;
    c->has_sel = false;
    c->sel = NULL;
    return c;
}
static bool from_elems(Val *vals, size_t n, Val *out, SnelErr *e) {
    Col *c;
    bool ok = col_from_vals(vals, n, &c, e); // consumes the values
    free(vals);
    if (!ok)
        return false;
    *out = vvec(c);
    return true;
}
// Build a sub-column, preserving the source's static element type so an empty
// slice of a [u8] is still a [u8] (not an untyped empty column).
static bool slice_col(const Col *src, Val *vals, size_t n, Val *out, SnelErr *e) {
    Col *tmp;
    bool ok = col_from_vals(vals, n, &tmp, e);
    free(vals);
    if (!ok)
        return false;
    Ty t = col_ty(src);
    Col *r;
    ok = coerce_col(tmp, &t, &r, e);
    col_release(tmp);
    if (!ok)
        return false;
    *out = vvec(r);
    return true;
}
bool op_rev(const Val *v, Val *out, SnelErr *e) {
    if (v->k != V_VEC) {
        seterr(e, "rev needs a vec");
        return false;
    }
    Col *c = v->u.vec;
    size_t n = c->len;
    Val *vals = malloc((n ? n : 1) * sizeof(Val));
    for (size_t i = 0; i < n; i++)
        vals[i] = col_elem(c, n - 1 - i);
    return from_elems(vals, n, out, e);
}
bool op_take(int64_t nn, const Val *v, Val *out, SnelErr *e) {
    if (v->k != V_VEC) {
        seterr(e, "take needs a vec");
        return false;
    }
    Col *c = v->u.vec;
    size_t len = c->len, k = nn < 0 ? 0 : ((size_t)nn > len ? len : (size_t)nn);
    Val *vals = malloc((k ? k : 1) * sizeof(Val));
    for (size_t i = 0; i < k; i++)
        vals[i] = col_elem(c, i);
    return slice_col(c, vals, k, out, e);
}
bool op_drop(int64_t nn, const Val *v, Val *out, SnelErr *e) {
    if (v->k != V_VEC) {
        seterr(e, "drop needs a vec");
        return false;
    }
    Col *c = v->u.vec;
    size_t len = c->len, k = nn < 0 ? 0 : ((size_t)nn > len ? len : (size_t)nn), m = len - k;
    Val *vals = malloc((m ? m : 1) * sizeof(Val));
    for (size_t i = 0; i < m; i++)
        vals[i] = col_elem(c, k + i);
    return slice_col(c, vals, m, out, e);
}
// element at a scalar index (the scalar counterpart of gather `v[idxs]`).
bool op_at(const Val *v, int64_t i, Val *out, SnelErr *e) {
    if (v->k != V_VEC) {
        seterr(e, "at needs a vec");
        return false;
    }
    Col *c = v->u.vec;
    if (i < 0 || (size_t)i >= c->len) {
        seterr(e, "at: index out of bounds");
        return false;
    }
    *out = col_elem(c, (size_t)i);
    return true;
}
// n copies of a scalar, as a typed vector (the vector-model constant).
bool op_rep(int64_t n, const Val *x, Val *out, SnelErr *e) {
    if (n < 0) {
        seterr(e, "rep of negative length");
        return false;
    }
    Val *vals = malloc(((size_t)(n > 0 ? n : 1)) * sizeof(Val));
    for (size_t i = 0; i < (size_t)n; i++)
        vals[i] = val_clone(*x);
    Col *tmp;
    bool ok = col_from_vals(vals, (size_t)n, &tmp, e);
    free(vals);
    if (!ok)
        return false;
    Ty t = val_ty(x);
    Col *r;
    ok = coerce_col(tmp, &t, &r, e);
    col_release(tmp);
    if (!ok)
        return false;
    *out = vvec(r);
    return true;
}
// `base` with base[idx[k]] := vals[k] (later writes win); scalar vals broadcast.
bool op_scatter(const Val *base, const Val *idx, const Val *vals, Val *out, SnelErr *e) {
    if (base->k != V_VEC || idx->k != V_VEC) {
        seterr(e, "scatter needs vecs");
        return false;
    }
    Col *bc = base->u.vec, *ic = idx->u.vec;
    Col *vc = vals->k == V_VEC ? vals->u.vec : NULL;
    if (vc && vc->len != ic->len) {
        seterr(e, "scatter: index/value length mismatch");
        return false;
    }
    Val *o = malloc((bc->len ? bc->len : 1) * sizeof(Val));
    for (size_t i = 0; i < bc->len; i++)
        o[i] = col_elem(bc, i);
    for (size_t k = 0; k < ic->len; k++) {
        Val jv = col_elem(ic, k);
        if (jv.k != V_I64) {
            seterr(e, "scatter indices must be [i64]");
            return false;
        }
        int64_t j = jv.u.i;
        if (j < 0 || (size_t)j >= bc->len) {
            seterr(e, "scatter: index out of bounds");
            return false;
        }
        val_drop(o[j]);
        o[j] = vc ? col_elem(vc, k) : val_clone(*vals);
    }
    Col *tmp;
    bool ok = col_from_vals(o, bc->len, &tmp, e);
    free(o);
    if (!ok)
        return false;
    Ty t = col_ty(bc);
    Col *r;
    ok = coerce_col(tmp, &t, &r, e);
    col_release(tmp);
    if (!ok)
        return false;
    *out = vvec(r);
    return true;
}
// shift by k with a fill: out[i] = v[i+k] when in range, else `fill`.
bool op_shift(const Val *v, int64_t k, const Val *fill, Val *out, SnelErr *e) {
    if (v->k != V_VEC) {
        seterr(e, "shift needs a vec");
        return false;
    }
    Col *c = v->u.vec;
    int64_t n = (int64_t)c->len;
    Val *vals = malloc((c->len ? c->len : 1) * sizeof(Val));
    for (int64_t i = 0; i < n; i++) {
        int64_t j = i + k;
        vals[i] = (j >= 0 && j < n) ? col_elem(c, (size_t)j) : val_clone(*fill);
    }
    return slice_col(c, vals, c->len, out, e);
}
// prefix (cumulative) sums; numeric vectors only.
static bool prefix(const Val *v, const char *who, bool mul, Val *out, SnelErr *e) {
    if (v->k != V_VEC) {
        seterr(e, who);
        return false;
    }
    Col *c = v->u.vec;
    if (!is_simple(c)) {
        seterr(e, who);
        return false;
    }
    if (c->cases[0].k == P_I64S) {
        int64_t acc = mul ? 1 : 0, *o = malloc((c->len ? c->len : 1) * sizeof(int64_t));
        for (size_t i = 0; i < c->len; i++) {
            Val x = col_elem(c, i);
            if (x.k == V_I64)
                acc = mul ? acc * x.u.i : acc + x.u.i;
            o[i] = acc;
        }
        *out = vvec(i64_col(o, c->len));
        return true;
    }
    if (c->cases[0].k == P_F64S) {
        double acc = mul ? 1 : 0, *o = malloc((c->len ? c->len : 1) * sizeof(double));
        for (size_t i = 0; i < c->len; i++) {
            Val x = col_elem(c, i);
            if (x.k == V_F64)
                acc = mul ? acc * x.u.f : acc + x.u.f;
            o[i] = canon_f64(acc);
        }
        *out = vvec(f64_col(o, c->len));
        return true;
    }
    seterr(e, who);
    return false;
}
bool op_sums(const Val *v, Val *out, SnelErr *e) {
    return prefix(v, "sums needs a numeric vec", false, out, e);
}
bool op_prods(const Val *v, Val *out, SnelErr *e) {
    return prefix(v, "prods needs a numeric vec", true, out, e);
}
bool op_first(const Val *v, Val *out, SnelErr *e) {
    if (v->k != V_VEC || v->u.vec->len == 0) {
        seterr(e, "first of empty vec");
        return false;
    }
    *out = col_elem(v->u.vec, 0);
    return true;
}
bool op_last(const Val *v, Val *out, SnelErr *e) {
    if (v->k != V_VEC || v->u.vec->len == 0) {
        seterr(e, "last of empty vec");
        return false;
    }
    *out = col_elem(v->u.vec, v->u.vec->len - 1);
    return true;
}
bool op_which(const Val *v, Val *out, SnelErr *e) {
    if (v->k != V_VEC) {
        seterr(e, "which needs a vec");
        return false;
    }
    Col *c = v->u.vec;
    int64_t *ix = malloc((c->len ? c->len : 1) * sizeof(int64_t));
    size_t k = 0;
    for (size_t i = 0; i < c->len; i++) {
        Val ev = col_elem(c, i);
        if (ev.k == V_BIT && ev.u.i)
            ix[k++] = (int64_t)i;
        val_drop(ev);
    }
    *out = vvec(i64_col(ix, k));
    return true;
}
bool op_distinct(const Val *v, Val *out, SnelErr *e) {
    if (v->k != V_VEC) {
        seterr(e, "distinct needs a vec");
        return false;
    }
    Col *c = v->u.vec;
    Val *kept = malloc((c->len ? c->len : 1) * sizeof(Val));
    size_t nk = 0;
    for (size_t i = 0; i < c->len; i++) {
        Val ev = col_elem(c, i);
        bool seen = false;
        for (size_t j = 0; j < nk; j++)
            if (cmp_val(&kept[j], &ev) == 0) {
                seen = true;
                break;
            }
        if (seen)
            val_drop(ev);
        else
            kept[nk++] = ev;
    }
    return from_elems(kept, nk, out, e);
}
// `in(x, v)`: does the set `v` contain the scalar `x`? (see op_member for the
// elementwise mask version)
bool op_contains(const Val *x, const Val *v, Val *out, SnelErr *e) {
    if (v->k != V_VEC) {
        seterr(e, "in needs a vec");
        return false;
    }
    Col *c = v->u.vec;
    bool found = false;
    for (size_t i = 0; i < c->len && !found; i++) {
        Val ev = col_elem(c, i);
        if (cmp_val(&ev, x) == 0)
            found = true;
        val_drop(ev);
    }
    *out = vbit(found);
    return true;
}

// ---------- sequence analysis (mirrors src/ops.rs) ----------
static Val bit_vvec(Bits bits) {
    Payload pl;
    memset(&pl, 0, sizeof pl);
    pl.k = P_BITS;
    pl.u.bits = bits;
    return vvec(col_simple(pl));
}

// mask over v: is each element equal to some element of `set`?
bool op_member(const Val *set, const Val *v, Val *out, SnelErr *e) {
    if (set->k != V_VEC || v->k != V_VEC) {
        seterr(e, "member needs (set, vec)");
        return false;
    }
    Col *s = set->u.vec, *c = v->u.vec;
    Bits bits = bits_new(0, false);
    for (size_t i = 0; i < c->len; i++) {
        Val ev = col_elem(c, i);
        bool found = false;
        for (size_t j = 0; j < s->len && !found; j++) {
            Val sv = col_elem(s, j);
            if (cmp_val(&sv, &ev) == 0)
                found = true;
            val_drop(sv);
        }
        val_drop(ev);
        bits_push(&bits, found);
    }
    *out = bit_vvec(bits);
    return true;
}

// mask over hay: does `needle` occur as a contiguous subsequence starting here?
bool op_matches(const Val *needle, const Val *hay, Val *out, SnelErr *e) {
    if (needle->k != V_VEC || hay->k != V_VEC) {
        seterr(e, "matches needs (needle, hay)");
        return false;
    }
    Col *n = needle->u.vec, *h = hay->u.vec;
    size_t m = n->len;
    Val *pat = malloc((m ? m : 1) * sizeof(Val));
    for (size_t j = 0; j < m; j++)
        pat[j] = col_elem(n, j);
    Bits bits = bits_new(0, false);
    for (size_t i = 0; i < h->len; i++) {
        bool ok = (i + m <= h->len);
        for (size_t j = 0; j < m && ok; j++) {
            Val hv = col_elem(h, i + j);
            if (cmp_val(&pat[j], &hv) != 0)
                ok = false;
            val_drop(hv);
        }
        bits_push(&bits, ok);
    }
    for (size_t j = 0; j < m; j++)
        val_drop(pat[j]);
    free(pat);
    *out = bit_vvec(bits);
    return true;
}

// mask: run-start boundaries — index 0, and each i where v[i] != v[i-1].
bool op_runs(const Val *v, Val *out, SnelErr *e) {
    if (v->k != V_VEC) {
        seterr(e, "runs needs a vec");
        return false;
    }
    Col *c = v->u.vec;
    Bits bits = bits_new(0, false);
    for (size_t i = 0; i < c->len; i++) {
        bool boundary = true;
        if (i > 0) {
            Val a = col_elem(c, i), b = col_elem(c, i - 1);
            boundary = cmp_val(&a, &b) != 0;
            val_drop(a);
            val_drop(b);
        }
        bits_push(&bits, boundary);
    }
    *out = bit_vvec(bits);
    return true;
}

// cut v into segments beginning at index 0 and at each set bit of `starts`.
bool op_partition(const Val *starts, const Val *v, Val *out, SnelErr *e) {
    if (starts->k != V_VEC || v->k != V_VEC) {
        seterr(e, "partition needs (mask, vec)");
        return false;
    }
    Col *m = starts->u.vec, *c = v->u.vec;
    if (m->len != c->len) {
        seterr(e, "partition: mask and vector must be the same length");
        return false;
    }
    size_t *bounds = malloc((c->len + 2) * sizeof(size_t));
    size_t nb = 0;
    if (c->len > 0)
        bounds[nb++] = 0;
    for (size_t i = 1; i < c->len; i++) {
        Val mv = col_elem(m, i);
        bool start = (mv.k == V_BIT && mv.u.i);
        val_drop(mv);
        if (start)
            bounds[nb++] = i;
    }
    bounds[nb] = c->len; // sentinel end
    Val *segs = malloc((nb ? nb : 1) * sizeof(Val));
    for (size_t g = 0; g < nb; g++) {
        size_t a = bounds[g], b = bounds[g + 1];
        Val *elems = malloc((b - a ? b - a : 1) * sizeof(Val));
        for (size_t i = a; i < b; i++)
            elems[i - a] = col_elem(c, i);
        if (!from_elems(elems, b - a, &segs[g], e)) {
            for (size_t gg = 0; gg < g; gg++)
                val_drop(segs[gg]);
            free(segs);
            free(bounds);
            return false;
        }
    }
    free(bounds);
    return from_elems(segs, nb, out, e);
}

// all overlapping length-k contiguous sub-vectors (len(v)-k+1 of them).
bool op_windows(int64_t k, const Val *v, Val *out, SnelErr *e) {
    if (v->k != V_VEC) {
        seterr(e, "windows needs a vec");
        return false;
    }
    if (k < 1) {
        seterr(e, "windows: k must be >= 1");
        return false;
    }
    Col *c = v->u.vec;
    size_t kk = (size_t)k;
    size_t nw = (kk <= c->len) ? (c->len - kk + 1) : 0;
    Val *ws = malloc((nw ? nw : 1) * sizeof(Val));
    for (size_t i = 0; i < nw; i++) {
        Val *elems = malloc(kk * sizeof(Val));
        for (size_t j = 0; j < kk; j++)
            elems[j] = col_elem(c, i + j);
        if (!from_elems(elems, kk, &ws[i], e)) {
            for (size_t ii = 0; ii < i; ii++)
                val_drop(ws[ii]);
            free(ws);
            return false;
        }
    }
    return from_elems(ws, nw, out, e);
}
bool op_all(const Val *v, Val *out, SnelErr *e) {
    if (v->k != V_VEC) {
        seterr(e, "all needs a vec");
        return false;
    }
    Col *c = v->u.vec;
    bool r = true;
    for (size_t i = 0; i < c->len && r; i++) {
        Val ev = col_elem(c, i);
        if (!(ev.k == V_BIT && ev.u.i))
            r = false;
        val_drop(ev);
    }
    *out = vbit(r);
    return true;
}
bool op_any(const Val *v, Val *out, SnelErr *e) {
    if (v->k != V_VEC) {
        seterr(e, "any needs a vec");
        return false;
    }
    Col *c = v->u.vec;
    bool r = false;
    for (size_t i = 0; i < c->len && !r; i++) {
        Val ev = col_elem(c, i);
        if (ev.k == V_BIT && ev.u.i)
            r = true;
        val_drop(ev);
    }
    *out = vbit(r);
    return true;
}
bool op_prod(const Col *c, Val *out, SnelErr *e) {
    if (!is_simple(c)) {
        seterr(e, "prod needs a numeric vec");
        return false;
    }
    if (c->cases[0].k == P_I64S) {
        int64_t s = 1;
        for (size_t i = 0; i < c->len; i++)
            if (!c->has_present || bits_get(&c->present, i))
                s = (int64_t)((uint64_t)s * (uint64_t)c->cases[0].u.i64[i]);
        *out = vi64(s);
        return true;
    }
    if (c->cases[0].k == P_F64S) {
        double s = 1;
        for (size_t i = 0; i < c->len; i++)
            if (!c->has_present || bits_get(&c->present, i))
                s *= c->cases[0].u.f64[i];
        *out = vf64(canon_f64(s));
        return true;
    }
    seterr(e, "prod needs a numeric vec");
    return false;
}
bool op_iota(int64_t n, Val *out, SnelErr *e) {
    if (n < 0) {
        seterr(e, "iota of negative length");
        return false;
    }
    int64_t *v = malloc((n ? n : 1) * sizeof(int64_t));
    for (int64_t i = 0; i < n; i++)
        v[i] = i;
    *out = vvec(i64_col(v, (size_t)n));
    return true;
}
bool op_group(Tab *t, const uint8_t *key, size_t keylen, Val *out, SnelErr *e) {
    Val *kc = tab_get(t, key, keylen);
    if (!kc || kc->k != V_VEC) {
        seterr(e, "group: no vec column");
        return false;
    }
    Col *kcol = kc->u.vec;
    Val keys[4096];
    size_t nkeys = 0;
    int64_t *buckets[4096];
    size_t bn[4096], bcap[4096];
    for (size_t i = 0; i < kcol->len; i++) {
        Val v = col_elem(kcol, i);
        int found = -1;
        for (size_t j = 0; j < nkeys; j++) {
            if (cmp_val(&keys[j], &v) == 0) {
                found = (int)j;
                break;
            }
        }
        if (found < 0) {
            keys[nkeys] = v;
            bn[nkeys] = 0;
            bcap[nkeys] = 4;
            buckets[nkeys] = malloc(4 * sizeof(int64_t));
            found = (int)nkeys;
            nkeys++;
        } else
            val_drop(v);
        if (bn[found] == bcap[found]) {
            bcap[found] *= 2;
            buckets[found] = realloc(buckets[found], bcap[found] * sizeof(int64_t));
        }
        buckets[found][bn[found]++] = (int64_t)i;
    }
    Val *rows = malloc((nkeys ? nkeys : 1) * sizeof(Val));
    for (size_t j = 0; j < nkeys; j++) {
        Payload p;
        p.k = P_I64S;
        p.u.i64 = malloc((bn[j] ? bn[j] : 1) * sizeof(int64_t));
        memcpy(p.u.i64, buckets[j], bn[j] * sizeof(int64_t));
        Col *ic = malloc(sizeof(Col));
        ic->rc = 1;
        ic->len = bn[j];
        ic->ncases = 1;
        ic->cases[0] = p;
        ic->has_present = false;
        ic->has_sel = false;
        ic->sel = NULL;
        Val ixv = vvec(ic);
        Val tv;
        tv.k = V_TAB;
        tv.u.tab = tab_retain(t);
        Val rowsv;
        if (!op_index(&tv, &ixv, &rowsv, e))
            return false;
        val_drop(tv);
        rows[j] = rowsv;
    }
    Tab *o = tab_new();
    Col *keycol_tmp;
    if (!col_from_vals(keys, nkeys, &keycol_tmp, e)) // keys is a stack array
        return false;
    Ty kt = col_ty(kcol);
    Col *keycol;
    bool ok = coerce_col(keycol_tmp, &kt, &keycol, e);
    col_release(keycol_tmp);
    if (!ok)
        return false;
    tab_bind(o, bin_new(key, keylen), vvec(keycol), NULL);
    Col *rowscol;
    ok = col_from_vals(rows, nkeys, &rowscol, e);
    free(rows);
    if (!ok)
        return false;
    tab_bind(o, bin_str("rows"), vvec(rowscol), NULL);
    Val v;
    v.k = V_TAB;
    v.u.tab = o;
    *out = v;
    return true;
}

// vectorized if
bool op_select(const Col *mask, Val t, Val e, Val *out, SnelErr *er) {
    if (mask->has_sel || mask->cases[0].k != P_BITS) {
        seterr(er, "if condition must be bit or [bit]");
        return false;
    }
    size_t n = mask->len;
    Val *vals = malloc((n ? n : 1) * sizeof(Val));
    for (size_t i = 0; i < n; i++) {
        bool on = bits_get(&mask->cases[0].u.bits, i) &&
                  (!mask->has_present || bits_get(&mask->present, i));
        Val src = on ? t : e;
        if (src.k == V_VEC) {
            if (src.u.vec->len != n) {
                seterr(er, "length mismatch");
                return false;
            }
            vals[i] = col_elem(src.u.vec, i);
        } else
            vals[i] = val_clone(src);
    }
    Col *r;
    bool ok = col_from_vals(vals, n, &r, er);
    free(vals);
    if (!ok)
        return false;
    *out = vvec(r);
    return true;
}
