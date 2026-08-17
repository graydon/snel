// One tagged binary format for every value. Mirrors src/wire.rs, including the
// 256-element chunk codec (raw/rle/pack/nullsup) and the type<->value and
// AST<->tab bijections. Buffers leak (short-lived process).
#include "snel.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

Node *node_new(AKind k, uint32_t lo);
bool is_u8_col(const Col *c);
uint8_t *col_bytes(const Col *c, size_t *len);

#define T_NILV 0
#define T_BIT0 1
#define T_BIT1 2
#define T_I64V 3
#define T_F64V 4
#define T_BINV 5
#define T_VECV 6
#define T_TABV 7
#define T_FUNV 8
#define T_PRIMV 9
#define CHUNK 256

// ---------- growable byte buffer ----------
typedef struct {
    uint8_t *p;
    size_t len, cap;
} Buf;
static void bput(Buf *b, const uint8_t *d, size_t n) {
    if (b->len + n > b->cap) {
        b->cap = (b->len + n) * 2 + 16;
        b->p = realloc(b->p, b->cap);
    }
    memcpy(b->p + b->len, d, n);
    b->len += n;
}
static void b1(Buf *b, uint8_t x) {
    bput(b, &x, 1);
}
static void bu32(Buf *b, uint32_t x) {
    uint8_t t[4];
    for (int i = 0; i < 4; i++)
        t[i] = x >> (8 * i);
    bput(b, t, 4);
}
static void bu16(Buf *b, uint16_t x) {
    uint8_t t[2] = {x, x >> 8};
    bput(b, t, 2);
}
static void bi64(Buf *b, int64_t x) {
    uint8_t t[8];
    uint64_t u = (uint64_t)x;
    for (int i = 0; i < 8; i++)
        t[i] = u >> (8 * i);
    bput(b, t, 8);
}
static void bbin(Buf *b, const Bin *bn) {
    bu32(b, bn->len);
    bput(b, bin_bytes(bn), bn->len);
}

Val ty_to_val(const Ty *t);
Val ast_to_val(const Node *n);

static void encode_col(const Col *c, Buf *b);
static void encode_tab(const Tab *t, Buf *b);

void encode_val_buf(const Val *v, Buf *b) {
    switch (v->k) {
        case V_U8:
            b1(b, T_BINV);
            b1(b, (uint8_t)(v->u.i & 0xff));
            break; // T_BINV reused as u8 tag
        case V_NIL:
            b1(b, T_NILV);
            break;
        case V_BIT:
            b1(b, v->u.i ? T_BIT1 : T_BIT0);
            break;
        case V_I64:
            b1(b, T_I64V);
            bi64(b, v->u.i);
            break;
        case V_F64: {
            b1(b, T_F64V);
            uint64_t u;
            memcpy(&u, &v->u.f, 8);
            bi64(b, (int64_t)u);
        } break;

        case V_VEC:
            b1(b, T_VECV);
            encode_col(v->u.vec, b);
            break;
        case V_TAB:
            b1(b, T_TABV);
            encode_tab(v->u.tab, b);
            break;
        case V_FUN: {
            Clo *c = v->u.fun;
            b1(b, T_FUNV);
            bu32(b, c->nparams);
            for (size_t i = 0; i < c->nparams; i++) {
                bbin(b, &c->params[i]);
                Val tv = ty_to_val(&c->ptypes[i]);
                encode_val_buf(&tv, b);
            }
            Val rv = ty_to_val(&c->ret);
            encode_val_buf(&rv, b);
            Val bv = ast_to_val(c->body);
            encode_val_buf(&bv, b);
            encode_tab(c->env, b);
        } break;
        case V_PRIM:
            b1(b, T_PRIMV);
            bbin(b, &v->u.bin);
            break;
    }
}

static void encode_tab(const Tab *t, Buf *b) {
    bu32(b, t->len);
    for (size_t i = 0; i < t->len; i++) {
        bbin(b, &t->keys[i]);
        if (t->has_doc[i]) {
            b1(b, 1);
            bbin(b, &t->docs[i]);
        } else
            b1(b, 0);
        encode_val_buf(&t->vals[i], b);
    }
}

// ----- chunk codecs -----
static void enc_bits(const Bits *bt, Buf *b) {
    size_t i = 0;
    while (i < bt->len) {
        size_t n = bt->len - i;
        if (n > CHUNK)
            n = CHUNK;
        bool allz = true, allo = true;
        for (size_t j = 0; j < n; j++) {
            bool v = bits_get(bt, i + j);
            if (v)
                allz = false;
            else
                allo = false;
        }
        if (allz)
            b1(b, 1);
        else if (allo)
            b1(b, 2);
        else {
            b1(b, 0);
            size_t nb = (n + 7) / 8;
            uint8_t *bytes = calloc(nb, 1);
            for (size_t j = 0; j < n; j++)
                if (bits_get(bt, i + j))
                    bytes[j / 8] |= 1 << (j % 8);
            bput(b, bytes, nb);
            free(bytes);
        }
        i += n;
    }
}
static void enc_u8s(const uint8_t *v, size_t len, Buf *b) {
    for (size_t off = 0; off < len; off += CHUNK) {
        size_t n = len - off;
        if (n > CHUNK)
            n = CHUNK;
        // rle runs
        size_t nruns = 0;
        for (size_t i = 0; i < n;) {
            size_t j = i;
            while (j < n && v[off + j] == v[off + i] && j - i < 255)
                j++;
            nruns++;
            i = j;
        }
        if (2 + nruns * 2 < n) {
            b1(b, 1);
            bu16(b, (uint16_t)nruns);
            for (size_t i = 0; i < n;) {
                size_t j = i;
                while (j < n && v[off + j] == v[off + i] && j - i < 255)
                    j++;
                b1(b, (uint8_t)(j - i - 1));
                b1(b, v[off + i]);
                i = j;
            }
        } else {
            b1(b, 0);
            bput(b, v + off, n);
        }
    }
}
static uint64_t zigzag(int64_t x) {
    return ((uint64_t)x << 1) ^ (uint64_t)(x >> 63);
}
static int64_t unzigzag(uint64_t x) {
    return (int64_t)(x >> 1) ^ -(int64_t)(x & 1);
}
static void enc_i64s(const int64_t *v, size_t len, Buf *b) {
    for (size_t off = 0; off < len; off += CHUNK) {
        size_t n = len - off;
        if (n > CHUNK)
            n = CHUNK;
        size_t raw = n * 8;
        size_t nruns = 0;
        for (size_t i = 0; i < n;) {
            size_t j = i;
            while (j < n && v[off + j] == v[off + i] && j - i < 255)
                j++;
            nruns++;
            i = j;
        }
        size_t rle = 2 + nruns * 9;
        int width = 0;
        for (size_t i = 0; i < n; i++) {
            uint64_t z = zigzag(v[off + i]);
            int w = 0;
            while (z) {
                w++;
                z >>= 8;
            }
            if (w > width)
                width = w;
        }
        size_t packed = 1 + n * width;
        size_t best = raw < rle ? raw : rle;
        if (packed < best)
            best = packed;
        if (best == raw) {
            b1(b, 0);
            for (size_t i = 0; i < n; i++)
                bi64(b, v[off + i]);
        } else if (best == rle) {
            b1(b, 1);
            bu16(b, (uint16_t)nruns);
            for (size_t i = 0; i < n;) {
                size_t j = i;
                while (j < n && v[off + j] == v[off + i] && j - i < 255)
                    j++;
                b1(b, (uint8_t)(j - i - 1));
                bi64(b, v[off + i]);
                i = j;
            }
        } else {
            b1(b, 2);
            b1(b, (uint8_t)width);
            for (size_t i = 0; i < n; i++) {
                uint64_t z = zigzag(v[off + i]);
                for (int k = 0; k < width; k++)
                    b1(b, z >> (8 * k));
            }
        }
    }
}
static void enc_f64s(const double *v, size_t len, Buf *b) {
    for (size_t off = 0; off < len; off += CHUNK) {
        size_t n = len - off;
        if (n > CHUNK)
            n = CHUNK;
        uint64_t *bits = malloc((n ? n : 1) * 8);
        for (size_t i = 0; i < n; i++)
            memcpy(&bits[i], &v[off + i], 8);
        size_t nruns = 0;
        for (size_t i = 0; i < n;) {
            size_t j = i;
            while (j < n && bits[j] == bits[i] && j - i < 255)
                j++;
            nruns++;
            i = j;
        }
        if (2 + nruns * 9 < n * 8) {
            b1(b, 1);
            bu16(b, (uint16_t)nruns);
            for (size_t i = 0; i < n;) {
                size_t j = i;
                while (j < n && bits[j] == bits[i] && j - i < 255)
                    j++;
                b1(b, (uint8_t)(j - i - 1));
                bi64(b, (int64_t)bits[i]);
                i = j;
            }
        } else {
            b1(b, 0);
            for (size_t i = 0; i < n; i++)
                bi64(b, (int64_t)bits[i]);
        }
        free(bits);
    }
}

static uint8_t payload_wire_kind(const Payload *p) {
    switch (p->k) {
        case P_BITS:
            return 1;
        case P_I64S:
            return 2;
        case P_F64S:
            return 3;
        case P_U8S:
            return 4;
        case P_VECS:
            return 5;
        default:
            return 6;
    }
}
static void encode_col(const Col *c, Buf *b) {
    bu32(b, c->len);
    uint8_t flags = 0;
    if (c->has_present)
        flags |= 1;
    if (c->has_sel)
        flags |= 2;
    b1(b, flags);
    b1(b, c->ncases);
    for (int i = 0; i < c->ncases; i++)
        b1(b, payload_wire_kind(&c->cases[i]));
    if (c->has_present)
        enc_bits(&c->present, b);
    if (c->has_sel)
        enc_u8s(c->sel, c->len, b);
    for (int i = 0; i < c->ncases; i++) {
        const Payload *p = &c->cases[i];
        switch (p->k) {
            case P_BITS:
                enc_bits(&p->u.bits, b);
                break;
            case P_I64S:
                enc_i64s(p->u.i64, c->len, b);
                break;
            case P_F64S:
                enc_f64s(p->u.f64, c->len, b);
                break;
            case P_U8S:
                enc_u8s(bin_bytes(&p->u.u8s), c->len, b);
                break;
            case P_VECS:
                for (size_t j = 0; j < c->len; j++)
                    encode_col(p->u.vecs[j], b);
                break;
            case P_TABS:
                for (size_t j = 0; j < c->len; j++)
                    encode_tab(p->u.tab[j], b);
                break;
        }
    }
}

void encode_val(const Val *v, uint8_t **buf, size_t *len, size_t *cap) {
    Buf b = {*buf, *len, *cap};
    encode_val_buf(v, &b);
    *buf = b.p;
    *len = b.len;
    *cap = b.cap;
}

// ---------- decode ----------
typedef struct {
    const uint8_t *b;
    size_t len, i;
    SnelErr *e;
} Rd;
static bool need(Rd *r, size_t n) {
    if (r->i + n > r->len) {
        snprintf(r->e->msg, sizeof r->e->msg, "truncated");
        return false;
    }
    return true;
}
static bool ru8(Rd *r, uint8_t *o) {
    if (!need(r, 1))
        return false;
    *o = r->b[r->i++];
    return true;
}
static bool ru16(Rd *r, uint16_t *o) {
    if (!need(r, 2))
        return false;
    *o = r->b[r->i] | (r->b[r->i + 1] << 8);
    r->i += 2;
    return true;
}
static bool ru32(Rd *r, uint32_t *o) {
    if (!need(r, 4))
        return false;
    *o = 0;
    for (int i = 0; i < 4; i++)
        *o |= (uint32_t)r->b[r->i + i] << (8 * i);
    r->i += 4;
    return true;
}
static bool ri64(Rd *r, int64_t *o) {
    if (!need(r, 8))
        return false;
    uint64_t u = 0;
    for (int i = 0; i < 8; i++)
        u |= (uint64_t)r->b[r->i + i] << (8 * i);
    r->i += 8;
    *o = (int64_t)u;
    return true;
}
static bool rbin(Rd *r, Bin *o) {
    uint32_t n;
    if (!ru32(r, &n))
        return false;
    if (!need(r, n))
        return false;
    *o = bin_new(r->b + r->i, n);
    r->i += n;
    return true;
}

static bool decode_val_rd(Rd *r, Val *out);
static bool decode_tab(Rd *r, Tab **out);
bool val_to_ty(const Val *v, Ty *out);
bool val_to_ast(const Val *v, Node **out, SnelErr *err);

static bool dec_bits(Rd *r, size_t len, Bits *out) {
    Bits b = bits_new(0, false);
    size_t i = 0;
    while (i < len) {
        size_t n = len - i;
        if (n > CHUNK)
            n = CHUNK;
        uint8_t tag;
        if (!ru8(r, &tag))
            return false;
        if (tag == 1) {
            for (size_t j = 0; j < n; j++)
                bits_push(&b, false);
        } else if (tag == 2) {
            for (size_t j = 0; j < n; j++)
                bits_push(&b, true);
        } else if (tag == 0) {
            size_t nb = (n + 7) / 8;
            if (!need(r, nb))
                return false;
            for (size_t j = 0; j < n; j++)
                bits_push(&b, (r->b[r->i + j / 8] >> (j % 8)) & 1);
            r->i += nb;
        } else {
            snprintf(r->e->msg, sizeof r->e->msg, "bad bit chunk");
            return false;
        }
        i += n;
    }
    *out = b;
    return true;
}
static bool dec_u8s(Rd *r, size_t len, uint8_t **out) {
    uint8_t *v = malloc(len ? len : 1);
    size_t got = 0;
    while (got < len) {
        size_t n = len - got;
        if (n > CHUNK)
            n = CHUNK;
        uint8_t tag;
        if (!ru8(r, &tag))
            return false;
        if (tag == 0) {
            if (!need(r, n))
                return false;
            memcpy(v + got, r->b + r->i, n);
            r->i += n;
            got += n;
        } else if (tag == 1) {
            uint16_t nr;
            if (!ru16(r, &nr))
                return false;
            for (int k = 0; k < nr; k++) {
                uint8_t rl, vl;
                if (!ru8(r, &rl) || !ru8(r, &vl))
                    return false;
                for (int m = 0; m <= rl; m++)
                    v[got++] = vl;
            }
        } else {
            snprintf(r->e->msg, sizeof r->e->msg, "bad u8 chunk");
            return false;
        }
    }
    *out = v;
    return true;
}
static bool dec_i64s(Rd *r, size_t len, int64_t **out) {
    int64_t *v = malloc((len ? len : 1) * sizeof(int64_t));
    size_t got = 0;
    while (got < len) {
        size_t n = len - got;
        if (n > CHUNK)
            n = CHUNK;
        uint8_t tag;
        if (!ru8(r, &tag))
            return false;
        if (tag == 0) {
            for (size_t i = 0; i < n; i++) {
                if (!ri64(r, &v[got]))
                    return false;
                got++;
            }
        } else if (tag == 1) {
            uint16_t nr;
            if (!ru16(r, &nr))
                return false;
            for (int k = 0; k < nr; k++) {
                uint8_t rl;
                int64_t vl;
                if (!ru8(r, &rl) || !ri64(r, &vl))
                    return false;
                for (int m = 0; m <= rl; m++)
                    v[got++] = vl;
            }
        } else if (tag == 2) {
            uint8_t w;
            if (!ru8(r, &w))
                return false;
            if (w > 8) {
                snprintf(r->e->msg, sizeof r->e->msg, "bad width");
                return false;
            }
            for (size_t i = 0; i < n; i++) {
                if (!need(r, w))
                    return false;
                uint64_t z = 0;
                for (int k = 0; k < w; k++)
                    z |= (uint64_t)r->b[r->i + k] << (8 * k);
                r->i += w;
                v[got++] = unzigzag(z);
            }
        } else {
            snprintf(r->e->msg, sizeof r->e->msg, "bad i64 chunk");
            return false;
        }
    }
    *out = v;
    return true;
}
static bool dec_f64s(Rd *r, size_t len, double **out) {
    double *v = malloc((len ? len : 1) * sizeof(double));
    size_t got = 0;
    while (got < len) {
        size_t n = len - got;
        if (n > CHUNK)
            n = CHUNK;
        uint8_t tag;
        if (!ru8(r, &tag))
            return false;
        if (tag == 0) {
            for (size_t i = 0; i < n; i++) {
                int64_t u;
                if (!ri64(r, &u))
                    return false;
                uint64_t uu = (uint64_t)u;
                memcpy(&v[got], &uu, 8);
                got++;
            }
        } else if (tag == 1) {
            uint16_t nr;
            if (!ru16(r, &nr))
                return false;
            for (int k = 0; k < nr; k++) {
                uint8_t rl;
                int64_t u;
                if (!ru8(r, &rl) || !ri64(r, &u))
                    return false;
                uint64_t uu = (uint64_t)u;
                double d;
                memcpy(&d, &uu, 8);
                for (int m = 0; m <= rl; m++)
                    v[got++] = d;
            }
        } else {
            snprintf(r->e->msg, sizeof r->e->msg, "bad f64 chunk");
            return false;
        }
    }
    *out = v;
    return true;
}

static bool decode_col(Rd *r, Col **out) {
    uint32_t len;
    uint8_t flags, nc;
    if (!ru32(r, &len) || !ru8(r, &flags) || !ru8(r, &nc))
        return false;
    if (nc == 0 || nc > 8) {
        snprintf(r->e->msg, sizeof r->e->msg, "bad case count");
        return false;
    }
    uint8_t kinds[8];
    for (int i = 0; i < nc; i++)
        if (!ru8(r, &kinds[i]))
            return false;
    Col *c = malloc(sizeof(Col));
    c->rc = 1;
    c->len = len;
    c->ncases = nc;
    c->has_present = flags & 1;
    c->has_sel = flags & 2;
    c->sel = NULL;
    if (c->has_present) {
        if (!dec_bits(r, len, &c->present))
            return false;
    }
    if (c->has_sel) {
        if (!dec_u8s(r, len, &c->sel))
            return false;
    }
    for (int i = 0; i < nc; i++) {
        Payload *p = &c->cases[i];
        switch (kinds[i]) {
            case 1:
                p->k = P_BITS;
                if (!dec_bits(r, len, &p->u.bits))
                    return false;
                break;
            case 2:
                p->k = P_I64S;
                if (!dec_i64s(r, len, &p->u.i64))
                    return false;
                break;
            case 3:
                p->k = P_F64S;
                if (!dec_f64s(r, len, &p->u.f64))
                    return false;
                break;
            case 4: {
                p->k = P_U8S;
                uint8_t *bs;
                if (!dec_u8s(r, len, &bs))
                    return false;
                p->u.u8s = bin_new(bs, len);
                free(bs);
            } break;
            case 5:
                p->k = P_VECS;
                p->u.vecs = malloc((len ? len : 1) * sizeof(Col *));
                for (uint32_t j = 0; j < len; j++)
                    if (!decode_col(r, &p->u.vecs[j]))
                        return false;
                break;
            case 6:
                p->k = P_TABS;
                p->u.tab = malloc((len ? len : 1) * sizeof(Tab *));
                for (uint32_t j = 0; j < len; j++)
                    if (!decode_tab(r, &p->u.tab[j]))
                        return false;
                break;
            default:
                snprintf(r->e->msg, sizeof r->e->msg, "bad payload kind");
                return false;
        }
    }
    if (c->has_sel)
        for (uint32_t j = 0; j < len; j++)
            if (c->sel[j] >= nc) {
                snprintf(r->e->msg, sizeof r->e->msg, "selector out of range");
                return false;
            }
    *out = c;
    return true;
}
static bool decode_tab(Rd *r, Tab **out) {
    uint32_t n;
    if (!ru32(r, &n))
        return false;
    Tab *t = tab_new();
    for (uint32_t i = 0; i < n; i++) {
        Bin k;
        if (!rbin(r, &k))
            return false;
        uint8_t hd;
        if (!ru8(r, &hd))
            return false;
        Bin doc;
        bool has = false;
        if (hd == 1) {
            if (!rbin(r, &doc))
                return false;
            has = true;
        }
        Val v;
        if (!decode_val_rd(r, &v))
            return false;
        tab_bind(t, k, v, has ? &doc : NULL);
    }
    *out = t;
    return true;
}
static bool decode_val_rd(Rd *r, Val *out) {
    uint8_t tag;
    if (!ru8(r, &tag))
        return false;
    switch (tag) {
        case T_NILV:
            *out = vnil();
            return true;
        case T_BIT0:
            *out = vbit(false);
            return true;
        case T_BIT1:
            *out = vbit(true);
            return true;
        case T_I64V: {
            int64_t x;
            if (!ri64(r, &x))
                return false;
            *out = vi64(x);
            return true;
        }
        case T_F64V: {
            int64_t u;
            if (!ri64(r, &u))
                return false;
            uint64_t uu = (uint64_t)u;
            double d;
            memcpy(&d, &uu, 8);
            *out = vf64(canon_f64(d));
            return true;
        }
        case T_BINV: {
            uint8_t x;
            if (!ru8(r, &x))
                return false;
            Val v;
            v.k = V_U8;
            v.u.i = x;
            *out = v;
            return true;
        }
        case T_VECV: {
            Col *c;
            if (!decode_col(r, &c))
                return false;
            Val v;
            v.k = V_VEC;
            v.u.vec = c;
            *out = v;
            return true;
        }
        case T_TABV: {
            Tab *t;
            if (!decode_tab(r, &t))
                return false;
            Val v;
            v.k = V_TAB;
            v.u.tab = t;
            *out = v;
            return true;
        }
        case T_FUNV: {
            uint32_t np;
            if (!ru32(r, &np))
                return false;
            Clo *c = malloc(sizeof(Clo));
            c->rc = 1;
            c->nparams = np;
            c->params = malloc((np ? np : 1) * sizeof(Bin));
            c->ptypes = malloc((np ? np : 1) * sizeof(Ty));
            for (uint32_t i = 0; i < np; i++) {
                if (!rbin(r, &c->params[i]))
                    return false;
                Val tv;
                if (!decode_val_rd(r, &tv))
                    return false;
                if (!val_to_ty(&tv, &c->ptypes[i])) {
                    snprintf(r->e->msg, sizeof r->e->msg, "bad param type");
                    return false;
                }
            }
            Val rv;
            if (!decode_val_rd(r, &rv))
                return false;
            if (!val_to_ty(&rv, &c->ret)) {
                snprintf(r->e->msg, sizeof r->e->msg, "bad ret type");
                return false;
            }
            Val bv;
            if (!decode_val_rd(r, &bv))
                return false;
            if (!val_to_ast(&bv, &c->body, r->e))
                return false;
            if (!decode_tab(r, &c->env))
                return false;
            Val v;
            v.k = V_FUN;
            v.u.fun = c;
            *out = v;
            return true;
        }
        case T_PRIMV: {
            Bin b;
            if (!rbin(r, &b))
                return false;
            Val v;
            v.k = V_PRIM;
            v.u.bin = b;
            *out = v;
            return true;
        }
        default:
            snprintf(r->e->msg, sizeof r->e->msg, "bad value tag");
            return false;
    }
}

bool decode_val(const uint8_t *buf, size_t len, size_t *pos, Val *out, SnelErr *e) {
    Rd r = {buf, len, *pos, e};
    if (!decode_val_rd(&r, out))
        return false;
    *pos = r.i;
    return true;
}

// ---------- identifiers as [u8] strings ----------
// The AST-as-tab encoding is all data now: identifiers (kinds, names, type
// names) are [u8] strings.
static Val vstr(const char *s) {
    Val v;
    v.k = V_VEC;
    v.u.vec = col_u8s((const uint8_t *)s, strlen(s));
    return v;
}
static Val vstr_b(const Bin *b) {
    Val v;
    v.k = V_VEC;
    v.u.vec = col_u8s(bin_bytes(b), b->len);
    return v;
}
// extract [u8] bytes of a string value into a Bin; false if v isn't a [u8]
static bool sb(const Val *v, Bin *out) {
    if (v->k != V_VEC || !is_u8_col(v->u.vec))
        return false;
    size_t n;
    uint8_t *b = col_bytes(v->u.vec, &n);
    *out = bin_new(b, n);
    free(b);
    return true;
}

// ---------- type <-> value ----------
static Val vec_of(Val *vals, size_t n) {
    Col *c;
    SnelErr e;
    if (!col_from_vals(vals, n, &c, &e))
        abort();
    Val v;
    v.k = V_VEC;
    v.u.vec = c;
    return v;
}
static Tab *tag_tab(const char *k) {
    Tab *t = tab_new();
    Bin nk = bin_str("n");
    tab_bind(t, nk, vstr(k), NULL);
    return t;
}

Val ty_to_val(const Ty *t) {
    switch (t->k) {
        case T_NIL:
            return vstr("nil");
        case T_BIT:
            return vstr("bit");
        case T_I64:
            return vstr("i64");
        case T_F64:
            return vstr("f64");
        case T_U8:
            return vstr("u8");
        case T_NAME:
            return vstr_b(&t->name);
        case T_VEC: {
            Tab *tt = tag_tab("vec_t");
            Bin ek = bin_str("e");
            tab_bind(tt, ek, ty_to_val(&t->elem[0]), NULL);
            Val v;
            v.k = V_TAB;
            v.u.tab = tt;
            return v;
        }
        case T_UNION: {
            Tab *tt = tag_tab("union_t");
            Val *es = malloc(t->n * sizeof(Val));
            for (size_t i = 0; i < t->n; i++)
                es[i] = ty_to_val(&t->elem[i]);
            Bin ek = bin_str("e");
            tab_bind(tt, ek, vec_of(es, t->n), NULL);
            Val v;
            v.k = V_TAB;
            v.u.tab = tt;
            return v;
        }
        case T_TAB: {
            Tab *tt = tag_tab("rec_t");
            Val *ks = malloc((t->n ? t->n : 1) * sizeof(Val)),
                *ts = malloc((t->n ? t->n : 1) * sizeof(Val));
            for (size_t i = 0; i < t->n; i++) {
                ks[i] = vstr_b(&t->fields[i]);
                ts[i] = ty_to_val(&t->elem[i]);
            }
            Bin kk = bin_str("k"), tk = bin_str("t");
            tab_bind(tt, kk, vec_of(ks, t->n), NULL);
            tab_bind(tt, tk, vec_of(ts, t->n), NULL);
            Val v;
            v.k = V_TAB;
            v.u.tab = tt;
            return v;
        }
        case T_FUN: {
            Tab *tt = tag_tab("fun_t");
            Val *as = malloc((t->n ? t->n : 1) * sizeof(Val));
            for (size_t i = 0; i < t->n; i++)
                as[i] = ty_to_val(&t->elem[i]);
            Bin ak = bin_str("a"), rk = bin_str("r");
            tab_bind(tt, ak, vec_of(as, t->n), NULL);
            tab_bind(tt, rk, ty_to_val(t->ret), NULL);
            Val v;
            v.k = V_TAB;
            v.u.tab = tt;
            return v;
        }
    }
    return vnil();
}

static bool vec_tys(const Val *v, Ty **out, size_t *n) {
    if (v->k != V_VEC)
        return false;
    Col *c = v->u.vec;
    Ty *ts = malloc((c->len ? c->len : 1) * sizeof(Ty));
    for (size_t i = 0; i < c->len; i++) {
        Val e = col_elem(c, i);
        if (!val_to_ty(&e, &ts[i]))
            return false;
    }
    *out = ts;
    *n = c->len;
    return true;
}
bool val_to_ty(const Val *v, Ty *out) {
    memset(out, 0, sizeof(Ty));
    Bin sbuf;
    if (sb(v, &sbuf)) {
        const uint8_t *b = bin_bytes(&sbuf);
        size_t n = sbuf.len;
        if (n == 3 && !memcmp(b, "nil", 3))
            out->k = T_NIL;
        else if (n == 3 && !memcmp(b, "bit", 3))
            out->k = T_BIT;
        else if (n == 3 && !memcmp(b, "i64", 3))
            out->k = T_I64;
        else if (n == 3 && !memcmp(b, "f64", 3))
            out->k = T_F64;
        else if (n == 2 && !memcmp(b, "u8", 2))
            out->k = T_U8;
        else {
            out->k = T_NAME;
            out->name = bin_clone(sbuf);
        }
        return true;
    }
    if (v->k == V_TAB) {
        Val *nn = tab_get(v->u.tab, (const uint8_t *)"n", 1);
        Bin nb;
        if (!nn || !sb(nn, &nb))
            return false;
        const uint8_t *b = bin_bytes(&nb);
        size_t n = nb.len;
        if (n == 5 && !memcmp(b, "vec_t", 5)) {
            Val *e = tab_get(v->u.tab, (const uint8_t *)"e", 1);
            if (!e)
                return false;
            out->k = T_VEC;
            out->elem = malloc(sizeof(Ty));
            out->n = 1;
            return val_to_ty(e, &out->elem[0]);
        }
        if (n == 7 && !memcmp(b, "union_t", 7)) {
            Val *e = tab_get(v->u.tab, (const uint8_t *)"e", 1);
            if (!e)
                return false;
            out->k = T_UNION;
            return vec_tys(e, &out->elem, &out->n);
        }
        if (n == 5 && !memcmp(b, "fun_t", 5)) {
            Val *a = tab_get(v->u.tab, (const uint8_t *)"a", 1),
                *rr = tab_get(v->u.tab, (const uint8_t *)"r", 1);
            if (!a || !rr)
                return false;
            out->k = T_FUN;
            if (!vec_tys(a, &out->elem, &out->n))
                return false;
            out->ret = malloc(sizeof(Ty));
            return val_to_ty(rr, out->ret);
        }
        if (n == 5 && !memcmp(b, "rec_t", 5)) {
            Val *k = tab_get(v->u.tab, (const uint8_t *)"k", 1),
                *tt = tab_get(v->u.tab, (const uint8_t *)"t", 1);
            if (!k || !tt || k->k != V_VEC)
                return false;
            out->k = T_TAB;
            Col *kc = k->u.vec;
            out->fields = malloc((kc->len ? kc->len : 1) * sizeof(Bin));
            for (size_t i = 0; i < kc->len; i++) {
                Val ke = col_elem(kc, i);
                if (!sb(&ke, &out->fields[i]))
                    return false;
            }
            size_t tn;
            if (!vec_tys(tt, &out->elem, &tn))
                return false;
            if (tn != kc->len)
                return false;
            out->n = tn;
            return true;
        }
        return false;
    }
    return false;
}

// ---------- AST <-> tab ----------
static void bind_s(Tab *t, const char *k, Val v) {
    Bin kb = bin_str(k);
    tab_bind(t, kb, v, NULL);
}
static Val nodes_vec(const Node *ns, size_t n) {
    Val *vs = malloc((n ? n : 1) * sizeof(Val));
    for (size_t i = 0; i < n; i++)
        vs[i] = ast_to_val(&ns[i]);
    return vec_of(vs, n);
}

Val ast_to_val(const Node *n) {
    Tab *t;
    switch (n->k) {
        case A_LIT:
            t = tag_tab("lit");
            bind_s(t, "v", val_clone(n->lit));
            break;
        case A_VAR:
            t = tag_tab("var");
            {
                Val v;
                v = vstr_b(&(n->name));
                bind_s(t, "x", v);
            }
            break;
        case A_PROJ:
            t = tag_tab("proj");
            bind_s(t, "e", ast_to_val(n->a));
            {
                Val v;
                v = vstr_b(&(n->name));
                bind_s(t, "x", v);
            }
            break;
        case A_IDX:
            t = tag_tab("idx");
            bind_s(t, "e", ast_to_val(n->a));
            bind_s(t, "i", ast_to_val(n->b));
            break;
        case A_APP:
            t = tag_tab("app");
            bind_s(t, "f", ast_to_val(n->a));
            bind_s(t, "a", nodes_vec(n->kids, n->nkids));
            break;
        case A_VEC:
            t = tag_tab("vec");
            bind_s(t, "e", nodes_vec(n->kids, n->nkids));
            break;
        case A_TAB: {
            t = tag_tab("tab");
            Val *ks = malloc((n->nkeys ? n->nkeys : 1) * sizeof(Val));
            for (size_t i = 0; i < n->nkeys; i++) {
                ks[i] = vstr_b(&n->keys[i]);
            }
            bind_s(t, "k", vec_of(ks, n->nkeys));
            bind_s(t, "e", nodes_vec(n->kids, n->nkids));
        } break;
        case A_FUN: {
            t = tag_tab("fun");
            Val *ps = malloc((n->nparams ? n->nparams : 1) * sizeof(Val));
            for (size_t i = 0; i < n->nparams; i++) {
                Tab *pt = tab_new();
                Val xv;
                xv = vstr_b(&(n->params[i]));
                Bin xk = bin_str("x");
                tab_bind(pt, xk, xv, NULL);
                Bin tk = bin_str("t");
                tab_bind(pt, tk, ty_to_val(&n->ptypes[i]), NULL);
                ps[i].k = V_TAB;
                ps[i].u.tab = pt;
            }
            bind_s(t, "p", vec_of(ps, n->nparams));
            bind_s(t, "t", ty_to_val(&n->ty));
            bind_s(t, "e", ast_to_val(n->a));
        } break;
        case A_IF:
            t = tag_tab("if");
            bind_s(t, "c", ast_to_val(n->a));
            bind_s(t, "t", ast_to_val(n->b));
            bind_s(t, "e", ast_to_val(n->c));
            break;
        case A_TRY:
            t = tag_tab("try");
            bind_s(t, "e1", ast_to_val(n->a));
            bind_s(t, "e2", ast_to_val(n->b));
            break;
        case A_ERR:
            t = tag_tab("err");
            bind_s(t, "e", ast_to_val(n->a));
            break;
        case A_IS:
            t = tag_tab("is");
            bind_s(t, "e", ast_to_val(n->a));
            bind_s(t, "t", ty_to_val(&n->ty));
            break;
        case A_AS:
            t = tag_tab("as");
            bind_s(t, "e", ast_to_val(n->a));
            bind_s(t, "t", ty_to_val(&n->ty));
            break;
        case A_SEQ:
            t = tag_tab("seq");
            bind_s(t, "d", nodes_vec(n->kids, n->nkids));
            break;
        case A_LET:
            t = tag_tab("let");
            {
                Val v;
                v = vstr_b(&(n->name));
                bind_s(t, "x", v);
            }
            if (n->has_ty)
                bind_s(t, "t", ty_to_val(&n->ty));
            bind_s(t, "e", ast_to_val(n->a));
            if (n->has_doc) {
                Val v;
                v = vstr_b(&(n->doc));
                bind_s(t, "doc", v);
            }
            if (n->is_pub)
                bind_s(t, "pub", vbit(true));
            break;
        case A_TYPE:
            t = tag_tab("type");
            {
                Val v;
                v = vstr_b(&(n->name));
                bind_s(t, "x", v);
            }
            bind_s(t, "t", ty_to_val(&n->ty));
            bind_s(t, "p", ast_to_val(n->a));
            if (n->has_doc) {
                Val v;
                v = vstr_b(&(n->doc));
                bind_s(t, "doc", v);
            }
            if (n->is_pub)
                bind_s(t, "pub", vbit(true));
            break;
        case A_USE:
            t = tag_tab("use");
            {
                Val v;
                v = vstr_b(&(n->name));
                bind_s(t, "x", v);
            }
            if (n->has_url) {
                Val v;
                v = vstr_b(&(n->url));
                bind_s(t, "url", v);
            }
            if (n->has_doc) {
                Val v;
                v = vstr_b(&(n->doc));
                bind_s(t, "doc", v);
            }
            break;
        default:
            t = tag_tab("lit");
            bind_s(t, "v", vnil());
            break;
    }
    Val v;
    v.k = V_TAB;
    v.u.tab = t;
    return v;
}

static bool vget(Tab *t, const char *k, Val **o) {
    *o = tab_get(t, (const uint8_t *)k, strlen(k));
    return *o != NULL;
}
static bool vnode(Tab *t, const char *k, Node **o, SnelErr *e) {
    Val *v;
    if (!vget(t, k, &v))
        return false;
    return val_to_ast(v, o, e);
}

bool val_to_ast(const Val *v, Node **out, SnelErr *err) {
    if (v->k != V_TAB) {
        snprintf(err->msg, sizeof err->msg, "code node must be a tab");
        return false;
    }
    Tab *t = v->u.tab;
    Val *nv = tab_get(t, (const uint8_t *)"n", 1);
    Bin nkb;
    if (!nv || !sb(nv, &nkb)) {
        snprintf(err->msg, sizeof err->msg, "node needs n");
        return false;
    }
    const uint8_t *k = bin_bytes(&nkb);
    size_t kn = nkb.len;
#define KIS(s) (kn == strlen(s) && !memcmp(k, s, kn))
    Node *n;
    Val *tmp;
    if (KIS("lit")) {
        n = node_new(A_LIT, 0);
        if (!vget(t, "v", &tmp))
            return false;
        n->lit = val_clone(*tmp);
    } else if (KIS("var")) {
        n = node_new(A_VAR, 0);
        if (!vget(t, "x", &tmp) || !sb(tmp, &n->name))
            return false;
    } else if (KIS("proj")) {
        n = node_new(A_PROJ, 0);
        if (!vnode(t, "e", &n->a, err))
            return false;
        if (!vget(t, "x", &tmp) || !sb(tmp, &n->name))
            return false;
    } else if (KIS("idx")) {
        n = node_new(A_IDX, 0);
        if (!vnode(t, "e", &n->a, err) || !vnode(t, "i", &n->b, err))
            return false;
    } else if (KIS("app")) {
        n = node_new(A_APP, 0);
        if (!vnode(t, "f", &n->a, err))
            return false;
        if (!vget(t, "a", &tmp) || tmp->k != V_VEC)
            return false;
        Col *c = tmp->u.vec;
        n->nkids = c->len;
        n->kids = malloc((c->len ? c->len : 1) * sizeof(Node));
        for (size_t i = 0; i < c->len; i++) {
            Val e = col_elem(c, i);
            Node *kn2;
            if (!val_to_ast(&e, &kn2, err))
                return false;
            n->kids[i] = *kn2;
        }
    } else if (KIS("vec")) {
        n = node_new(A_VEC, 0);
        if (!vget(t, "e", &tmp) || tmp->k != V_VEC)
            return false;
        Col *c = tmp->u.vec;
        n->nkids = c->len;
        n->kids = malloc((c->len ? c->len : 1) * sizeof(Node));
        for (size_t i = 0; i < c->len; i++) {
            Val e = col_elem(c, i);
            Node *kn2;
            if (!val_to_ast(&e, &kn2, err))
                return false;
            n->kids[i] = *kn2;
        }
    } else if (KIS("tab")) {
        n = node_new(A_TAB, 0);
        Val *kk;
        if (!vget(t, "k", &kk) || !vget(t, "e", &tmp))
            return false;
        Col *kc = kk->u.vec, *ec = tmp->u.vec;
        if (kc->len != ec->len)
            return false;
        n->nkeys = n->nkids = kc->len;
        n->keys = malloc((kc->len ? kc->len : 1) * sizeof(Bin));
        n->kids = malloc((kc->len ? kc->len : 1) * sizeof(Node));
        for (size_t i = 0; i < kc->len; i++) {
            Val ke = col_elem(kc, i);
            if (!sb(&ke, &n->keys[i]))
                return false;
            Val ee = col_elem(ec, i);
            Node *kn2;
            if (!val_to_ast(&ee, &kn2, err))
                return false;
            n->kids[i] = *kn2;
        }
    } else if (KIS("fun")) {
        n = node_new(A_FUN, 0);
        Val *pp;
        if (!vget(t, "p", &pp) || pp->k != V_VEC)
            return false;
        Col *pc = pp->u.vec;
        n->nparams = pc->len;
        n->params = malloc((pc->len ? pc->len : 1) * sizeof(Bin));
        n->ptypes = malloc((pc->len ? pc->len : 1) * sizeof(Ty));
        for (size_t i = 0; i < pc->len; i++) {
            Val pe = col_elem(pc, i);
            if (pe.k != V_TAB)
                return false;
            Val *xv = tab_get(pe.u.tab, (const uint8_t *)"x", 1),
                *tv = tab_get(pe.u.tab, (const uint8_t *)"t", 1);
            if (!xv || !sb(xv, &n->params[i]) || !tv)
                return false;
            if (!val_to_ty(tv, &n->ptypes[i]))
                return false;
        }
        Val *rt;
        if (!vget(t, "t", &rt) || !val_to_ty(rt, &n->ty))
            return false;
        n->has_ty = true;
        if (!vnode(t, "e", &n->a, err))
            return false;
    } else if (KIS("if")) {
        n = node_new(A_IF, 0);
        if (!vnode(t, "c", &n->a, err) || !vnode(t, "t", &n->b, err) || !vnode(t, "e", &n->c, err))
            return false;
    } else if (KIS("try")) {
        n = node_new(A_TRY, 0);
        if (!vnode(t, "e1", &n->a, err) || !vnode(t, "e2", &n->b, err))
            return false;
    } else if (KIS("err")) {
        n = node_new(A_ERR, 0);
        if (!vnode(t, "e", &n->a, err))
            return false;
    } else if (KIS("is")) {
        n = node_new(A_IS, 0);
        if (!vnode(t, "e", &n->a, err))
            return false;
        if (!vget(t, "t", &tmp) || !val_to_ty(tmp, &n->ty))
            return false;
        n->has_ty = true;
    } else if (KIS("as")) {
        n = node_new(A_AS, 0);
        if (!vnode(t, "e", &n->a, err))
            return false;
        if (!vget(t, "t", &tmp) || !val_to_ty(tmp, &n->ty))
            return false;
        n->has_ty = true;
    } else if (KIS("seq")) {
        n = node_new(A_SEQ, 0);
        if (!vget(t, "d", &tmp) || tmp->k != V_VEC)
            return false;
        Col *c = tmp->u.vec;
        n->nkids = c->len;
        n->kids = malloc((c->len ? c->len : 1) * sizeof(Node));
        for (size_t i = 0; i < c->len; i++) {
            Val e = col_elem(c, i);
            Node *kn2;
            if (!val_to_ast(&e, &kn2, err))
                return false;
            n->kids[i] = *kn2;
        }
    } else if (KIS("let")) {
        n = node_new(A_LET, 0);
        if (!vget(t, "x", &tmp) || !sb(tmp, &n->name))
            return false;
        Val *ty;
        if (vget(t, "t", &ty)) {
            if (!val_to_ty(ty, &n->ty))
                return false;
            n->has_ty = true;
        }
        if (!vnode(t, "e", &n->a, err))
            return false;
        Val *dc;
        if (vget(t, "doc", &dc) && sb(dc, &n->doc)) {
            n->has_doc = true;
        }
        Val *pb;
        if (vget(t, "pub", &pb) && pb->k == V_BIT && pb->u.i)
            n->is_pub = true;
    } else if (KIS("type")) {
        n = node_new(A_TYPE, 0);
        if (!vget(t, "x", &tmp) || !sb(tmp, &n->name))
            return false;
        if (!vget(t, "t", &tmp) || !val_to_ty(tmp, &n->ty))
            return false;
        n->has_ty = true;
        if (!vnode(t, "p", &n->a, err))
            return false;
        Val *dc;
        if (vget(t, "doc", &dc) && sb(dc, &n->doc)) {
            n->has_doc = true;
        }
        Val *pb;
        if (vget(t, "pub", &pb) && pb->k == V_BIT && pb->u.i)
            n->is_pub = true;
    } else if (KIS("use")) {
        n = node_new(A_USE, 0);
        if (!vget(t, "x", &tmp) || !sb(tmp, &n->name))
            return false;
        Val *ur;
        if (vget(t, "url", &ur) && sb(ur, &n->url))
            n->has_url = true;
        Val *dc;
        if (vget(t, "doc", &dc) && sb(dc, &n->doc)) {
            n->has_doc = true;
        }
    } else {
        snprintf(err->msg, sizeof err->msg, "unknown node kind");
        return false;
    }
    *out = n;
    return true;
}
