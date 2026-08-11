// Values: refcounted columns/tabs/closures, SSO byte buffers, packed bitmaps.
#include "snel.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p)
        abort();
    return p;
}
static void *xrealloc(void *p, size_t n) {
    p = realloc(p, n ? n : 1);
    if (!p)
        abort();
    return p;
}

uint64_t fnv1a(const uint8_t *b, size_t n) {
    uint64_t h = 0xcbf29ce484222325ULL;
    for (size_t i = 0; i < n; i++) {
        h ^= b[i];
        h *= 0x100000001b3ULL;
    }
    return h;
}

// ---------- Bin (SSO; heap payload carries a refcount header) ----------

typedef struct {
    int32_t rc;
    uint32_t len;
} BinHdr;

Bin bin_new(const uint8_t *b, size_t n) {
    Bin r;
    r.len = (uint32_t)n;
    if (n <= 14) {
        r.heap = false;
        memset(r.u.sso, 0, 15);
        if (n)
            memcpy(r.u.sso, b, n);
    } else {
        r.heap = true;
        BinHdr *h = xmalloc(sizeof(BinHdr) + n);
        h->rc = 1;
        h->len = (uint32_t)n;
        memcpy((uint8_t *)h + sizeof(BinHdr), b, n);
        r.u.ptr = (uint8_t *)h + sizeof(BinHdr);
    }
    return r;
}
Bin bin_str(const char *s) {
    return bin_new((const uint8_t *)s, strlen(s));
}

const uint8_t *bin_bytes(const Bin *b) {
    return b->heap ? b->u.ptr : b->u.sso;
}

Bin bin_clone(Bin b) {
    if (b.heap) {
        BinHdr *h = (BinHdr *)(b.u.ptr - sizeof(BinHdr));
        h->rc++;
    }
    return b;
}
void bin_drop(Bin *b) {
    if (b->heap) {
        BinHdr *h = (BinHdr *)(b->u.ptr - sizeof(BinHdr));
        if (--h->rc == 0)
            free(h);
        b->heap = false;
        b->len = 0;
    }
}
bool bin_eq(const Bin *a, const Bin *b) {
    return a->len == b->len && memcmp(bin_bytes(a), bin_bytes(b), a->len) == 0;
}
bool bin_is_sym(const Bin *b) {
    if (b->len == 0)
        return false;
    const uint8_t *p = bin_bytes(b);
    for (size_t i = 0; i < b->len; i++) {
        uint8_t c = p[i];
        if (!((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') ||
              c == '_'))
            return false;
    }
    return true;
}
// A valid identifier: sym-shaped and not starting with a digit.
bool bin_is_ident(const Bin *b) {
    return bin_is_sym(b) && !(bin_bytes(b)[0] >= '0' && bin_bytes(b)[0] <= '9');
}
bool bin_is_utf8(const uint8_t *b, size_t n) {
    size_t i = 0;
    while (i < n) {
        uint8_t c = b[i];
        size_t need;
        if (c < 0x80)
            need = 0;
        else if ((c & 0xe0) == 0xc0) {
            need = 1;
            if (c < 0xc2)
                return false;
        } else if ((c & 0xf0) == 0xe0)
            need = 2;
        else if ((c & 0xf8) == 0xf0) {
            need = 3;
            if (c > 0xf4)
                return false;
        } else
            return false;
        if (i + need >= n)
            return false;
        for (size_t j = 1; j <= need; j++)
            if ((b[i + j] & 0xc0) != 0x80)
                return false;
        i += need + 1;
    }
    return true;
}

// ---------- Bits ----------

Bits bits_new(size_t len, bool fill) {
    Bits b;
    b.len = len;
    b.wcap = (len + 63) / 64;
    b.w = xmalloc(b.wcap * sizeof(uint64_t) + 1);
    memset(b.w, fill ? 0xff : 0, b.wcap * sizeof(uint64_t));
    if (fill && len % 64)
        b.w[b.wcap - 1] &= ((uint64_t)1 << (len % 64)) - 1;
    return b;
}
bool bits_get(const Bits *b, size_t i) {
    return (b->w[i / 64] >> (i % 64)) & 1;
}
void bits_set(Bits *b, size_t i, bool v) {
    uint64_t m = (uint64_t)1 << (i % 64);
    if (v)
        b->w[i / 64] |= m;
    else
        b->w[i / 64] &= ~m;
}
void bits_push(Bits *b, bool v) {
    if (b->len % 64 == 0) {
        b->wcap = b->len / 64 + 1;
        b->w = xrealloc(b->w, b->wcap * sizeof(uint64_t));
        b->w[b->wcap - 1] = 0;
    }
    b->len++;
    bits_set(b, b->len - 1, v);
}
Bits bits_clone(const Bits *b) {
    Bits r;
    r.len = b->len;
    r.wcap = b->wcap ? b->wcap : 1;
    r.w = xmalloc(r.wcap * sizeof(uint64_t));
    memcpy(r.w, b->w, ((b->len + 63) / 64) * sizeof(uint64_t));
    return r;
}
void bits_free(Bits *b) {
    free(b->w);
    b->w = NULL;
    b->len = 0;
}

// ---------- Payload ----------

static void payload_free(Payload *p, size_t len) {
    switch (p->k) {
        case P_BITS:
            bits_free(&p->u.bits);
            break;
        case P_I64S:
            free(p->u.i64);
            break;
        case P_F64S:
            free(p->u.f64);
            break;
        case P_U8S:
            bin_drop(&p->u.u8s);
            break;
        case P_VECS:
            for (size_t i = 0; i < len; i++)
                col_release(p->u.vecs[i]);
            free(p->u.vecs);
            break;
        case P_TABS:
            for (size_t i = 0; i < len; i++)
                tab_release(p->u.tab[i]);
            free(p->u.tab);
            break;
    }
}

// ---------- Col ----------

Col *col_simple(Payload p) {
    Col *c = xmalloc(sizeof(Col));
    c->rc = 1;
    c->has_present = false;
    c->has_sel = false;
    c->sel = NULL;
    c->ncases = 1;
    c->cases[0] = p;
    switch (p.k) {
        case P_BITS:
            c->len = p.u.bits.len;
            break;
        case P_U8S:
            c->len = p.u.u8s.len;
            break;
        default:
            c->len = 0;
            break; // caller sets len via col_from_vals path
    }
    return c;
}

// A [u8] string column from raw bytes.
Col *col_u8s(const uint8_t *b, size_t n) {
    Payload p;
    p.k = P_U8S;
    p.u.u8s = bin_new(b, n);
    return col_simple(p);
}

Col *col_retain(Col *c) {
    if (c)
        c->rc++;
    return c;
}
void col_release(Col *c) {
    if (!c || --c->rc)
        return;
    if (c->has_present)
        bits_free(&c->present);
    free(c->sel);
    for (int i = 0; i < c->ncases; i++)
        payload_free(&c->cases[i], c->len);
    free(c);
}

// ---------- Tab ----------

Tab *tab_new(void) {
    Tab *t = xmalloc(sizeof(Tab));
    t->rc = 1;
    t->len = 0;
    t->cap = 0;
    t->keys = NULL;
    t->vals = NULL;
    t->docs = NULL;
    t->has_doc = NULL;
    return t;
}
Tab *tab_retain(Tab *t) {
    if (t)
        t->rc++;
    return t;
}
void tab_release(Tab *t) {
    if (!t || --t->rc)
        return;
    for (size_t i = 0; i < t->len; i++) {
        bin_drop(&t->keys[i]);
        val_drop(t->vals[i]);
        if (t->has_doc[i])
            bin_drop(&t->docs[i]);
    }
    free(t->keys);
    free(t->vals);
    free(t->docs);
    free(t->has_doc);
    free(t);
}
Tab *tab_clone(const Tab *t) {
    Tab *r = tab_new();
    r->cap = r->len = t->len;
    r->keys = xmalloc(t->len * sizeof(Bin));
    r->vals = xmalloc(t->len * sizeof(Val));
    r->docs = xmalloc(t->len * sizeof(Bin));
    r->has_doc = xmalloc(t->len * sizeof(bool));
    for (size_t i = 0; i < t->len; i++) {
        r->keys[i] = bin_clone(t->keys[i]);
        r->vals[i] = val_clone(t->vals[i]);
        r->has_doc[i] = t->has_doc[i];
        if (t->has_doc[i])
            r->docs[i] = bin_clone(t->docs[i]);
    }
    return r;
}
Val *tab_get(Tab *t, const uint8_t *k, size_t n) {
    for (size_t i = t->len; i-- > 0;)
        if (t->keys[i].len == n && memcmp(bin_bytes(&t->keys[i]), k, n) == 0)
            return &t->vals[i];
    return NULL;
}
void tab_bind(Tab *t, Bin key, Val v, const Bin *doc) {
    int i = -1;
    for (size_t j = 0; j < t->len; j++)
        if (bin_eq(&t->keys[j], &key)) {
            i = (int)j;
            break;
        }
    if (i >= 0) {
        val_drop(t->vals[i]);
        t->vals[i] = v;
        if (t->has_doc[i])
            bin_drop(&t->docs[i]);
        t->has_doc[i] = doc != NULL;
        if (doc)
            t->docs[i] = bin_clone(*doc);
        bin_drop(&key);
        return;
    }
    if (t->len == t->cap) {
        t->cap = t->cap ? t->cap * 2 : 4;
        t->keys = xrealloc(t->keys, t->cap * sizeof(Bin));
        t->vals = xrealloc(t->vals, t->cap * sizeof(Val));
        t->docs = xrealloc(t->docs, t->cap * sizeof(Bin));
        t->has_doc = xrealloc(t->has_doc, t->cap * sizeof(bool));
    }
    t->keys[t->len] = key;
    t->vals[t->len] = v;
    t->has_doc[t->len] = doc != NULL;
    if (doc)
        t->docs[t->len] = bin_clone(*doc);
    t->len++;
}

// ---------- Val ----------

// The refcounted slow path; scalars are handled inline in snel.h (val_clone/
// val_drop early-out for the common no-refcount kinds).
Val val_retain_heap(Val v) {
    switch (v.k) {
        case V_PRIM:
            v.u.bin = bin_clone(v.u.bin);
            break;
        case V_VEC:
            col_retain(v.u.vec);
            break;
        case V_TAB:
            tab_retain(v.u.tab);
            break;
        case V_FUN:
            v.u.fun->rc++;
            break;
        default:
            break;
    }
    return v;
}
void clo_release(Clo *c);
void val_release_heap(Val v) {
    switch (v.k) {
        case V_PRIM:
            bin_drop(&v.u.bin);
            break;
        case V_VEC:
            col_release(v.u.vec);
            break;
        case V_TAB:
            tab_release(v.u.tab);
            break;
        case V_FUN:
            clo_release(v.u.fun);
            break;
        default:
            break;
    }
}

// ---------- error line numbers ----------
// Error spans are byte offsets. The formatted message wants a line number, and
// the modules that build those messages (check.c, eval.c) do not receive the
// unit text, so the CLI hands it over here. Mirrors err_line in src/lib.rs.
static const char *g_err_src = NULL;
const char *err_src(void) {
    return g_err_src;
}
void err_set_src(const char *src) {
    g_err_src = src;
}
unsigned err_line(uint32_t at) {
    unsigned line = 1;
    if (!g_err_src)
        return line;
    for (uint32_t i = 0; i < at && g_err_src[i]; i++)
        if (g_err_src[i] == '\n')
            line++;
    return line;
}
