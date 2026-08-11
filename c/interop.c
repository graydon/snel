// Interop: JSON (nesting) and CSV (flat tables only). Mirrors src/interop.rs;
// both must produce byte-identical output. See that file for the mapping.
#include "snel.h"
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

bool is_u8_col(const Col *c);
uint8_t *col_bytes(const Col *c, size_t *len);

// ---------- a growable byte string ----------
typedef struct {
    char *p;
    size_t n, cap;
} S;

static void sput_n(S *s, const char *b, size_t n) {
    if (s->n + n + 1 > s->cap) {
        s->cap = (s->n + n + 1) * 2;
        s->p = realloc(s->p, s->cap);
    }
    memcpy(s->p + s->n, b, n);
    s->n += n;
    s->p[s->n] = 0;
}
static void sput(S *s, const char *b) {
    sput_n(s, b, strlen(b));
}
static void sputc_(S *s, char c) {
    sput_n(s, &c, 1);
}
static Val s_val(S *s) {
    Val v;
    v.k = V_VEC;
    v.u.vec = col_u8s((const uint8_t *)(s->p ? s->p : ""), s->n);
    free(s->p);
    return v;
}
static void seterr_(SnelErr *e, const char *m) {
    snprintf(e->msg, sizeof e->msg, "%s", m);
}

// ---------- JSON writing ----------

static void write_json_str(S *s, const uint8_t *b, size_t n) {
    sputc_(s, '"');
    for (size_t i = 0; i < n; i++) {
        uint8_t c = b[i];
        switch (c) {
            case '"':
                sput(s, "\\\"");
                break;
            case '\\':
                sput(s, "\\\\");
                break;
            case '\n':
                sput(s, "\\n");
                break;
            case '\t':
                sput(s, "\\t");
                break;
            case '\r':
                sput(s, "\\r");
                break;
            default:
                if (c < 0x20) {
                    char buf[8];
                    snprintf(buf, sizeof buf, "\\u%04x", c);
                    sput(s, buf);
                } else
                    sputc_(s, (char)c); // utf-8 continuation bytes pass through
        }
    }
    sputc_(s, '"');
}

static bool write_json(S *s, const Val *v, SnelErr *e) {
    char buf[64];
    switch (v->k) {
        case V_NIL:
            sput(s, "null");
            return true;
        case V_BIT:
            sput(s, v->u.i ? "true" : "false");
            return true;
        case V_I64:
            snprintf(buf, sizeof buf, "%lld", (long long)v->u.i);
            sput(s, buf);
            return true;
        case V_U8:
            snprintf(buf, sizeof buf, "%llu", (unsigned long long)(v->u.i & 0xff));
            sput(s, buf);
            return true;
        case V_F64: {
            double x = v->u.f;
            if (!(x == x) || x > 1.7976931348623157e308 || x < -1.7976931348623157e308) {
                seterr_(e, "tojson: inf/nan have no JSON form");
                return false;
            }
            char *f = fmt_f64(x);
            sput(s, f);
            free(f);
            return true;
        }
        case V_VEC: {
            Col *c = v->u.vec;
            if (is_u8_col(c)) {
                size_t n;
                uint8_t *b = col_bytes(c, &n);
                write_json_str(s, b, n);
                free(b);
                return true;
            }
            sputc_(s, '[');
            for (size_t i = 0; i < c->len; i++) {
                if (i)
                    sputc_(s, ',');
                Val ev = col_elem(c, i);
                bool ok = write_json(s, &ev, e);
                val_drop(ev);
                if (!ok)
                    return false;
            }
            sputc_(s, ']');
            return true;
        }
        case V_TAB: {
            Tab *t = v->u.tab;
            sputc_(s, '{');
            for (size_t i = 0; i < t->len; i++) {
                if (i)
                    sputc_(s, ',');
                write_json_str(s, bin_bytes(&t->keys[i]), t->keys[i].len);
                sputc_(s, ':');
                if (!write_json(s, &t->vals[i], e))
                    return false;
            }
            sputc_(s, '}');
            return true;
        }
        default:
            seterr_(e, "tojson: a function has no JSON form");
            return false;
    }
}

bool op_tojson(const Val *v, Val *out, SnelErr *e) {
    S s = {0};
    if (!write_json(&s, v, e)) {
        free(s.p);
        return false;
    }
    *out = s_val(&s);
    return true;
}

// ---------- JSON reading ----------

typedef struct {
    const uint8_t *b;
    size_t n, i;
} JP;

static void jws(JP *p) {
    while (p->i < p->n &&
           (p->b[p->i] == ' ' || p->b[p->i] == '\t' || p->b[p->i] == '\n' || p->b[p->i] == '\r'))
        p->i++;
}
static bool jlit(JP *p, const char *s) {
    size_t l = strlen(s);
    if (p->i + l <= p->n && memcmp(p->b + p->i, s, l) == 0) {
        p->i += l;
        return true;
    }
    return false;
}

// a JSON string body into a fresh malloc'd buffer (caller frees)
static bool jstring(JP *p, uint8_t **out, size_t *outn, SnelErr *e) {
    p->i++; // opening quote
    size_t cap = 16, n = 0;
    uint8_t *buf = malloc(cap);
    for (;;) {
        if (p->i >= p->n) {
            free(buf);
            seterr_(e, "fromjson: unterminated string");
            return false;
        }
        uint8_t c = p->b[p->i++];
        if (n + 4 >= cap) {
            cap *= 2;
            buf = realloc(buf, cap);
        }
        if (c == '"') {
            *out = buf;
            *outn = n;
            return true;
        }
        if (c != '\\') {
            buf[n++] = c;
            continue;
        }
        if (p->i >= p->n) {
            free(buf);
            seterr_(e, "fromjson: bad escape");
            return false;
        }
        uint8_t esc = p->b[p->i++];
        switch (esc) {
            case '"':
                buf[n++] = '"';
                break;
            case '\\':
                buf[n++] = '\\';
                break;
            case '/':
                buf[n++] = '/';
                break;
            case 'n':
                buf[n++] = '\n';
                break;
            case 't':
                buf[n++] = '\t';
                break;
            case 'r':
                buf[n++] = '\r';
                break;
            case 'b':
                buf[n++] = 0x08;
                break;
            case 'f':
                buf[n++] = 0x0c;
                break;
            case 'u': {
                if (p->i + 4 > p->n) {
                    free(buf);
                    seterr_(e, "fromjson: bad \\u escape");
                    return false;
                }
                char h[5] = {0};
                memcpy(h, p->b + p->i, 4);
                for (int k = 0; k < 4; k++)
                    if (!isxdigit((unsigned char)h[k])) {
                        free(buf);
                        seterr_(e, "fromjson: bad \\u escape");
                        return false;
                    }
                unsigned long cp = strtoul(h, NULL, 16);
                p->i += 4;
                if (cp >= 0xd800 && cp <= 0xdfff)
                    cp = 0xfffd; // lone surrogate
                // encode as UTF-8 (mirrors Rust's char::encode_utf8)
                if (cp < 0x80)
                    buf[n++] = (uint8_t)cp;
                else if (cp < 0x800) {
                    buf[n++] = (uint8_t)(0xc0 | (cp >> 6));
                    buf[n++] = (uint8_t)(0x80 | (cp & 0x3f));
                } else {
                    buf[n++] = (uint8_t)(0xe0 | (cp >> 12));
                    buf[n++] = (uint8_t)(0x80 | ((cp >> 6) & 0x3f));
                    buf[n++] = (uint8_t)(0x80 | (cp & 0x3f));
                }
                break;
            }
            default:
                free(buf);
                seterr_(e, "fromjson: bad escape");
                return false;
        }
    }
}

static bool jvalue(JP *p, Val *out, SnelErr *e);

static bool jnumber(JP *p, Val *out, SnelErr *e) {
    size_t start = p->i;
    if (p->i < p->n && p->b[p->i] == '-')
        p->i++;
    bool is_float = false;
    while (p->i < p->n) {
        uint8_t c = p->b[p->i];
        if (c >= '0' && c <= '9')
            p->i++;
        else if (c == '.' || c == 'e' || c == 'E' || c == '+' || c == '-') {
            is_float = true;
            p->i++;
        } else
            break;
    }
    size_t len = p->i - start;
    if (len == 0 || (len == 1 && p->b[start] == '-')) {
        seterr_(e, "fromjson: expected a value");
        return false;
    }
    char tmp[64];
    if (len >= sizeof tmp)
        len = sizeof tmp - 1;
    memcpy(tmp, p->b + start, len);
    tmp[len] = 0;
    if (!is_float) {
        char *end;
        long long ll = strtoll(tmp, &end, 10);
        if (*end == 0) {
            *out = vi64(ll);
            return true;
        }
    }
    double d;
    if (!parse_f64(tmp, &d)) {
        seterr_(e, "fromjson: bad number");
        return false;
    }
    *out = vf64(d);
    return true;
}

static bool jvalue(JP *p, Val *out, SnelErr *e) {
    jws(p);
    if (p->i >= p->n) {
        seterr_(e, "fromjson: unexpected end of input");
        return false;
    }
    uint8_t c = p->b[p->i];
    if (c == 'n') {
        if (!jlit(p, "null")) {
            seterr_(e, "fromjson: expected null");
            return false;
        }
        *out = vnil();
        return true;
    }
    if (c == 't') {
        if (!jlit(p, "true")) {
            seterr_(e, "fromjson: expected true");
            return false;
        }
        *out = vbit(true);
        return true;
    }
    if (c == 'f') {
        if (!jlit(p, "false")) {
            seterr_(e, "fromjson: expected false");
            return false;
        }
        *out = vbit(false);
        return true;
    }
    if (c == '"') {
        uint8_t *b;
        size_t bn;
        if (!jstring(p, &b, &bn, e))
            return false;
        Val v;
        v.k = V_VEC;
        v.u.vec = col_u8s(b, bn);
        free(b);
        *out = v;
        return true;
    }
    if (c == '[') {
        p->i++;
        size_t cap = 8, n = 0;
        Val *items = malloc(cap * sizeof(Val));
        jws(p);
        if (p->i < p->n && p->b[p->i] == ']')
            p->i++;
        else
            for (;;) {
                if (n == cap) {
                    cap *= 2;
                    items = realloc(items, cap * sizeof(Val));
                }
                if (!jvalue(p, &items[n], e)) {
                    for (size_t k = 0; k < n; k++)
                        val_drop(items[k]);
                    free(items);
                    return false;
                }
                n++;
                jws(p);
                if (p->i < p->n && p->b[p->i] == ',') {
                    p->i++;
                    continue;
                }
                if (p->i < p->n && p->b[p->i] == ']') {
                    p->i++;
                    break;
                }
                for (size_t k = 0; k < n; k++)
                    val_drop(items[k]);
                free(items);
                seterr_(e, "fromjson: expected , or ] in array");
                return false;
            }
        Col *c2;
        bool ok = col_from_vals(items, n, &c2, e); // consumes items
        free(items);
        if (!ok)
            return false;
        Val v;
        v.k = V_VEC;
        v.u.vec = c2;
        *out = v;
        return true;
    }
    if (c == '{') {
        p->i++;
        Tab *t = tab_new();
        jws(p);
        if (p->i < p->n && p->b[p->i] == '}')
            p->i++;
        else
            for (;;) {
                jws(p);
                if (p->i >= p->n || p->b[p->i] != '"') {
                    tab_release(t);
                    seterr_(e, "fromjson: expected a string key");
                    return false;
                }
                uint8_t *kb;
                size_t kn;
                if (!jstring(p, &kb, &kn, e)) {
                    tab_release(t);
                    return false;
                }
                jws(p);
                if (p->i >= p->n || p->b[p->i] != ':') {
                    free(kb);
                    tab_release(t);
                    seterr_(e, "fromjson: expected : after key");
                    return false;
                }
                p->i++;
                Val v;
                if (!jvalue(p, &v, e)) {
                    free(kb);
                    tab_release(t);
                    return false;
                }
                tab_bind(t, bin_new(kb, kn), v, NULL);
                free(kb);
                jws(p);
                if (p->i < p->n && p->b[p->i] == ',') {
                    p->i++;
                    continue;
                }
                if (p->i < p->n && p->b[p->i] == '}') {
                    p->i++;
                    break;
                }
                tab_release(t);
                seterr_(e, "fromjson: expected , or } in object");
                return false;
            }
        Val v;
        v.k = V_TAB;
        v.u.tab = t;
        *out = v;
        return true;
    }
    return jnumber(p, out, e);
}

bool op_fromjson(const Val *v, Val *out, SnelErr *e) {
    if (v->k != V_VEC || !is_u8_col(v->u.vec)) {
        seterr_(e, "fromjson needs a string ([u8])");
        return false;
    }
    size_t n;
    uint8_t *b = col_bytes(v->u.vec, &n);
    JP p = {b, n, 0};
    bool ok = jvalue(&p, out, e);
    if (ok) {
        jws(&p);
        if (p.i != n) {
            val_drop(*out);
            seterr_(e, "fromjson: trailing input after the value");
            ok = false;
        }
    }
    free(b);
    return ok;
}

// ---------- CSV ----------

static bool csv_field(const Val *v, S *out, SnelErr *e) {
    char buf[64];
    switch (v->k) {
        case V_NIL:
            return true; // empty field
        case V_BIT:
            sput(out, v->u.i ? "true" : "false");
            return true;
        case V_I64:
            snprintf(buf, sizeof buf, "%lld", (long long)v->u.i);
            sput(out, buf);
            return true;
        case V_U8:
            snprintf(buf, sizeof buf, "%llu", (unsigned long long)(v->u.i & 0xff));
            sput(out, buf);
            return true;
        case V_F64: {
            double x = v->u.f;
            if (!(x == x) || x > 1.7976931348623157e308 || x < -1.7976931348623157e308) {
                seterr_(e, "tocsv: inf/nan have no CSV form");
                return false;
            }
            char *f = fmt_f64(x);
            sput(out, f);
            free(f);
            return true;
        }
        case V_VEC:
            if (is_u8_col(v->u.vec)) {
                size_t n;
                uint8_t *b = col_bytes(v->u.vec, &n);
                sput_n(out, (const char *)b, n);
                free(b);
                return true;
            }
            /* fallthrough */
        default:
            seterr_(e, "tocsv: fields must be scalars or strings (CSV cannot nest)");
            return false;
    }
}

static void csv_quote(S *s, const char *b, size_t n) {
    bool need = false;
    for (size_t i = 0; i < n; i++)
        if (b[i] == ',' || b[i] == '"' || b[i] == '\n' || b[i] == '\r')
            need = true;
    if (!need) {
        sput_n(s, b, n);
        return;
    }
    sputc_(s, '"');
    for (size_t i = 0; i < n; i++) {
        if (b[i] == '"')
            sputc_(s, '"');
        sputc_(s, b[i]);
    }
    sputc_(s, '"');
}

bool op_tocsv(const Val *v, Val *out, SnelErr *e) {
    if (v->k != V_TAB) {
        seterr_(e, "tocsv needs a tab of equal-length vecs");
        return false;
    }
    Tab *t = v->u.tab;
    for (size_t i = 0; i < t->len; i++)
        if (t->vals[i].k != V_VEC || is_u8_col(t->vals[i].u.vec)) {
            seterr_(e, "tocsv: every field must be a vec of scalars");
            return false;
        }
    size_t rows = t->len ? t->vals[0].u.vec->len : 0;
    for (size_t i = 0; i < t->len; i++)
        if (t->vals[i].u.vec->len != rows) {
            seterr_(e, "tocsv: all fields must have the same length");
            return false;
        }
    S s = {0};
    for (size_t i = 0; i < t->len; i++) {
        if (i)
            sputc_(&s, ',');
        csv_quote(&s, (const char *)bin_bytes(&t->keys[i]), t->keys[i].len);
    }
    sputc_(&s, '\n');
    for (size_t r = 0; r < rows; r++) {
        for (size_t i = 0; i < t->len; i++) {
            if (i)
                sputc_(&s, ',');
            Val ev = col_elem(t->vals[i].u.vec, r);
            S f = {0};
            bool ok = csv_field(&ev, &f, e);
            val_drop(ev);
            if (!ok) {
                free(f.p);
                free(s.p);
                return false;
            }
            csv_quote(&s, f.p ? f.p : "", f.n);
            free(f.p);
        }
        sputc_(&s, '\n');
    }
    *out = s_val(&s);
    return true;
}

// records of fields, honoring quotes
typedef struct {
    char **f;
    size_t n, cap;
} Rec;
static void rec_push(Rec *r, char *s) {
    if (r->n == r->cap) {
        r->cap = r->cap ? r->cap * 2 : 8;
        r->f = realloc(r->f, r->cap * sizeof(char *));
    }
    r->f[r->n++] = s;
}
typedef struct {
    Rec *r;
    size_t n, cap;
} Recs;
static void recs_push(Recs *rs, Rec r) {
    if (rs->n == rs->cap) {
        rs->cap = rs->cap ? rs->cap * 2 : 8;
        rs->r = realloc(rs->r, rs->cap * sizeof(Rec));
    }
    rs->r[rs->n++] = r;
}
static void recs_free(Recs *rs) {
    for (size_t i = 0; i < rs->n; i++) {
        for (size_t j = 0; j < rs->r[i].n; j++)
            free(rs->r[i].f[j]);
        free(rs->r[i].f);
    }
    free(rs->r);
}

static bool csv_records(const uint8_t *b, size_t n, Recs *out, SnelErr *e) {
    Recs rs = {0};
    Rec rec = {0};
    S cur = {0};
    bool quoted = false, any = false;
    size_t i = 0;
    while (i < n) {
        uint8_t c = b[i];
        if (quoted) {
            if (c == '"') {
                if (i + 1 < n && b[i + 1] == '"') {
                    sputc_(&cur, '"');
                    i += 2;
                    continue;
                }
                quoted = false;
                i++;
                continue;
            }
            sputc_(&cur, (char)c);
            i++;
            continue;
        }
        if (c == '"') {
            quoted = true;
            any = true;
            i++;
        } else if (c == ',') {
            rec_push(&rec, cur.p ? cur.p : calloc(1, 1));
            memset(&cur, 0, sizeof cur);
            any = true;
            i++;
        } else if (c == '\r') {
            i++;
        } else if (c == '\n') {
            if (any || cur.n) {
                rec_push(&rec, cur.p ? cur.p : calloc(1, 1));
                memset(&cur, 0, sizeof cur);
                recs_push(&rs, rec);
                memset(&rec, 0, sizeof rec);
            }
            any = false;
            i++;
        } else {
            sputc_(&cur, (char)c);
            any = true;
            i++;
        }
    }
    if (quoted) {
        free(cur.p);
        recs_free(&rs);
        for (size_t j = 0; j < rec.n; j++)
            free(rec.f[j]);
        free(rec.f);
        seterr_(e, "fromcsv: unterminated quoted field");
        return false;
    }
    if (any || cur.n) {
        rec_push(&rec, cur.p ? cur.p : calloc(1, 1));
        recs_push(&rs, rec);
    } else {
        free(cur.p);
        free(rec.f);
    }
    *out = rs;
    return true;
}

static bool all_i64(char **cells, size_t n) {
    bool any = false;
    for (size_t i = 0; i < n; i++) {
        if (!cells[i][0])
            continue;
        any = true;
        char *end;
        strtoll(cells[i], &end, 10);
        if (*end)
            return false;
    }
    return any;
}
static bool all_f64(char **cells, size_t n) {
    bool any = false;
    for (size_t i = 0; i < n; i++) {
        if (!cells[i][0])
            continue;
        any = true;
        double d;
        if (!parse_f64(cells[i], &d) || !(d == d) || d > 1.7976931348623157e308 ||
            d < -1.7976931348623157e308)
            return false;
    }
    return any;
}

// infer a column from its text cells (mirrors src/interop.rs csv_column)
static bool csv_column(char **cells, size_t n, Val *out, SnelErr *e) {
    bool ints = all_i64(cells, n), nums = !ints && all_f64(cells, n);
    Val *vals = malloc((n ? n : 1) * sizeof(Val));
    for (size_t i = 0; i < n; i++) {
        if (ints) {
            vals[i] = cells[i][0] ? vi64(strtoll(cells[i], NULL, 10)) : vnil();
        } else if (nums) {
            if (cells[i][0]) {
                double d;
                parse_f64(cells[i], &d);
                vals[i] = vf64(d);
            } else
                vals[i] = vnil();
        } else {
            Val v;
            v.k = V_VEC;
            v.u.vec = col_u8s((const uint8_t *)cells[i], strlen(cells[i]));
            vals[i] = v;
        }
    }
    Col *c;
    bool ok = col_from_vals(vals, n, &c, e); // consumes vals
    free(vals);
    if (!ok)
        return false;
    Val v;
    v.k = V_VEC;
    v.u.vec = c;
    *out = v;
    return true;
}

bool op_fromcsv(const Val *v, Val *out, SnelErr *e) {
    if (v->k != V_VEC || !is_u8_col(v->u.vec)) {
        seterr_(e, "fromcsv needs a string ([u8])");
        return false;
    }
    size_t n;
    uint8_t *b = col_bytes(v->u.vec, &n);
    Recs rs = {0};
    bool ok = csv_records(b, n, &rs, e);
    free(b);
    if (!ok)
        return false;
    Tab *t = tab_new();
    if (rs.n == 0) {
        Val tv;
        tv.k = V_TAB;
        tv.u.tab = t;
        *out = tv;
        recs_free(&rs);
        return true;
    }
    Rec header = rs.r[0];
    size_t nrows = rs.n - 1;
    for (size_t ci = 0; ci < header.n; ci++) {
        char **cells = malloc((nrows ? nrows : 1) * sizeof(char *));
        for (size_t r = 0; r < nrows; r++)
            cells[r] = (ci < rs.r[r + 1].n) ? rs.r[r + 1].f[ci] : (char *)"";
        Val col;
        bool cok = csv_column(cells, nrows, &col, e);
        free(cells);
        if (!cok) {
            tab_release(t);
            recs_free(&rs);
            return false;
        }
        tab_bind(t, bin_new((const uint8_t *)header.f[ci], strlen(header.f[ci])), col, NULL);
    }
    recs_free(&rs);
    Val tv;
    tv.k = V_TAB;
    tv.u.tab = t;
    *out = tv;
    return true;
}
