// A small Language Server for Snel, over stdio (`snel lsp`). Mirrors
// src/lsp.rs. Like the Rust side it needs no library: requests are decoded with
// the language's own JSON reader (interop.c), and replies are written with the
// same escaping rules.
//
// It only *parses and checks*; it never evaluates. An editor must not run a
// user's `io` effects on every keystroke, so diagnostics come from the parser
// and the static checker alone, and `use` imports are left unresolved.
#include "snel.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

bool op_fromjson(const Val *v, Val *out, SnelErr *e);
int op_arity(int op); // check.c
bool is_u8_col(const Col *c);
uint8_t *col_bytes(const Col *c, size_t *len);

// strdup / strncasecmp are not C99; keep the port self-contained.
static char *dup_str(const char *s) {
    size_t n = strlen(s) + 1;
    char *p = malloc(n);
    memcpy(p, s, n);
    return p;
}
static int ci_prefix(const char *s, const char *pfx) {
    for (; *pfx; s++, pfx++) {
        char a = *s, b = *pfx;
        if (a >= 'A' && a <= 'Z')
            a += 32;
        if (a != b)
            return 1;
    }
    return 0;
}

// ---------- open documents ----------
#define DOCS_MAX 64
typedef struct {
    char *uri;
    char *text;
} Doc;
static Doc g_docs[DOCS_MAX];
static size_t g_ndocs;

static char *doc_get(const char *uri) {
    for (size_t i = 0; i < g_ndocs; i++)
        if (!strcmp(g_docs[i].uri, uri))
            return g_docs[i].text;
    return NULL;
}
static void doc_put(const char *uri, const char *text) {
    for (size_t i = 0; i < g_ndocs; i++)
        if (!strcmp(g_docs[i].uri, uri)) {
            free(g_docs[i].text);
            g_docs[i].text = dup_str(text);
            return;
        }
    if (g_ndocs < DOCS_MAX) {
        g_docs[g_ndocs].uri = dup_str(uri);
        g_docs[g_ndocs].text = dup_str(text);
        g_ndocs++;
    }
}
static void doc_del(const char *uri) {
    for (size_t i = 0; i < g_ndocs; i++)
        if (!strcmp(g_docs[i].uri, uri)) {
            free(g_docs[i].uri);
            free(g_docs[i].text);
            g_docs[i] = g_docs[--g_ndocs];
            return;
        }
}

// ---------- JSON helpers over Snel values ----------

static Val *jfield(const Val *v, const char *k) {
    if (v->k != V_TAB)
        return NULL;
    return tab_get(v->u.tab, (const uint8_t *)k, strlen(k));
}
// a JSON string field as a fresh C string (caller frees), or NULL
static char *jstr_of(const Val *v) {
    if (!v || v->k != V_VEC || !is_u8_col(v->u.vec))
        return NULL;
    size_t n;
    uint8_t *b = col_bytes(v->u.vec, &n);
    char *s = malloc(n + 1);
    memcpy(s, b, n);
    s[n] = 0;
    free(b);
    return s;
}
static long jint_of(const Val *v, long dflt) {
    if (!v)
        return dflt;
    if (v->k == V_I64)
        return (long)v->u.i;
    if (v->k == V_F64)
        return (long)v->u.f;
    return dflt;
}

// escape a string into a JSON literal appended to a malloc'd buffer
typedef struct {
    char *p;
    size_t n, cap;
} B;
static void bput_n(B *b, const char *s, size_t n) {
    if (b->n + n + 1 > b->cap) {
        b->cap = (b->n + n + 1) * 2;
        b->p = realloc(b->p, b->cap);
    }
    memcpy(b->p + b->n, s, n);
    b->n += n;
    b->p[b->n] = 0;
}
static void bput(B *b, const char *s) {
    bput_n(b, s, strlen(s));
}
static void bjstr(B *b, const char *s) {
    bput(b, "\"");
    for (const unsigned char *p = (const unsigned char *)s; *p; p++) {
        char tmp[8];
        switch (*p) {
            case '"':
                bput(b, "\\\"");
                break;
            case '\\':
                bput(b, "\\\\");
                break;
            case '\n':
                bput(b, "\\n");
                break;
            case '\t':
                bput(b, "\\t");
                break;
            case '\r':
                bput(b, "\\r");
                break;
            default:
                if (*p < 0x20) {
                    snprintf(tmp, sizeof tmp, "\\u%04x", *p);
                    bput(b, tmp);
                } else
                    bput_n(b, (const char *)p, 1);
        }
    }
    bput(b, "\"");
}

// ---------- positions ----------

// a byte offset as an LSP (line, utf-16 character) position
static void position(const char *src, uint32_t at, unsigned *line, unsigned *ch) {
    size_t len = strlen(src);
    if (at > len)
        at = (uint32_t)len;
    unsigned ln = 0;
    size_t ls = 0;
    for (size_t i = 0; i < at; i++)
        if (src[i] == '\n') {
            ln++;
            ls = i + 1;
        }
    unsigned col = 0;
    for (size_t i = ls; i < at;) {
        unsigned char c = (unsigned char)src[i];
        size_t adv = c < 0x80 ? 1 : (c < 0xe0 ? 2 : (c < 0xf0 ? 3 : 4));
        col += (adv == 4) ? 2 : 1; // utf-16 code units
        i += adv;
    }
    *line = ln;
    *ch = col;
}

// ---------- protocol framing ----------

static void send_body(const char *body) {
    printf("Content-Length: %zu\r\n\r\n%s", strlen(body), body);
    fflush(stdout);
}
static void respond(const char *id, const char *result) {
    B b = {0};
    bput(&b, "{\"jsonrpc\":\"2.0\",\"id\":");
    bput(&b, id);
    bput(&b, ",\"result\":");
    bput(&b, result);
    bput(&b, "}");
    send_body(b.p);
    free(b.p);
}

// read one framed message body (caller frees); NULL at end of input
static char *read_message(void) {
    char header[8192];
    size_t hn = 0;
    for (;;) {
        int c = getchar();
        if (c == EOF)
            return NULL;
        if (hn + 1 >= sizeof header)
            return NULL;
        header[hn++] = (char)c;
        header[hn] = 0;
        if (hn >= 4 && !memcmp(header + hn - 4, "\r\n\r\n", 4))
            break;
    }
    size_t len = 0;
    for (char *l = header; l && *l;) {
        char *nl = strstr(l, "\r\n");
        if (nl)
            *nl = 0;
        if (!ci_prefix(l, "content-length:"))
            len = (size_t)strtoul(l + 15, NULL, 10);
        if (!nl)
            break;
        l = nl + 2;
    }
    if (!len)
        return NULL;
    char *body = malloc(len + 1);
    size_t got = 0;
    while (got < len) {
        size_t r = fread(body + got, 1, len - got, stdin);
        if (r == 0) {
            free(body);
            return NULL;
        }
        got += r;
    }
    body[len] = 0;
    return body;
}

// ---------- diagnostics ----------

// parse + check only; never evaluate. Returns true when a problem was found.
static bool diagnose(const char *src, char *msg, size_t msgn, uint32_t *at) {
    size_t nds;
    SnelErr pe;
    Node *ds = parse_unit(src, &nds, &pe);
    if (!ds) {
        snprintf(msg, msgn, "parse error: %s", pe.msg);
        *at = pe.span;
        return true;
    }
    char eb[512];
    if (!check_unit(ds, nds, NULL, 0, NULL, NULL, 0, eb, sizeof eb)) {
        snprintf(msg, msgn, "check error: %s", check_last_msg());
        *at = check_last_span();
        return true;
    }
    return false;
}

static void publish(const char *uri, const char *src) {
    char msg[512];
    uint32_t at = 0;
    B b = {0};
    bput(&b, "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{\"uri\":");
    bjstr(&b, uri);
    bput(&b, ",\"diagnostics\":[");
    if (diagnose(src, msg, sizeof msg, &at)) {
        unsigned line, ch;
        position(src, at, &line, &ch);
        // the span end is unknown; underline to the next whitespace
        unsigned end = ch + 1;
        size_t len = strlen(src);
        for (size_t i = at; i < len; i++) {
            if (src[i] == ' ' || src[i] == '\t' || src[i] == '\n' || src[i] == '\r')
                break;
            if (i > at)
                end++;
        }
        char range[256];
        snprintf(range, sizeof range,
                 "{\"range\":{\"start\":{\"line\":%u,\"character\":%u},"
                 "\"end\":{\"line\":%u,\"character\":%u}},\"severity\":1,\"source\":\"snel\","
                 "\"message\":",
                 line, ch, line, end);
        bput(&b, range);
        bjstr(&b, msg);
        bput(&b, "}");
    }
    bput(&b, "]}}");
    send_body(b.p);
    free(b.p);
}

// ---------- hover ----------

static char *word_at(const char *src, unsigned line, unsigned character) {
    const char *l = src;
    for (unsigned i = 0; i < line && l; i++) {
        const char *nl = strchr(l, '\n');
        l = nl ? nl + 1 : NULL;
    }
    if (!l)
        return NULL;
    const char *eol = strchr(l, '\n');
    size_t ll = eol ? (size_t)(eol - l) : strlen(l);
    size_t i = character < ll ? character : ll;
#define ISW(c) (((c) >= 'a' && (c) <= 'z') || ((c) >= 'A' && (c) <= 'Z') || \
                ((c) >= '0' && (c) <= '9') || (c) == '_')
    size_t s = i, e = i;
    while (s > 0 && ISW((unsigned char)l[s - 1]))
        s--;
    while (e < ll && ISW((unsigned char)l[e]))
        e++;
#undef ISW
    if (s == e)
        return NULL;
    char *w = malloc(e - s + 1);
    memcpy(w, l + s, e - s);
    w[e - s] = 0;
    return w;
}

static const char *KW_DOC[][2] = {
    {"let", "bind a name: `let x = e;`"},
    {"fun", "function literal or declaration: `fun f(x: T) -> T = e;`"},
    {"type", "named type: `type n = T;`, or a predicate subtype `type n = T where p;`"},
    {"mod", "module: sugar over a fun returning a tab of its `pub` names"},
    {"pub", "export this declaration from the unit"},
    {"use", "import another unit; resolved and typed at check time"},
    {"do", "block: `do d; ...; e end`, the same as `( d; ...; e )`"},
    {"end", "closes a `do` block"},
    {"if", "scalar, lazy conditional; use `select` for a `[bit]` mask"},
    {"try", "`try e else f` - recover from `err` (values roll back, effects do not)"},
    {"err", "raise an error, caught by an enclosing `try`"},
    {"is", "type test: scalar -> bit, vec vs a scalar type -> [bit]"},
    {"where", "attaches a predicate to a `type`"},
    {"nil", "the absent value"},
    {"true", "bit literal"},
    {"false", "bit literal"},
    {NULL, NULL},
};

// markdown for a word, or NULL (caller frees)
static char *hover_text(const char *w) {
    int op = op_by_name((const uint8_t *)w, strlen(w));
    if (op >= 0) {
        int n = op_arity(op);
        char *s = malloc(256);
        snprintf(s, 256,
                 "**%s** \u2014 builtin, %d argument%s\n\nA language-level name: resolved directly, "
                 "never shadowed.",
                 w, n, n == 1 ? "" : "s");
        return s;
    }
    for (int i = 0; KW_DOC[i][0]; i++)
        if (!strcmp(KW_DOC[i][0], w)) {
            size_t n = strlen(w) + strlen(KW_DOC[i][1]) + 24;
            char *s = malloc(n);
            snprintf(s, n, "**%s** \u2014 %s", w, KW_DOC[i][1]);
            return s;
        }
    return NULL;
}

// ---------- server ----------

int lsp_serve(void) {
    char *body;
    while ((body = read_message()) != NULL) {
        Val doc_v;
        {
            Val src;
            src.k = V_VEC;
            src.u.vec = col_u8s((const uint8_t *)body, strlen(body));
            SnelErr e;
            bool ok = op_fromjson(&src, &doc_v, &e);
            val_drop(src);
            free(body);
            if (!ok)
                continue;
        }
        Val *m = jfield(&doc_v, "method");
        char *method = jstr_of(m);
        // an id may be a number or a string; echo it back in kind
        Val *idv = jfield(&doc_v, "id");
        char idbuf[256] = {0};
        bool has_id = false;
        if (idv) {
            if (idv->k == V_I64) {
                snprintf(idbuf, sizeof idbuf, "%lld", (long long)idv->u.i);
                has_id = true;
            } else {
                char *s = jstr_of(idv);
                if (s) {
                    B b = {0};
                    bjstr(&b, s);
                    snprintf(idbuf, sizeof idbuf, "%s", b.p);
                    free(b.p);
                    free(s);
                    has_id = true;
                }
            }
        }
        Val *params = jfield(&doc_v, "params");

        if (!method) {
            val_drop(doc_v);
            continue;
        }
        if (!strcmp(method, "initialize")) {
            if (has_id)
                respond(idbuf,
                        "{\"capabilities\":{\"textDocumentSync\":1,\"hoverProvider\":true},"
                        "\"serverInfo\":{\"name\":\"snel\",\"version\":\"0.1.0\"}}");
        } else if (!strcmp(method, "shutdown")) {
            if (has_id)
                respond(idbuf, "null");
        } else if (!strcmp(method, "exit")) {
            free(method);
            val_drop(doc_v);
            return 0;
        } else if (!strcmp(method, "textDocument/didOpen")) {
            Val *td = params ? jfield(params, "textDocument") : NULL;
            char *uri = td ? jstr_of(jfield(td, "uri")) : NULL;
            char *text = td ? jstr_of(jfield(td, "text")) : NULL;
            if (uri && text) {
                publish(uri, text);
                doc_put(uri, text);
            }
            free(uri);
            free(text);
        } else if (!strcmp(method, "textDocument/didChange")) {
            Val *td = params ? jfield(params, "textDocument") : NULL;
            char *uri = td ? jstr_of(jfield(td, "uri")) : NULL;
            char *text = NULL;
            Val *ch = params ? jfield(params, "contentChanges") : NULL;
            if (ch && ch->k == V_VEC && ch->u.vec->len > 0) { // full sync: last change
                Val last = col_elem(ch->u.vec, ch->u.vec->len - 1);
                text = jstr_of(jfield(&last, "text"));
                val_drop(last);
            }
            if (uri && text) {
                publish(uri, text);
                doc_put(uri, text);
            }
            free(uri);
            free(text);
        } else if (!strcmp(method, "textDocument/didSave")) {
            Val *td = params ? jfield(params, "textDocument") : NULL;
            char *uri = td ? jstr_of(jfield(td, "uri")) : NULL;
            if (uri) {
                char *t = doc_get(uri);
                if (t)
                    publish(uri, t);
            }
            free(uri);
        } else if (!strcmp(method, "textDocument/didClose")) {
            Val *td = params ? jfield(params, "textDocument") : NULL;
            char *uri = td ? jstr_of(jfield(td, "uri")) : NULL;
            if (uri)
                doc_del(uri);
            free(uri);
        } else if (!strcmp(method, "textDocument/hover")) {
            if (has_id) {
                Val *td = params ? jfield(params, "textDocument") : NULL;
                char *uri = td ? jstr_of(jfield(td, "uri")) : NULL;
                Val *pos = params ? jfield(params, "position") : NULL;
                unsigned line = (unsigned)jint_of(pos ? jfield(pos, "line") : NULL, 0);
                unsigned chr = (unsigned)jint_of(pos ? jfield(pos, "character") : NULL, 0);
                char *text = uri ? doc_get(uri) : NULL;
                char *w = text ? word_at(text, line, chr) : NULL;
                char *md = w ? hover_text(w) : NULL;
                if (md) {
                    B b = {0};
                    bput(&b, "{\"contents\":{\"kind\":\"markdown\",\"value\":");
                    bjstr(&b, md);
                    bput(&b, "}}");
                    respond(idbuf, b.p);
                    free(b.p);
                } else
                    respond(idbuf, "null");
                free(uri);
                free(w);
                free(md);
            }
        } else if (has_id) {
            respond(idbuf, "null"); // unknown request: don't leave the client waiting
        }
        free(method);
        val_drop(doc_v);
    }
    return 0;
}
