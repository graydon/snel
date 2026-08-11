// Lexer. Mirrors src/lex.rs. Doc comments (full-line `--` immediately before a
// declaration) become tokens; other `--` comments are whitespace. Newlines are
// tokens (declaration separators outside brackets).
#include "lex.h"
#include "snel.h"
#include <ctype.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const char *PUNCTS[] = {"->", "<=", ">=", "<>", "|>", "(",  ")", "[", "]", "{", "}", ",",
                               ";",  ".",  "=",  "<",  ">",  "+",  "-", "*", "/", "%", ":", "|",
                               "?",  NULL};

static void push(Lexed *L, Tok t) {
    if (L->n == L->cap) {
        L->cap = L->cap ? L->cap * 2 : 64;
        L->t = realloc(L->t, L->cap * sizeof(Tok));
    }
    L->t[L->n++] = t;
}
static Tok mk(TokKind k, uint32_t at) {
    Tok t;
    memset(&t, 0, sizeof t);
    t.k = k;
    t.at = at;
    return t;
}

// returns false and fills err on error
bool lex(const char *src, Lexed *L, SnelErr *err) {
    memset(L, 0, sizeof *L);
    size_t len = strlen(src), i = 0;
    bool line_start = true;
    while (i < len) {
        unsigned char c = src[i];
        if (c == '\n') {
            push(L, mk(TK_NEWLINE, i));
            i++;
            line_start = true;
            continue;
        }
        if (isspace(c)) {
            i++;
            continue;
        }
        if (c == '-' && src[i + 1] == '-') {
            size_t start = i, j = i + 2;
            while (j < len && src[j] != '\n')
                j++;
            if (line_start) {
                size_t a = i + 2, b = j;
                while (a < b && isspace((unsigned char)src[a]))
                    a++;
                while (b > a && isspace((unsigned char)src[b - 1]))
                    b--;
                if (L->n > 0 && L->t[L->n - 1].k == TK_DOC) {
                    Bin *prev = &L->t[L->n - 1].bin;
                    size_t pl = prev->len;
                    uint8_t *tmp = malloc(pl + 1 + (b - a));
                    memcpy(tmp, bin_bytes(prev), pl);
                    tmp[pl] = '\n';
                    memcpy(tmp + pl + 1, src + a, b - a);
                    Bin nb = bin_new(tmp, pl + 1 + (b - a));
                    bin_drop(prev);
                    *prev = nb;
                    free(tmp);
                } else {
                    Tok t = mk(TK_DOC, start);
                    t.bin = bin_new((const uint8_t *)src + a, b - a);
                    push(L, t);
                }
                if (j < len)
                    j++; // swallow newline so doc glues to next decl
            }
            i = j;
            continue;
        }
        line_start = false;
        // u8 char literal: 'c', an escape '\n' '\t' '\\' '\'', or hex byte '\xNN'
        if (c == '\'') {
            uint8_t v;
            size_t adv;
            if (src[i + 1] == '\\') {
                char e = src[i + 2];
                if (e == 'n') {
                    v = '\n';
                    adv = 3;
                } else if (e == 't') {
                    v = '\t';
                    adv = 3;
                } else if (e == '\\') {
                    v = '\\';
                    adv = 3;
                } else if (e == '\'') {
                    v = '\'';
                    adv = 3;
                } else if (e == 'x') {
                    if (!isxdigit((unsigned char)src[i + 3]) ||
                        !isxdigit((unsigned char)src[i + 4])) {
                        snprintf(err->msg, sizeof err->msg, "bad \\x in char literal");
                        err->span = i;
                        return false;
                    }
                    char h[3] = {src[i + 3], src[i + 4], 0};
                    v = (uint8_t)strtol(h, NULL, 16);
                    adv = 5;
                } else {
                    snprintf(err->msg, sizeof err->msg, "bad char escape");
                    err->span = i;
                    return false;
                }
            } else if (src[i + 1] != '\'' && src[i + 1] != '\n') {
                v = (uint8_t)src[i + 1];
                adv = 2;
            } else {
                snprintf(err->msg, sizeof err->msg, "bad char literal");
                err->span = i;
                return false;
            }
            if (src[i + adv] != '\'') {
                snprintf(err->msg, sizeof err->msg,
                         "char literal must be one char in single quotes");
                err->span = i;
                return false;
            }
            Tok t = mk(TK_U8, i);
            t.u8 = v;
            push(L, t);
            i += adv + 1;
            continue;
        }
        // bit-vector literal: :1011 (a [bit]); `_` allowed. `:name` (a symbol)
        // stays a punct — only `:` directly followed by a 0/1 digit is a bit vec.
        if (c == ':' && (src[i + 1] == '0' || src[i + 1] == '1')) {
            size_t j = i + 1;
            while (j < len && (src[j] == '0' || src[j] == '1' || src[j] == '_'))
                j++;
            uint8_t *buf = malloc(j - i);
            size_t bl = 0;
            for (size_t k = i + 1; k < j; k++)
                if (src[k] != '_')
                    buf[bl++] = src[k];
            Tok t = mk(TK_BITVEC, i);
            t.bin = bin_new(buf, bl);
            free(buf);
            push(L, t);
            i = j;
            continue;
        }
        if (isdigit(c)) {
            // hex / binary integer literals: 0x… / 0b…, `_` allowed as a separator
            if (c == '0' && (src[i + 1] == 'x' || src[i + 1] == 'b')) {
                bool hex = src[i + 1] == 'x';
                size_t j = i + 2;
                while (j < len && (src[j] == '_' || (hex ? isxdigit((unsigned char)src[j])
                                                         : (src[j] == '0' || src[j] == '1'))))
                    j++;
                char tmp[80];
                size_t tl = 0;
                for (size_t k = i + 2; k < j && tl + 1 < sizeof tmp; k++)
                    if (src[k] != '_')
                        tmp[tl++] = src[k];
                tmp[tl] = 0;
                if (tl == 0) {
                    snprintf(err->msg, sizeof err->msg, "expected digits after 0%c", src[i + 1]);
                    err->span = i;
                    return false;
                }
                errno = 0;
                char *e2;
                unsigned long long m = strtoull(tmp, &e2, hex ? 16 : 2);
                if (errno == ERANGE || *e2) {
                    snprintf(err->msg, sizeof err->msg, "integer literal out of range");
                    err->span = i;
                    return false;
                }
                Tok t = mk(TK_INT, i);
                t.mag = m;
                push(L, t);
                i = j;
                continue;
            }
            size_t start = i, j = i;
#define DIGIT_(x) (isdigit((unsigned char)(x)) || (x) == '_') // `_` separator allowed
            while (j < len && DIGIT_(src[j]))
                j++;
            bool is_float = false;
            if (j < len && src[j] == '.' && isdigit((unsigned char)src[j + 1])) {
                is_float = true;
                j++;
                while (j < len && DIGIT_(src[j]))
                    j++;
            }
            if (j < len && (src[j] == 'e' || src[j] == 'E')) {
                size_t k = j + 1;
                if (k < len && (src[k] == '+' || src[k] == '-'))
                    k++;
                if (k < len && isdigit((unsigned char)src[k])) {
                    is_float = true;
                    j = k;
                    while (j < len && DIGIT_(src[j]))
                        j++;
                }
            }
#undef DIGIT_
            char tmp[64];
            size_t tl = 0;
            for (size_t k = start; k < j && tl + 1 < sizeof tmp; k++)
                if (src[k] != '_')
                    tmp[tl++] = src[k];
            tmp[tl] = 0;
            if (is_float) {
                double d;
                if (!parse_f64(tmp, &d)) {
                    snprintf(err->msg, sizeof err->msg, "bad float");
                    err->span = start;
                    return false;
                }
                Tok t = mk(TK_FLOAT, start);
                t.f = d;
                push(L, t);
            } else {
                errno = 0;
                char *e2;
                unsigned long long m = strtoull(tmp, &e2, 10);
                if (errno == ERANGE || *e2) {
                    snprintf(err->msg, sizeof err->msg, "int out of range");
                    err->span = start;
                    return false;
                }
                Tok t = mk(TK_INT, start);
                t.mag = m;
                push(L, t);
            }
            i = j;
            continue;
        }
        if (isalpha(c) || c == '_') {
            size_t start = i, j = i;
            while (j < len && (isalnum((unsigned char)src[j]) || src[j] == '_'))
                j++;
            Tok t = mk(TK_NAME, start);
            t.bin = bin_new((const uint8_t *)src + start, j - start);
            push(L, t);
            i = j;
            continue;
        }
        if (c == '"') {
            size_t start = i, j = i + 1;
            uint8_t *out = malloc(len);
            size_t on = 0;
            for (;;) {
                if (j >= len) {
                    snprintf(err->msg, sizeof err->msg, "unterminated string");
                    err->span = start;
                    free(out);
                    return false;
                }
                if (src[j] == '"')
                    break;
                if (src[j] == '\\') {
                    j++;
                    char e = src[j];
                    if (e == '\\')
                        out[on++] = '\\';
                    else if (e == '"')
                        out[on++] = '"';
                    else if (e == 'n')
                        out[on++] = '\n';
                    else if (e == 't')
                        out[on++] = '\t';
                    else if (e == 'x') {
                        char h[3] = {src[j + 1], src[j + 2], 0};
                        out[on++] = (uint8_t)strtol(h, NULL, 16);
                        j += 2;
                    } else {
                        snprintf(err->msg, sizeof err->msg, "bad escape");
                        err->span = j;
                        free(out);
                        return false;
                    }
                    j++;
                } else
                    out[on++] = src[j++];
            }
            Tok t = mk(TK_STR, start);
            t.bin = bin_new(out, on);
            push(L, t);
            free(out);
            i = j + 1;
            continue;
        }
        // punctuation
        int matched = -1;
        for (int p = 0; PUNCTS[p]; p++) {
            size_t pl = strlen(PUNCTS[p]);
            if (i + pl <= len && memcmp(src + i, PUNCTS[p], pl) == 0) {
                matched = p;
                break;
            }
        }
        if (matched < 0) {
            snprintf(err->msg, sizeof err->msg, "stray character %c", c);
            err->span = i;
            return false;
        }
        Tok t = mk(TK_PUNCT, i);
        t.punct = PUNCTS[matched];
        push(L, t);
        i += strlen(PUNCTS[matched]);
    }
    push(L, mk(TK_EOF, len));
    return true;
}
