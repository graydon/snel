#ifndef SNEL_LEX_H
#define SNEL_LEX_H
#include "snel.h"

typedef enum {
    TK_INT,
    TK_FLOAT,
    TK_U8,
    TK_BITVEC, // #1011 bit-vector literal ('0'/'1' digits in `bin`, `_` stripped)
    TK_STR,
    TK_SYM,
    TK_NAME,
    TK_PUNCT,
    TK_DOC,
    TK_NEWLINE,
    TK_EOF
} TokKind;

typedef struct {
    TokKind k;
    uint32_t at;
    uint8_t u8;        // TK_U8 ('c' char or '\xNN' hex byte)
    uint64_t mag;      // TK_INT magnitude (range-checked at parser; lets -2^63 round-trip)
    double f;          // TK_FLOAT
    Bin bin;           // TK_STR, TK_SYM, TK_NAME, TK_DOC
    const char *punct; // TK_PUNCT
} Tok;

typedef struct {
    Tok *t;
    size_t n, cap;
} Lexed;

bool lex(const char *src, Lexed *L, SnelErr *err);

#endif
