// Builtin op name table and small AST/type constructors. Nodes and types are
// arena-allocated (leaked; the process is short-lived).
#include "snel.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const char *OP_NAMES[OP__COUNT] = {
    "add",     "sub",     "mul",    "div",    "rem",    "neg",      "abs",     "itof",  "ftoi",
    "sqrt",    "floor",   "ceil",   "sign",   "ord",    "chr",      "eq",      "ne",    "lt",
    "le",      "gt",      "ge",     "and",    "or",     "not",      "len",     "cat",   "iota",
    "grade",   "sum",     "prod",   "min",    "max",    "isnil",    "all",     "any",   "rev",
    "take",    "drop",    "first",  "last",   "which",  "distinct", "in",      "map",   "map2",
    "fold",    "scan",    "filter", "group",  "get",    "select",   "find",    "split", "join",
    "locals",  "reflect", "show",   "encode", "decode", "parse",    "unparse", "at",    "rep",
    "scatter", "shift",   "sums",   "prods",  "member", "matches",  "runs",    "partition",
    "windows", "tojson",  "fromjson", "tocsv",  "fromcsv"};

int op_by_name(const uint8_t *b, size_t n) {
    for (int i = 0; i < OP__COUNT; i++)
        if (strlen(OP_NAMES[i]) == n && memcmp(OP_NAMES[i], b, n) == 0)
            return i;
    return -1;
}
const char *op_name(int op) {
    return OP_NAMES[op];
}

Node *node_new(AKind k, uint32_t lo) {
    Node *n = calloc(1, sizeof(Node));
    n->k = k;
    n->lo = lo;
    n->hi = lo;
    n->has_url = false;
    n->op_cache = -2; // unresolved (0 is a valid op index, so calloc's 0 won't do)
    n->var_slot = -1;
    return n;
}

Ty *ty_alloc(void) {
    return calloc(1, sizeof(Ty));
}

// Flatten + dedup (first-appearance order), collapsing singletons. Shared by
// the parser and cat.
Ty union_of_pub(Ty *parts, size_t n) {
    Ty flat[64];
    size_t fn = 0;
    for (size_t i = 0; i < n; i++) {
        if (parts[i].k == T_UNION)
            for (size_t j = 0; j < parts[i].n; j++)
                flat[fn++] = parts[i].elem[j];
        else
            flat[fn++] = parts[i];
    }
    Ty out[64];
    size_t on = 0;
    for (size_t i = 0; i < fn; i++) {
        bool dup = false;
        char *fi = fmt_ty(&flat[i]);
        for (size_t j = 0; j < on; j++) {
            char *fj = fmt_ty(&out[j]);
            if (!strcmp(fi, fj))
                dup = true;
            free(fj);
            if (dup)
                break;
        }
        free(fi);
        if (!dup)
            out[on++] = flat[i];
    }
    if (on == 1)
        return out[0];
    Ty u;
    memset(&u, 0, sizeof u);
    u.k = T_UNION;
    u.n = on;
    u.elem = malloc(on * sizeof(Ty));
    memcpy(u.elem, out, on * sizeof(Ty));
    return u;
}
