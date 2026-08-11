// snel — C99 port. Interface. See ../SPEC.md and the Rust reference in ../src.
// Behavior is identical to the Rust build (text output, binary bytes, errors).
#ifndef SNEL_H
#define SNEL_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

// ---------- values ----------
// Refcounted, immutable, functional-but-in-place. Four kinds: scalar (nil/bit/i64/f64/
// bin), vec (column), tab, fun. bins use small-buffer optimization (<=14B).

typedef enum { V_NIL, V_BIT, V_I64, V_F64, V_U8, V_VEC, V_TAB, V_FUN, V_PRIM } VKind;

// A byte buffer with SSO. Owns a heap block only when len > 14. Backs prim names,
// tab keys, and the [u8] column payload.
typedef struct {
    uint32_t len;
    bool heap;
    union {
        uint8_t sso[15];
        uint8_t *ptr; // refcount stored in a header before *ptr; see bin_*
    } u;
} Bin;

typedef struct Col Col;
typedef struct Tab Tab;
typedef struct Clo Clo;

typedef struct {
    VKind k;
    union {
        int64_t i; // V_BIT (0/1), V_I64, V_U8 (byte)
        double f;  // V_F64
        Bin bin;   // V_PRIM (primitive name)
        Col *vec;  // V_VEC (refcounted); a string is a [u8] vec
        Tab *tab;  // V_TAB (refcounted)
        Clo *fun;  // V_FUN (refcounted)
    } u;
} Val;

// Packed bit vector, LSB-first per 64-bit word.
typedef struct {
    size_t len;
    uint64_t *w;
    size_t wcap;
} Bits;

// P_U8S: a [u8] column's bytes (one Bin). P_VECS: a [[T]] column (array of
// sub-columns, incl. columns of strings). P_TABS: a [tab] column.
typedef enum { P_BITS, P_I64S, P_F64S, P_U8S, P_VECS, P_TABS } PKind;

// One case payload of a column (flat homogeneous buffer).
typedef struct {
    PKind k;
    union {
        Bits bits;
        int64_t *i64;
        double *f64;
        Bin u8s;    // P_U8S: the byte buffer of a [u8] column
        Col **vecs; // P_VECS: each refcounted
        Tab **tab;  // P_TABS: each refcounted
    } u;
} Payload;

// A column: len elements; optional presence bitmap (nil admission); optional
// case selector (unions of >=2 non-nil cases); one payload per case.
struct Col {
    int32_t rc;
    size_t len;
    bool has_present;
    Bits present;
    bool has_sel;
    uint8_t *sel;
    uint8_t ncases;
    Payload cases[8];
};

// Ordered key->value map (byte-string keys), unique, right-biased rebinding.
struct Tab {
    int32_t rc;
    size_t len, cap;
    Bin *keys;
    Val *vals;
    Bin *docs; // doc per field; docs[i].len==0 && !heap means none
    bool *has_doc;
};

// A type. Mirrors ast::Ty.
typedef enum { T_NIL, T_BIT, T_I64, T_F64, T_U8, T_VEC, T_UNION, T_TAB, T_FUN, T_NAME } TKind;
typedef struct Ty Ty;
struct Ty {
    TKind k;
    // T_VEC: elem[0]; T_UNION/T_FUN args: elem[0..n); T_FUN ret: ret
    Ty *elem;
    size_t n;
    Ty *ret;     // T_FUN
    Bin *fields; // T_TAB field names (n of them)
    Bin name;    // T_NAME
};

// AST node kinds. Mirrors ast::Ast.
typedef enum {
    A_LIT,
    A_VAR,
    A_PROJ,
    A_IDX,
    A_APP,
    A_VEC,
    A_TAB,
    A_FUN,
    A_IF,
    A_TRY,
    A_ERR,
    A_IS,
    A_AS,
    A_SEQ,
    A_LET,
    A_TYP,
    A_USE
} AKind;

typedef struct Node Node;
struct Node {
    AKind k;
    uint32_t lo, hi; // source span
    Val lit;         // A_LIT
    Bin name;        // A_VAR/A_PROJ field/A_LET-A_TYP-A_USE name
    Node *a, *b, *c; // children (roles per kind)
    Node *kids;
    size_t nkids; // A_APP args, A_VEC elems, A_SEQ decls, A_TAB vals
    Bin *keys;
    size_t nkeys; // A_TAB keys
    Ty ty;
    bool has_ty; // A_AS/A_IS/A_LET annotation, A_FUN ret
    // A_FUN params:
    Bin *params;
    Ty *ptypes;
    size_t nparams;
    Bin doc;
    bool has_doc; // decl doc
    Bin url;      // A_USE: `use x = "url"` (remote units are unsupported in C)
    bool has_url;
    bool is_pub;  // decl pub flag
    int op_cache; // A_APP: resolved builtin op, -1 = not a builtin, -2 = unresolved
    int var_slot; // A_VAR: cached env slot (inline cache), -1 = unknown
};

// A closure.
struct Clo {
    int32_t rc;
    Bin *params;
    Ty *ptypes;
    size_t nparams;
    Ty ret;
    Node *body; // shared, owned by the source AST arena
    Tab *env;   // captured, refcounted
};

// ---------- refcount / value helpers ----------
// val_clone/val_drop are on the hottest path (every arg, binding, and element).
// Scalars (kind < V_VEC) carry no refcount, so handle them inline and only call
// out for the refcounted kinds.
Val val_retain_heap(Val v);
void val_release_heap(Val v);
static inline Val val_clone(Val v) {
    return v.k >= V_VEC ? val_retain_heap(v) : v;
}
static inline void val_drop(Val v) {
    if (v.k >= V_VEC)
        val_release_heap(v);
}
Col *col_retain(Col *c);
void col_release(Col *c);
Tab *tab_retain(Tab *t);
void tab_release(Tab *t);

Bin bin_new(const uint8_t *b, size_t n);
Bin bin_str(const char *s);
Bin bin_clone(Bin b);
void bin_drop(Bin *b);
const uint8_t *bin_bytes(const Bin *b);
bool bin_eq(const Bin *a, const Bin *b);
bool bin_is_sym(const Bin *b);
bool bin_is_ident(const Bin *b);
bool bin_is_utf8(const uint8_t *b, size_t n);
Col *col_u8s(const uint8_t *b, size_t n);

Bits bits_new(size_t len, bool fill);
bool bits_get(const Bits *b, size_t i);
void bits_set(Bits *b, size_t i, bool v);
void bits_push(Bits *b, bool v);
Bits bits_clone(const Bits *b);
void bits_free(Bits *b);

Tab *tab_new(void);
Tab *tab_clone(const Tab *t);
void tab_bind(Tab *t, Bin key, Val v, const Bin *doc);
Val *tab_get(Tab *t, const uint8_t *k, size_t n);

Col *col_simple(Payload p); // takes ownership of payload buffers

// ---------- error handling (transactions) ----------
// A failable computation longjmps to the nearest try; see eval.c.
typedef struct {
    char msg[256];
    uint32_t span;
} SnelErr;

// ---------- pipeline ----------
typedef struct Parser Parser;
// Parse a whole unit into a NUL-terminated array of decl nodes (arena-owned).
Node *parse_unit(const char *src, size_t *ndecls, SnelErr *err);

// Type value <-> Ty, AST <-> tab (wire.c)
Val ty_to_val(const Ty *t);
bool val_to_ty(const Val *v, Ty *out);
Val ast_to_val(const Node *n);
bool val_to_ast(const Val *v, Node **out, SnelErr *err); // allocates arena

// Binary format (wire.c)
void encode_val(const Val *v, uint8_t **buf, size_t *len, size_t *cap);
bool decode_val(const uint8_t *buf, size_t len, size_t *pos, Val *out, SnelErr *err);

// Printing (print.c)
char *fmt_val(const Val *v); // malloc'd
char *fmt_ty(const Ty *t);   // malloc'd
char *fmt_node(const Node *n, int prec);
char *fmt_program(const Node *ds, size_t n);
Val col_elem(const Col *c, size_t i);
Ty col_ty(const Col *c);
Ty val_ty(const Val *v);
char *fmt_f64(double x);
bool parse_f64(const char *s, double *out);
double canon_f64(double x);

// Ops (ops.c) — return false and set err on failure.
bool op_arith(int op, Val a, Val b, Val *out, SnelErr *e);
bool op_unary(int op, Val a, Val *out, SnelErr *e);
bool op_compare(int op, Val a, Val b, Val *out, SnelErr *e);
bool op_boolean(int op, Val *args, size_t n, Val *out, SnelErr *e);
bool op_index(const Val *target, const Val *ix, Val *out, SnelErr *e);
bool col_from_vals(Val *vals, size_t n, Col **out, SnelErr *e);
bool coerce_col(const Col *c, const Ty *t, Col **out, SnelErr *e);
int cmp_val(const Val *a, const Val *b);
Val op_isnil(const Val *v);
bool op_select(const Col *mask, Val t, Val e, Val *out, SnelErr *er);

// Eval (eval.c)
typedef struct Cx Cx;
// A unit loader for `use`: returns the loaded unit's tab value.
typedef struct Loader {
    Val (*load)(struct Loader *self, const Bin *name, bool *ok, char *err, size_t errlen);
    // `use x = "url"`: fetch a unit named by a URL. NULL means unsupported.
    Val (*load_url)(struct Loader *self, const Bin *name, const Bin *url, bool *ok, char *err,
                    size_t errlen);
    void *data;
} Loader;
bool module_doc(const char *src, Bin *out);
// An error span is a byte offset; these turn it into a line number for the
// formatted message. The CLI calls err_set_src once it has read the unit.
void err_set_src(const char *src);
const char *err_src(void);
unsigned err_line(uint32_t at);
uint32_t check_last_span(void); // position of the last check error (lsp.c)
const char *check_last_msg(void);
int lsp_serve(void);            // `snel lsp`: language server over stdio
bool check_unit(Node *ds, size_t nds, const Bin *toplevel, size_t ntop, const Bin *imp_names,
                const Ty *imp_tys, size_t nimp, char *errbuf, size_t errlen);
bool eval_program(Node *ds, size_t nds, Loader *loader, Val *out, char *errbuf, size_t errlen);
bool run_program(Node *ds, size_t nds, Loader *loader, Val *out, char *errbuf, size_t errlen);
bool run_closure(const Val *f, Loader *loader, Val *out, char *errbuf, size_t errlen);

// io.c
Val io_tab(void);
Val call_prim(const Bin *name, Val *args, size_t na, bool *ok, char *err, size_t errlen);
void io_set_args(int argc, char **argv);

// Builtin ops enum (must match ast::Op order used by name table)
enum {
    OP_ADD,
    OP_SUB,
    OP_MUL,
    OP_DIV,
    OP_REM,
    OP_NEG,
    OP_ABS,
    OP_ITOF,
    OP_FTOI,
    OP_SQRT,
    OP_FLOOR,
    OP_CEIL,
    OP_SIGN,
    OP_ORD,
    OP_CHR,
    OP_EQ,
    OP_NE,
    OP_LT,
    OP_LE,
    OP_GT,
    OP_GE,
    OP_AND,
    OP_OR,
    OP_NOT,
    OP_LEN,
    OP_CAT,
    OP_IOTA,
    OP_GRADE,
    OP_SUM,
    OP_PROD,
    OP_MIN,
    OP_MAX,
    OP_ISNIL,
    OP_ALL,
    OP_ANY,
    OP_REV,
    OP_TAKE,
    OP_DROP,
    OP_FIRST,
    OP_LAST,
    OP_WHICH,
    OP_DISTINCT,
    OP_IN,
    OP_MAP,
    OP_MAP2,
    OP_FOLD,
    OP_SCAN,
    OP_FILTER,
    OP_GROUP,
    OP_GET,
    OP_SELECT,
    OP_FIND,
    OP_SPLIT,
    OP_JOIN,
    OP_ENV,
    OP_REFLECT,
    OP_SHOW,
    OP_ENCODE,
    OP_DECODE,
    OP_PARSE,
    OP_UNPARSE,
    OP_AT,
    OP_REP,
    OP_SCATTER,
    OP_SHIFT,
    OP_SUMS,
    OP_PRODS,
    OP_MEMBER,
    OP_MATCHES,
    OP_RUNS,
    OP_PARTITION,
    OP_WINDOWS,
    OP_TOJSON,
    OP_FROMJSON,
    OP_TOCSV,
    OP_FROMCSV,
    OP__COUNT
};
int op_by_name(const uint8_t *b, size_t n); // -1 if not a builtin
const char *op_name(int op);

// FNV-1a 64
uint64_t fnv1a(const uint8_t *b, size_t n);

// convenience constructors
static inline Val vnil(void) {
    Val v;
    v.k = V_NIL;
    return v;
}
static inline Val vbit(bool b) {
    Val v;
    v.k = V_BIT;
    v.u.i = b;
    return v;
}
static inline Val vi64(int64_t x) {
    Val v;
    v.k = V_I64;
    v.u.i = x;
    return v;
}
static inline Val vf64(double x) {
    Val v;
    v.k = V_F64;
    v.u.f = x;
    return v;
}

#endif
