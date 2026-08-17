# Snel — language specification

> This file is mostly LLM-written and lightly human-edited, as with the code.
> For a gentler, human-written orientation, start with the [README](README.md).

Snel is a small, statically-checked, vectorized language. This document defines
its values, types, grammar, evaluation, builtins, and on-disk formats.

---

## 1. Overview

The defining choices, each expanded later:

- **Vectorized, no loops.** The only aggregate operations are bulk operations on
  whole columns. There is no user-level loop or recursion.
- **Masks are the control idiom.** A `[bit]` column selects, filters, and
  branches; `select` replaces elementwise `if`.
- **Immutable values.** No mutation operators exist. (The runtime reuses
  uniquely-owned buffers in place — functional-but-in-place, §10.2 — as an
  invisible allocation optimization.)
- **Statically checked, terminating.** A checker runs before evaluation. With no
  recursion and an application rule that rejects self-application, every program
  terminates (IO aside).
- **Homoiconic.** Code is data: one AST, one binary format, used for values and
  for programs alike.
- **One aggregate.** The *tab* (an ordered keyed map) serves as record,
  dataframe, module, environment, and AST node — one structure, not five.

---

## 2. Values

There are four value kinds; the first splits into five scalar types.

| kind | forms | notes |
|------|-------|-------|
| **scalar** | `nil`, `bit`, `i64`, `f64`, `u8` | `u8` is a byte |
| **vec** `[T]` | a flat, homogeneous column | see below |
| **tab** | ordered key→value map | unique byte-string keys |
| **fun** | a closure | params, body, captured env |

**Vectors.** A `[T]` is a flat column of `T`.

- If `T` admits `nil`, the column carries a **presence bitmap** (1 = present).
  For `T|nil` this bitmap *is* the case selector.
- A union with ≥2 non-nil cases carries a **case-selector** column plus one
  full-length, aligned payload per case.
- A **string is `[u8]`** — there is no separate string type. A column of strings
  is `[[u8]]`; vectors nest freely.

**Tabs.** An ordered map from unique byte-string keys to values. Rebinding a key
replaces its entry (right-biased: a later binding wins). One tab type does the
work of record, dataframe (a tab of equal-length vecs), environment, module, and
AST node.

**Funs.** A closure holds its parameters, body, and a captured environment
trimmed to the body's free variables — which include the *type* names its
signature and annotations mention, and, transitively, the type names those
types' own definitions mention (so a captured `type` whose base names another
`type` still resolves inside the closure). Because there is no recursion,
captured environments are acyclic.

**Representation note.** Small byte buffers and small bit vectors are stored
inline in memory (small-buffer optimization); the on-disk format is byte-packed
regardless.

---

## 3. Types

### 3.1 Type grammar

```
T := nil | bit | i64 | f64 | u8      -- scalars
   | [T]                             -- vector
   | T | T                           -- union
   | { sym: T, … }                   -- record (tab) type
   | fun(T, …) -> T                  -- function type
   | name                            -- a named type

type name = T                        -- type alias
type name = T where <fun>            -- predicate subtype; <fun> is a pure fun(T)->bit
```

- `T?` is sugar for `T | nil`.
- A `type name = T where p` defines `name` as the subtype of `T` whose values
  satisfy the predicate `p`. Statically `name ≤ T`. The predicate must not
  capture `io`.
- **`where` is optional.** `type name = T` names `T` and nothing more — the
  always-true predicate, so `name` and `T` have exactly the same values. Naming
  a record or function type this way is the usual reason to reach for `type`:
  `type Frame = { ch: [u8], line: [i64] }` then reads as a type everywhere a
  signature would otherwise spell the whole record out.
- A `type` body may name other `type`s (`type Pass = { text: Text, code: Code }`).

### 3.2 Built-in refinements over `[u8]`

| name | meaning |
|------|---------|
| `str` | a `[u8]` that is valid UTF-8 |
| `sym` | a non-empty `[u8]` of `[a-zA-Z0-9_]`, not starting with a digit |

### 3.3 The `is` test

`x is T` returns a `bit` (or `[bit]`), by one of three rules:

| operand vs `T` | behavior | result |
|----------------|----------|--------|
| any value vs a scalar case | read the selector / presence bitmap | `bit` |
| any value vs a named / `str` / `sym` refinement | run the (native) predicate | `bit` |
| a **vec** vs a *scalar* element type | test each element | `[bit]` |
| a **vec** vs a *vector* type (e.g. `str`) | test the whole value | `bit` |

Union columns support `is`, indexing, `len`, and `cat`, but **not** elementwise
arithmetic — test with `is`, narrow with `select`, then operate.

### 3.4 The static checker

The checker runs before evaluation and proves three things:

1. every name resolves to an **earlier** binding (no recursion);
2. every call is **arity-correct**;
3. every application is **type-correct**: the callee is a function and each
   argument is a structural subtype of its parameter.

Structural subtyping: records are width- and depth-covariant; functions are
contravariant in arguments and covariant in result. Rule (3) makes
self-application (`x(x)`) untypeable — the one route to non-termination that
first-class functions would otherwise open.

### 3.5 Unknown (gradual) types

Inferred types are *optional*. An **unknown** result is permissive: it satisfies
any parameter and any ascription, so the checker never produces a false
positive. Unknown is not the common case; it arises only from these sources:

1. builtins whose result shape depends on runtime data: `group`, `get`, `locals`,
   `reflect`, `decode`, `parse`;
2. an empty vector literal, or a vector/record literal with an unknown-typed
   element or field;
3. an `if`/`try` whose two branches have *incompatible* types (see §5.4) — no
   union is synthesized across branches;
4. anything downstream of the above (projection, indexing, application propagate
   unknown).

Everything else infers a precise type, including: elementwise arithmetic and
comparison (seeing through `type` aliases over a numeric base); a mixed vector
literal (element type = the union of its elements'); `map`/`fold`/`scan`/`filter`;
`select`; the reductions `sum`/`prod`/`min`/`max`; `cat`; `find`; `sums`/`prods`;
`iota`/`grade`/`which`/`len`; the reshaping ops; `split`/`join`/`show`/`encode`/
`unparse`; and the names a `use` brings in — each import is loaded and typed at
check time, so a **missing file or an import cycle is a compile error**, not a
runtime one.

### 3.6 What is checked at runtime

Exact conformance for ascriptions and parameter bindings — predicate subtypes,
refinement narrowing, union/nil normalization — is decided by the runtime
`coerce` those forms compile to, since a predicate can only run on an actual
value.

---

## 4. Grammar

### 4.1 Keywords

```
let fun type mod pub use try else err if then where do end nil is
true false and or not inf nan          -- also reserved
bit i64 f64 u8                          -- type names
```

Keywords are reserved as *terms*, but may still be used as tab keys / field
names (`io.env`, `{ first = … }`) — keys are a separate namespace.

### 4.2 Literals

| form | type | notes |
|------|------|-------|
| `123` | `i64` | decimal |
| `0xFF`, `0b1010` | `i64` | hex / binary |
| `1.5`, `1e9`, `inf`, `nan` | `f64` | a float has a `.` or an `e` |
| `true`, `false` | `bit` | |
| `:1011` | `[bit]` | bit-vector literal, index 0 first |
| `'c'`, `'\xNN'` | `u8` | char literal or hex byte |
| `"str"` | `[u8]` | string literal |
| `:sym` | `[u8]` | sugar for the string `"sym"` |
| `nil` | `nil` | |
| `[e, …]` | `[T]` | vector literal |
| `{ x = e, … }` | tab | record literal |

- **Digit separator.** `_` may appear between digits in any integer or
  bit-vector literal: `1_000_000`, `0xff_ff`, `0b1100_0000`, `:1100_1010`.
- **Escapes.** In a `"…"` string and after `\` in a `'…'` char: `\\ \" \n \t`
  and `\xNN` (a hex byte).
- `:name` is a symbol only when `name` starts with an identifier character;
  `:` directly followed by a `0`/`1` digit is a bit-vector literal instead.

### 4.3 Expressions and declarations

```
e := lit | x | e.x | e[e] | e(e, …)          -- literal, var, project, index, call
   | op-expr                                  -- operators (§4.4)
   | e |> e                                   -- pipe (§4.6)
   | fun(x: T, …) -> T = e                     -- function literal
   | if e then e else e | try e else e | err e
   | (d; …; e) | do d; …; e end                -- sequence / block (§4.5)
   | e is T | (e : T)                          -- type test / ascription

d := let x[: T] = e
   | fun f(x: T, …) -> T = e                   -- sugar for  let f = fun(…) = e
   | type n = T [where e]
   | mod …                                     -- §4.7
   | use n [= "url"]                             -- §8
   | e                                         -- a bare expression is a declaration
```

Declarations and block items are separated by `;`. **Newlines are insignificant
whitespace** — a form spans lines freely, and a `;` (not a line break) ends it.

### 4.4 Operator precedence

Tightest first; all left-associative unless noted.

| level | operators |
|------:|-----------|
| 1 (tightest) | postfix: `.x`, `e[e]`, `f(…)` |
| 2 | prefix unary: `-`, `not` |
| 3 | `* / %` |
| 4 | `+ -` |
| 5 | `= <> < <= > >=` |
| 6 | `and` |
| 7 | `or` |
| 8 | `\|>` (pipe) |
| 9 (loosest) | `is` (non-associative) |

The bodies of `fun`, `if`, `try`, and `err` extend as far right as possible.

### 4.5 Blocks (sequence expressions)

A `(d; …; e)` — or, equivalently, `do d; …; e end` — is a *sequence expression*:

- the declarations `d` bind locals scoped to the block;
- the block's value is its final expression `e`.

`(e)` is just a parenthesized expression; `(e : T)` is an ascription.

### 4.6 The pipe

`x |> f(a)` is sugar, resolved at parse time, for `f(a, x)`:

- the piped value is appended as the call's **last** argument;
- unless one or more `_` placeholders appear in the call, in which case each `_`
  is replaced by the piped value: `n |> rep(_, x)` is `rep(n, x)`;
- a bare callee pipes as a single argument: `x |> f` is `f(x)`.

Most bulk builtins take their vector last (§6), so chains read left to right:
`v |> filter(p) |> map(f) |> sum`.

### 4.7 Modules

`mod` is sugar over funs and tabs; there is no separate module system.

```
mod m { pub d1 … dn }        ≡  let m = (d1; …; dn; { pubs });
mod m(p: T) { pub d1 … dn }  ≡  let m = fun(p: T) -> { pubs } = (d1; …; dn; { pubs });
```

`{ pubs }` is the record of the module's `pub` names. In a *parametric* module,
each `pub let` must carry a type annotation (its type is read into the fun's
declared result type).

### 4.8 Comments

- A full-line `--` comment **immediately before a declaration** is a **doc
  comment**: attached to that declaration, kept in memory, printed, and
  serialized.
- Any other `--` runs to end of line and is whitespace.

### 4.9 Canonical printing

A value prints as a literal that re-reads to an equal value:

- integers and floats are grouped with `_` every 3 digits (`1_000_000`);
- a `[bit]` column prints as `:1011`, grouped every 4 bits;
- a `u8` prints as a char literal; bits print as `true`/`false`;
- a `[u8]` prints as a `"…"` string when valid UTF-8, else as a `['\xNN', …]`
  char-byte vector;
- an empty or union-typed vector carries an ascription so it re-checks
  identically;
- a closure with a captured env prints as `(let k = v; …; fun …)` — the env as a
  leading let-sequence, so it re-reads to the same closure.

---

## 5. Semantics

Big-step, `E ⊢ e ⇓ v`, where `E` is a tab. No substitution anywhere.

### 5.1 Core forms

- **`e.x`** — evaluate `e`, look up key `x` (rightmost binding wins).
- **`let x = e1; e2`** — evaluate `e1` to `v`, then evaluate `e2` under `E+{x:v}`.
- **`fun …`** — evaluate to a closure capturing the free variables of its body.
- **application** — evaluate the fun and args under `E`, then evaluate the body
  under `Ec + {params ↦ args}`, where `Ec` is the captured env (lexical scope).

### 5.2 `if` (scalar, lazy)

- The condition must be a **scalar `bit`**; only the taken branch is evaluated.
- A `[bit]` (or any non-bit) condition is a **static error** — use `select`.
- A lazy vectorized branch, when genuinely needed, is recoverable with thunks:
  `select(c, fun() = a, fun() = b)()`.

### 5.3 `select` (vectorized, eager)

`select(c, a, b)` is the eager, branchless counterpart of `if`:

- a scalar `bit` `c` picks a whole branch;
- a `[bit]` mask `c` picks elementwise (a `nil` mask bit picks `b`).

### 5.4 `try` / `else` (transactions)

`try e1 else e2` — if evaluating `e1` reaches `err e`, discard it and yield `e2`.
Because values are immutable, this is transactional **for values**; external
effects do not roll back. An `err` records a message and a source span.

### 5.5 Termination

No recursion: a binding's RHS sees only earlier bindings, and the application
rule makes self-application untypeable. With no `eval` and no fixpoint, every
program terminates (IO aside).

Builtin names (§6) are language-level and reserved (never shadowed by a
binding). A builtin is a first-class value: naming one without applying it
evaluates to a callable that routes straight to the builtin (no closure is
synthesized). So `map(sum, windows(3, v))` and `map2(add, a, b)` are point-free.

Builtins are, however, the one place the checker's *no-type-variables* design
shows through, because a builtin is **polymorphic** and so has no single type
the checker can write down (`sum` is `[i64]→i64`, `[f64]→f64`, `[bit]→i64`, …).
The checker resolves this per *application*, not as a value type:

- A direct call `sum(v)` — and a builtin passed **directly** to a higher-order
  op, `map(sum, v)` / `fold(add, 0, v)` — is typed **precisely**: the checker
  sees the builtin at the call site and computes the result from the argument
  types (and checks its arity).
- A builtin **bound to a variable** and used later — `let f = sum; map(f, v)` —
  is **gradual**: the binding would need a value type, and there isn't one, so
  the link "`f` is `sum`" is dropped. It still runs correctly (arity is checked
  at the call site), but a misuse surfaces at runtime, not at check time.

This is a deliberate ragged edge, not a general rule: a **closure** keeps its
type through a variable normally (`let g = fun(w: [i64]) -> i64 = sum(w)` gives
`g : fun([i64]) -> i64`, checked precisely wherever it flows), because a closure
is monomorphic and has exactly one type. Only polymorphic builtins-as-values are
affected — the fast, vectorized primitives are simply special.

---

## 6. Builtins

Signatures use `v` for a vector, `T` for its element type, and `?` for a
nil-admitting result.

### 6.1 Elementwise arithmetic

Broadcasting scalar↔vec, nil-propagating: `+ - * / % abs neg itof ftoi sqrt
floor ceil sign`.

- `i64` `+ - *` wrap two's-complement.
- `/ %` error on a zero divisor and on `i64_min / -1`; `%` takes the dividend's
  sign.
- `ftoi` truncates toward zero and errors outside `i64` range.
- `sqrt floor ceil` are `f64`; `sign` gives `-1 / 0 / 1`.

### 6.2 Comparison and boolean

`= <> < <= > >=` are **total**, return `bit`, and lift elementwise. One order per
type:

| type | order |
|------|-------|
| `bit` | `0 < 1` |
| `i64` | signed |
| `u8` | unsigned |
| `f64` | IEEE totalOrder: `-0.0 < 0.0`; `=` is order-equality; NaN canonicalized at construction and greatest |
| vec | lexicographic by element (so whole strings sort and group) |
| `nil` | least within its column |

Cross-kind comparison happens only inside union columns, by the fixed rank
`bit < i64 < f64 < u8 < vec < tab`. `and or not` operate on bit / bitmaps.

> On two `[u8]`, `"a" < "b"` compares **byte-wise** (returning `[bit]`);
> whole-string order is what `grade` / `group` / `min` use.

### 6.3 Reductions and scans

| builtin | meaning |
|---------|---------|
| `sum(v)` `prod(v)` `min(v)` `max(v)` | reduce a column to a scalar |
| `all(v)` `any(v)` | reduce a mask to a `bit` |
| `sums(v)` `prods(v)` | prefix (cumulative) scans, same length |

Examples: `sums([1,2,3]) = [1,3,6]`;
`prods(cat([1], rep(4, 10))) = [1,10,100,1_000,10_000]`.

### 6.4 Structure and reshaping

These take the vector **last**, so they chain through the pipe.

| builtin | meaning |
|---------|---------|
| `len(v)` | length |
| `cat(a, b)` | concatenate two vectors |
| `rev(v)` | reverse |
| `distinct(v)` | dedupe, first-appearance order |
| `take(n, v)` `drop(n, v)` | first / past-first `n`, clamped to length |
| `first(v)` `last(v)` | ends |
| `at(i, v)` | element at scalar index `i` (scalar gather) |
| `shift(k, fill, v)` | slide `k` places, filling past the ends (positive `k` looks right, negative left) |
| `which(mask)` | the set indices, e.g. `which(:101) = [0,2]` |
| `in(x, v)` | membership → `bit` |
| `isnil(v)` | presence test |
| `rep(n, x)` | `n` copies of a scalar |
| `iota(n)` | `[0, 1, …, n-1]` |

### 6.5 Ordering and grouping

| builtin | meaning |
|---------|---------|
| `grade(v)` | stable ascending permutation; sort is `v[grade(v)]` |
| `group(t, :k)` | `{ k = keys, rows = [tab] }`; keys in first-appearance order, rows in source order |
| `get(t, key)` | tab lookup by a runtime key → `v?` (`nil` if absent) |

### 6.6 Indexing and scatter

- **Gather:** `v[ivec]`, `v[mask]` (mask length = `len(v)`); `t[ivec]`,
  `t[mask]` select rows (all fields must be equal-length vecs).
- **Scatter** (the inverse): `scatter(ivec, vals, base)` yields `base` with
  `base[ivec[k]] := vals[k]`. Later writes win; `vals` may be a scalar,
  broadcast to every index.
- A **`type` name** indexes as whatever it names (including `str` / `sym`, which
  index as `[u8]`). The result has the *base* type, not the name: indexing need
  not preserve a refinement, since a slice of a `str` need not be UTF-8.

Counting is `sum(mask)` — bits lift to `i64` under arithmetic. No operation
observes any internal hash order.

### 6.7 Higher-order

| builtin | meaning |
|---------|---------|
| `map(f, v)` | map `f` over `v` |
| `map2(f, a, b)` | zip two vectors with `f` |
| `filter(f, v)` | keep elements where `f` holds |
| `fold(f, z, v)` | left fold from `z` |
| `scan(f, z, v)` | fold keeping each intermediate |

### 6.8 Strings

Strings are `[u8]`, so `len` / `cat` / indexing / `grade` need no
string-specific forms. Three remain:

| builtin | meaning |
|---------|---------|
| `find(needle, hay)` | byte offset of `needle` in `hay`, or `nil` |
| `split(sep, s)` | split `s` on `sep` → `[[u8]]` |
| `join(sep, [[u8]])` | join with `sep` → `[u8]` |

### 6.9 Reflection and (de)serialization

All read-only over data — no evaluation, so nothing reopens termination.

| builtin | meaning |
|---------|---------|
| `locals()` | the current environment as a tab |
| `reflect(f)` | a closure as `{ params, ret, body, env }` |
| `show(v)` | canonical text `[u8]` |
| `encode(v)` `decode(b)` | the binary format (§10) |
| `parse(src)` | source → a vector of declaration AST-tabs |
| `unparse(ast)` | an AST-tab (or vector of them) → source |

So `unparse(decode(encode(parse(src))))` round-trips source through binary — what
`snel bin` does, expressed in the language.

### 6.10 Sequence analysis

Composable building blocks for sequence and pattern work. Each returns a mask
(combine with `which`/`sum`/`and`/`or`/`not`) or a `[[T]]` (combine with `map`),
and works on any element type. `member` is the elementwise companion of the
scalar `in`.

| builtin | result | meaning |
|---------|--------|---------|
| `member(set, v)` | `[bit]` | is each `v[i]` an element of `set`? (find-all-in-class) |
| `matches(needle, hay)` | `[bit]` | every index where `needle` occurs as a contiguous subsequence — the all-positions `find` (an empty needle matches everywhere) |
| `runs(v)` | `[bit]` | run-start boundaries: index 0, and each `i` where `v[i] ≠ v[i-1]` |
| `partition(starts, v)` | `[[T]]` | cut `v` into segments beginning at index 0 and at each set bit of `starts` (lossless — the segments re-concatenate to `v`) |
| `windows(k, v)` | `[[T]]` | all overlapping length-`k` sub-vectors, `len(v)-k+1` of them (`k ≥ 1`) |

Idioms: run-length encoding is `partition(runs(v), v)` then `map` of
`first`/`len`; a moving statistic is `map(f, windows(k, v))`; classification and
pattern location produce masks you combine and feed to `which`. See
`examples/sequences.sn`.

### 6.11 Interop: JSON and CSV

| builtin | result | meaning |
|---------|--------|---------|
| `tojson(v)` | `[u8]` | JSON text for any value except a function |
| `fromjson(s)` | value | parse JSON text |
| `tocsv(t)` | `[u8]` | CSV text for a *flat* table |
| `fromcsv(s)` | tab | parse CSV text into a flat table |

JSON maps both ways: `nil`↔`null`, `bit`↔`true`/`false`, numbers, `[u8]`↔string,
`[T]`↔array, tab↔object. A function has no JSON form (an error), and neither do
`inf`/`nan`. Reading a number gives `i64` when it is integral and fits, else
`f64`; `\uXXXX` decodes to UTF-8 (a lone surrogate becomes U+FFFD); a mixed
array reads as a union column, exactly like the equivalent vector literal.

CSV is deliberately **partial**, because CSV cannot nest: `tocsv` accepts only a
tab whose fields are equal-length vectors of scalars (or strings), and `fromcsv`
returns such a tab, taking the first record as the header. Quoting is
RFC4180-style (`""` escapes a quote). An empty cell reads as `nil` in a numeric
column; a column's type is inferred all-integer → `[i64]`, all-numeric →
`[f64]`, else `[[u8]]`.

---

## 7. io

Every unit evaluates **pure** — nothing has ambient `io`. Effects enter through
one door: a unit may export `fun main(io) …`, which `snel run` calls with the io
capability. The same unit is therefore a library when `use`d and an app when
run. Any code that wants a capability takes it as a parameter, and `main`
annotates only the io fields it uses (least privilege via width subtyping).

`io` is a tab of first-class `Prim` values; all take and return strings (`[u8]`)
unless noted.

| primitive | effect |
|-----------|--------|
| `io.read(path)` | file contents |
| `io.write(path, bytes)` | write a file |
| `io.args() -> [[u8]]` | command-line arguments |
| `io.locals()` | the process environment as a tab |
| `io.exe() -> [u8]` | path of the running interpreter (so a program can spawn itself) |
| `io.spawn(prog, argv, stdin, envs) -> stdout` | run a subprocess; each env is `"KEY=VALUE"` |
| `io.list(dir) -> [[u8]]` | directory entries |
| `io.stat(path) -> {size, mtime, isdir}` | file metadata |
| `io.exists(path) -> bit` | existence |
| `io.mkdir/rmdir/unlink(path)` | filesystem mutation |
| `io.rename/link(from, to)` | filesystem mutation |
| `io.time() -> i64` | milliseconds since the epoch |
| `io.sleep(ms)` | delay |

Because `io` is an ordinary value, a caller can pass a **mock** `io` to mediate
what the code it calls may do. `io.exe` + `io.spawn` + `encode`/`decode` give a
bounded, isolated `eval`: run a closure in a child interpreter and read the
result back through the binary format (see `examples/subeval.sn`). `try`/`else`
rolls back values, not external effects.

---

## 8. Units, imports, caching

- **`foo.sn`** — a list of declarations; it evaluates to a tab of its `pub`
  names.
- **`use foo`** — binds that tab, loading and evaluating `foo.sn` on first demand
  and caching the result for the run. An import is loaded and type-checked at
  **check time**, so a missing file or an import cycle is a compile error.
- **`foo.sni`** — a generated interface: a source hash on line 1, then the
  module doc (if any), then the pub names, their types, and their doc comments.
  It is printed by the interpreter from a checked `.sn`, in the same syntax the
  parser reads. The hash is FNV-1a 64 over the source bytes.

### 8.1 Module doc comments

A `--` block at the very top of a unit, separated from the first declaration by
a **blank line**, is the unit's module doc. A leading block with *no* blank line
after it is the first declaration's own doc, as usual.

```
-- What this module is for.
-- A second line of module doc.

-- documents `f`
pub fun f(x: i64) -> i64 = x;
```

### 8.2 Remote units (optional)

`use x = "url"` names a unit to fetch rather than a local `x.sn`. It is
deliberately restricted:

- **Off by default at runtime.** The CLI must be passed `--remote`;
  `--no-remote` forces it off. Without it, a URL import is a compile error.
- **Schemes.** `file:` and `http(s):` are supported; anything else is an error.
  HTTP(S) fetches run the system `curl` (via fork/exec, so no shell quoting is
  involved) rather than linking a TLS stack into the interpreter.
- **Caching.** A fetched unit is evaluated and cached under its name for the
  run, exactly like a local one, and participates in the same cycle detection.
- **Subprocess eval.** The capability is explicit there too: a child spawned by
  `subeval` gets no network unless the parent passes `--remote` (see
  `subeval_remote` in `examples/subeval.sn`).
- **Both implementations** support this; there is no build-time switch, only the
  runtime `--remote` flag.

---

## 9. Code as data

There is one internal AST, with a fixed bijection to canonical tabs that serves
printing, serialization, and reflection. Each node has a kind field `n`; field
order is fixed; declaration nodes take an optional `doc`.

```
{n='lit,  v}                {n='var,  x}               {n='proj, e, x}
{n='idx,  e, i}             {n='app,  f, a=[…]}        {n='vec,  e=[…]}
{n='tab,  k=[…], e=[…]}     {n='fun,  p=[…], t, e}     {n='if,   c, t, e}
{n='try,  e1, e2}           {n='err,  e}               {n='is,   e, t}
{n='as,   e, t}             {n='seq,  d=[…]}
{n='let,  x, t?, e, doc?, pub?}  {n='type, x, t, p, doc?, pub?}  {n='use, x, doc?}
```

- `mod` desugars before encoding; operators encode as `app` of builtin names.
- Node kinds, names, and type names are `[u8]` strings — the AST is entirely
  data.
- Types encode as values: prims and named types as strings; compounds as tagged
  tabs — `[T]` as `{n='vec_t, e}`, unions as `{n='union_t, e=[…]}`, tab types as
  `{n='rec_t, k=[…], t=[…]}`, fun types as `{n='fun_t, a=[…], r}`.

---

## 10. Representation, round-trip, and functional-but-in-place

### 10.1 Round-trip

`memory ↔ text ↔ binary` round-trips losslessly, doc comments included.

### 10.2 Storage and in-place reuse (FBIP)

Columns are flat, contiguous buffers behind reference counts; leaves are whole
columns (no interior pointers to amortize).

The language is purely functional: values are immutable and there is **no
user-level mutation**. Every operation produces a logically new value. Reference
counting lets the runtime realize that model **functional-but-in-place** (FBIP) —
reusing storage without ever exposing mutation:

- **Sharing.** Binding, capturing, and indexing share a column's buffer rather
  than copying it.
- **In-place reuse.** An operation that would allocate a fresh result may instead
  overwrite its input's buffer *when that input is uniquely owned* (refcount 1) —
  such a buffer is about to be dropped, so reusing it to hold the new value is
  safe and unobservable. When the buffer is shared (refcount > 1), the operation
  copies it first, then writes. Purely an allocation optimization; it changes no
  observable behavior.

This is not classic copy-on-write (which shares *mutable* state and copies to
preserve isolation) — nothing here is mutable to a user; the "write" only ever
lands in a buffer that is provably about to be freed. The reuse decision is made
**dynamically** (a refcount check at the operation), not by the static
[Perceus](https://www.microsoft.com/en-us/research/publication/perceus-garbage-free-reference-counting-with-reuse/)-style
reuse analysis that FBIP languages like Koka and Lean use to place reuse tokens
at compile time; Snel does no such analysis.

### 10.3 f64 text form

The fewest significant digits (1–17) whose correctly-rounded decimal reparses to
identical bits. Normalized `d.ddd`, exponent `e±N` (no leading zeros) when the
decimal exponent is `< -4` or `≥ 17`; integral values keep a `.0`; the special
spellings are `inf`, `-inf`, `nan`.

---

## 11. Binary format

One tagged format for everything.

- **Fixed-width columns** (bit, i64, f64, bitmaps, selectors) are written in
  256-element chunks, each with a 1-byte encoding tag: `raw | rle | nullsup`.
  The encoder picks the smallest.
- **bin / tab columns** are tagged sequences.
- **Closures** are params + body + trimmed env.

---

## 12. Implementations

Two implementations, observably identical — same text output, binary bytes, and
errors:

- **Rust** (primary) and **C99**, no dependencies — including the language
  server (which reuses the language's own JSON codec) and remote units (which
  shell out to the system `curl`).
- A **differential fuzzer** generates random programs — type-directed and
  scope-aware, covering the whole grammar and every builtin — runs both
  implementations, and diffs `run`, `bin`, `fmt`, and `sni`
  (`tools/difftest.sh`). `tools/lspdiff.sh` does the same for the language
  server, where diagnostic *positions* are compared rather than canonicalized.
- The same generator drives a **coverage-guided** libfuzzer target (`fuzz/`),
  which mutates raw bytes into programs and asserts the round-trip laws of
  §10.1 rather than comparing implementations. `tools/coverage.sh` reports how
  much of the interpreter a corpus reaches.
- Both check statically and then evaluate; the REPL does so per form.
- Modules, per implementation: `value`, `lex`, `parse`, `check`, `eval`, `bin`,
  `io`, `interop`, `main` (plus Rust-only `lsp`).
- **`snel lsp`** — a language server over stdio, in both twins, byte-identical
  in its protocol output. It parses and checks but never evaluates, so an
  editor never runs a user's effects.
- **Editor support** for vim, emacs, and VS Code lives in `editors/`.
