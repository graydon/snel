// End-to-end tests: evaluation results, and the three-way round trip
// memory <-> text <-> binary required by the spec.

use snel::eval::NoLoader;
use snel::{eval_unit, parse, print};

fn eval(src: &str) -> String {
    let mut l = NoLoader;
    match eval_unit(&mut l, src) {
        Ok(v) => print::fmt_val(&v),
        Err(e) => format!("ERR: {}", e),
    }
}

// Evaluate `let it = <expr>` and return the printed value of `it`.
fn expr(e: &str) -> String {
    let mut l = NoLoader;
    let src = format!("pub let it = {}", e);
    match eval_unit(&mut l, &src) {
        Ok(snel::value::Val::Tab(t)) => print::fmt_val(t.get(b"it").unwrap()),
        Ok(v) => print::fmt_val(&v),
        Err(e) => format!("ERR: {}", e),
    }
}

#[test]
fn arithmetic_and_broadcast() {
    assert_eq!(expr("2 + 3 * 4"), "14");
    assert_eq!(expr("1.5 / 0.5"), "3.0");
    assert_eq!(expr("[1,2,3] * 2"), "[2, 4, 6]");
    assert_eq!(expr("[1,2,3] + [10,20,30]"), "[11, 22, 33]");
    assert_eq!(expr("10 % 3"), "1");
    assert_eq!(expr("-5"), "-5");
}

#[test]
fn nil_and_masks() {
    assert_eq!(expr("[3,1,nil,7,5] > 2"), ":1001_1");
    assert_eq!(expr("[3,1,nil,7,5][[3,1,nil,7,5] > 2]"), "[3, 7, 5]");
    assert_eq!(expr("iota(5)[[3,1,nil,7,5] > 2]"), "[0, 3, 4]");
    assert_eq!(expr("[1,nil,3] + [10,20,30]"), "[11, nil, 33]");
    assert_eq!(expr("isnil([1,nil,3])"), ":010");
    assert_eq!(expr("sum([3,1,nil,7,5] > 2)"), "3");
}

#[test]
fn comparisons_total_order() {
    assert_eq!(expr("nan = nan"), "true"); // canonical NaN, order-equality
    assert_eq!(expr("0.0 = -0.0"), "false"); // totalOrder distinguishes signed zero
    assert_eq!(expr("nil < 1"), "true"); // nil least
    // strings are [u8], so `<` compares byte-wise (elementwise)
    assert_eq!(expr("\"abc\" < \"abd\""), ":001");
    // whole-string lexicographic order shows up in grade/sort of a column
    assert_eq!(expr("[\"b\", \"a\", \"c\"][grade([\"b\", \"a\", \"c\"])]"), "[\"a\", \"b\", \"c\"]");
}

#[test]
fn scalar_if_and_vector_select() {
    // `if` is a scalar, lazy conditional; a [bit] mask is a type error there
    assert_eq!(expr("if true then 10 else 20"), "10");
    assert!(expr("if [true,false,true] then [1,2,3] else 0").starts_with("ERR"));
    // elementwise choice is `select`, on a scalar bit or a [bit] mask
    assert_eq!(expr("select([true,false,true], [1,2,3], 0)"), "[1, 0, 3]");
    assert_eq!(expr("select(3 > 2, 10, 20)"), "10");
}

#[test]
fn functions_fold_map() {
    assert_eq!(
        eval("fun dbl(x: i64) -> i64 = x * 2; pub let r = dbl(21)"),
        "{ r = 42 }"
    );
    assert_eq!(
        expr("fold(fun(a: i64, x: i64) -> i64 = a + x, 0, [1,2,3,4])"),
        "10"
    );
    assert_eq!(expr("map(fun(x: i64) -> i64 = x * x, [1,2,3])"), "[1, 4, 9]");
}

#[test]
fn tables_and_group() {
    let t = "let t = { name = [\"a\",\"b\",\"c\"], age = [30, 41, 30] }; ";
    assert_eq!(eval(&format!("{}pub let r = t.age", t)), "{ r = [30, 41, 30] }");
    assert_eq!(
        eval(&format!("{}pub let r = t[t.age > 35]", t)),
        "{ r = { name = [\"b\"], age = [41] } }"
    );
    // group keeps first-appearance order
    let g = eval(&format!("{}pub let r = group(t, :age)", t));
    assert!(g.contains("age = [30, 41]"), "{}", g);
}

#[test]
fn predicate_subtypes() {
    let s = "typ pos = i64 where fun(x: i64) -> bit = x > 0; ";
    assert_eq!(eval(&format!("{}pub let r = 5 is pos", s)), "{ r = true }");
    assert_eq!(eval(&format!("{}pub let r = 0 is pos", s)), "{ r = false }");
    // ascription failure is an error
    assert!(eval(&format!("{}pub let r: pos = -3", s)).starts_with("ERR"));
}

#[test]
fn static_type_errors() {
    // The checker rejects these before evaluation. Self-application is the
    // important one: it is what keeps evaluation terminating.
    let bad = [
        "let g = fun(x: fun(nil)->nil)->nil = x(x)", // self-application
        "pub let r = 5(3)",                          // call a non-function
        "fun f(x: i64) -> i64 = x; pub let r = f(1, 2)", // arity
        "fun f(x: i64) -> i64 = x; pub let r = f(\"hi\")", // argument type
        "let t = { a = 1 }; pub let r = t.b",        // missing field
        "pub let r = zzz",                           // unbound name
        "pub let r = len(1, 2)",                     // builtin arity
        "let x: foo = 1",                            // unknown type
        "fun f(x: i64) -> f64 = x + 1",              // body i64 vs return f64
        "fun f(v: [i64]) -> [i64] = v > 2",          // compare yields [bit], not [i64]
    ];
    for src in bad {
        assert!(eval(src).contains("check error"), "expected a check error for: {src}");
    }
}

#[test]
fn elementwise_typing() {
    // Arithmetic is typed through broadcast and nil-propagation; comparison
    // yields bit/[bit]. These type precisely and run.
    assert_eq!(eval("fun f(v: [i64?]) -> [i64?] = v + 1; pub let r = f([3,nil,5])"), "{ r = [4, nil, 6] }");
    assert_eq!(eval("fun f(v: [i64?]) -> [bit] = v > 2; pub let r = f([3,1,nil])"), "{ r = :100 }");
    // A genuine multi-case union operand stays gradual (no false rejection);
    // comparison on it is allowed and runs, arithmetic is left to runtime.
    assert_eq!(eval("typ num = i64|f64; let m: [num] = [1, 2.5]; pub let r = m > 0"), "{ r = :11 }");
}

#[test]
fn valid_application_checks() {
    assert_eq!(expr("(fun(x: i64) -> i64 = x + 1)(41)"), "42");
}

#[test]
fn builtins_are_first_class() {
    // a bare builtin is a value that routes directly to the builtin when called
    assert_eq!(expr("map(sum, windows(3, [1, 2, 3, 4, 5]))"), "[6, 9, 12]");
    assert_eq!(expr("map2(add, [1, 2], [10, 20])"), "[11, 22]");
    assert_eq!(expr("show(first)"), "\"first\""); // prints as its bare name
    // arity is enforced at the first-class call site (checker can't, it's gradual)
    assert!(expr("map(add, [1, 2, 3])").starts_with("ERR")); // add needs 2 args
}

#[test]
fn ord_chr() {
    assert_eq!(expr("ord(\'A\')"), "65");
    assert_eq!(expr("chr(97)"), "'a'");
    assert_eq!(expr("ord([\'a\', \'b\', \'c\'])"), "[97, 98, 99]");
    assert_eq!(expr(r#"all(chr(ord("snel")) = "snel")"#), "true");
}

#[test]
fn new_builtins() {
    assert_eq!(expr("rev([1,2,3])"), "[3, 2, 1]");
    assert_eq!(expr("take(2, [1,2,3,4])"), "[1, 2]");
    assert_eq!(expr("drop(2, [1,2,3,4])"), "[3, 4]");
    assert_eq!(expr("first([9,8,7])"), "9");
    assert_eq!(expr("last([9,8,7])"), "7");
    assert_eq!(expr("distinct([1,1,2,3,2])"), "[1, 2, 3]");
    assert_eq!(expr("which([true,false,true,true])"), "[0, 2, 3]");
    assert_eq!(expr("prod([1,2,3,4])"), "24");
    assert_eq!(expr("all([true,true])"), "true");
    assert_eq!(expr("any([false,false])"), "false");
    assert_eq!(expr("in(2, [1,2,3])"), "true");
    assert_eq!(expr("scan(fun(a: i64, x: i64) -> i64 = a + x, 0, [1,2,3])"), "[1, 3, 6]");
    assert_eq!(expr("map2(fun(a: i64, b: i64) -> i64 = a + b, [1,2], [10,20])"), "[11, 22]");
    assert_eq!(expr("filter(fun(x: i64) -> bit = x > 1, [1,2,3])"), "[2, 3]");
    assert_eq!(expr("floor(3.7)"), "3.0");
    assert_eq!(expr("sign(-5)"), "-1");
}

#[test]
fn serialization_builtins() {
    // value -> binary -> value round-trips (compared via canonical text)
    assert_eq!(expr("all(show(decode(encode([1,2,3]))) = show([1,2,3]))"), "true");
    // source -> AST -> source
    assert_eq!(expr(r#"unparse(parse("let x = 2 + 3"))"#), r#""let x = 2 + 3;\n""#);
    // source -> AST -> binary -> AST -> source (the self-serializer, in Snel)
    assert_eq!(expr(r#"unparse(decode(encode(parse("let x = 2 + 3"))))"#), r#""let x = 2 + 3;\n""#);
}

#[test]
fn closure_captures_print_and_reread() {
    // A closure over a captured binding prints as a let-sequence that re-reads
    // to an identical closure — the lossless text form, with no `with`.
    let printed = expr("(let b = 10; fun(x: i64) -> i64 = x + b)");
    assert!(printed.contains("let b = 10"), "got: {printed}");
    assert_eq!(expr(&printed), printed); // idempotent through text
}

#[test]
fn try_else_transaction() {
    assert_eq!(expr("try 1 / 0 else -1"), "-1");
    assert_eq!(
        eval("fun chk(x: i64) -> i64 = if x < 0 then err \"neg\" else x; pub let r = try chk(-4) else 0"),
        "{ r = 0 }"
    );
}

#[test]
fn no_recursion_is_rejected() {
    // f references itself: unbound at its own RHS
    assert!(eval("fun f(x: i64) -> i64 = f(x)").starts_with("ERR"));
}

#[test]
fn review_regressions() {
    // nil broadcasts against f64 vecs (was: type error)
    assert_eq!(expr("nil + [1.5, 2.5]"), "[nil, nil]");
    // sum/if reject union columns instead of reading dummy slots
    assert_eq!(expr("try sum(([true, 5] : [bit|i64])) else 999"), "999");
    assert_eq!(
        expr("try select(([true, 5] : [bit|i64]), [10, 20], [30, 40]) else [999, 999]"),
        "[999, 999]"
    );
    // i64::MIN round-trips through text
    assert_eq!(expr("-9223372036854775808"), "-9_223_372_036_854_775_808");
    // deep union-member coercion: [i64]? still checks elements
    assert!(expr("([true] : [i64]?)").starts_with("ERR"));
    // broadcast against a fun scalar errors rather than panicking
    assert!(expr("[1,2] + fun(x: i64) -> i64 = x").starts_with("ERR"));
}

#[test]
fn u8_and_string_literals() {
    assert_eq!(expr("\'A\'"), "'A'"); // ascii char literal -> u8
    assert_eq!(expr("0xff"), "255"); // hex byte literal
    assert_eq!(expr("\"hello\""), "\"hello\""); // string is a [u8]
    assert_eq!(expr(":label"), "\"label\""); // 'name is sugar for a string
    assert_eq!(expr("[\'a\', \'b\', \'c\']"), "\"abc\""); // a [u8] of chars renders as a string
    assert_eq!(expr("['\\xde', '\\xad', '\\xbe']"), "['\\xde', '\\xad', '\\xbe']"); // non-utf8 -> hex
    assert_eq!(expr("[\"a\", \"bb\", \"c\"]"), "[\"a\", \"bb\", \"c\"]"); // [[u8]] column of strings
}

#[test]
fn str_sym_refinement_types() {
    // str = [u8] valid utf8; sym = [u8] identifier — whole-value tests
    assert_eq!(expr("\"hello\" is str"), "true");
    assert_eq!(expr(":foo is sym"), "true");
    assert_eq!(expr("\"a b\" is sym"), "false"); // space is not a sym char
    assert_eq!(expr("5 is str"), "false");
    // usable in ascription
    assert_eq!(eval("pub let s: str = \"ok\""), "{ s = \"ok\" }");
    assert!(eval("pub let s: sym = \"a b\"").starts_with("ERR"));
}

#[test]
fn named_types_compose_and_index() {
    // A `typ` body may name another `typ`. The inner name has to reach the
    // *closure* that coerces against the outer one, so it rides along in the
    // captured env (was: eval error "unbound type `Inner`").
    // (`where` is optional — a bare `typ` is a plain alias)
    let nested = "typ Inner = { a: [i64] };\
                  typ Outer = { i: Inner, n: i64 };\
                  fun mk() -> Outer = { i = { a = [1] }, n = 0 };";
    assert_eq!(eval(&format!("{nested} pub let v = mk()")), "{ v = { i = { a = [1] }, n = 0 } }");
    // ...including when the closure is reached indirectly, through a builtin
    assert_eq!(
        eval(&format!(
            "{nested} fun bump(o: Outer, k: i64) -> Outer = {{ i = o.i, n = o.n + k }};\
             pub let v = fold(bump, mk(), [1, 2])"
        )),
        "{ v = { i = { a = [1] }, n = 3 } }"
    );

    // `e[i]` sees through a `typ` alias, the way `e.x` always has. The result is
    // the *base* type, since indexing need not preserve the refinement.
    assert_eq!(
        eval("typ Frame = { ch: [u8], ln: [i64] };\
              fun keep(f: Frame, m: [bit]) -> Frame = f[m];\
              pub let v = keep({ ch = \"abcd\", ln = [0, 0, 1, 1] }, \"abcd\" <> 'b')"),
        "{ v = { ch = \"acd\", ln = [0, 1, 1] } }"
    );
    assert_eq!(
        eval("typ Nums = [i64]; fun pick(v: Nums, ix: [i64]) -> [i64] = v[ix];\
              pub let v = pick([9, 8, 7], [2, 0])"),
        "{ v = [7, 9] }"
    );
    // an alias names a type and nothing else: same values, and `is` always holds
    assert_eq!(eval("typ N = i64; pub let a = 5 is N"), "{ a = true }");
    // ...and it prints back as an alias, not as the predicate it desugars to
    assert_eq!(parse_print("typ N = i64;"), "typ N = i64;\n");
    assert_eq!(parse_print("typ R = { a: [i64] };"), "typ R = {a: [i64]};\n");
    assert_eq!(
        parse_print("typ pos = i64 where fun(x: i64) -> bit = x > 0;"),
        "typ pos = i64 where fun(x: i64) -> bit = x > 0;\n"
    );
    assert_eq!(eval("typ N = i64; pub let a = (5 : N)"), "{ a = 5 }");
    assert_eq!(eval("typ F = fun(i64) -> i64; fun ap(f: F, x: i64) -> i64 = f(x);\
                     pub let a = ap(fun(z: i64) -> i64 = z + 1, 41)"), "{ a = 42 }");
    // the built-in refinements index too
    assert_eq!(eval("fun two(s: str) -> [u8] = s[[0, 1]]; pub let v = two(\"hello\")"), "{ v = \"he\" }");
    // and a non-indexable type is still rejected
    assert!(eval("typ N = i64; fun bad(x: N) -> i64 = x[0]; pub let v = bad(3)")
        .starts_with("ERR"));
}

// Divergences the differential fuzzer turned up between the Rust and C twins.
// Each is pinned here on the Rust side; tools/difftest.sh is what checks the
// two implementations still agree.
#[test]
fn fuzzer_found_regressions() {
    // `and`/`or` take bit / [bit]; a scalar bit broadcasts, anything else is an
    // error. (C read the operand's union payload as an integer regardless of
    // kind, so a tab or an f64 silently became "true".)
    for bad in ["{ k = [1] }", "1.5", "\"ab\"", "[1, 2]", "nil"] {
        assert!(expr(&format!("or({bad}, :01)")).starts_with("ERR"), "or({bad}, :01)");
        assert!(expr(&format!("and(:01, {bad})")).starts_with("ERR"), "and(:01, {bad})");
    }
    assert_eq!(expr("or(true, :01)"), ":11"); // a scalar bit still broadcasts
    assert_eq!(expr("and(:110, false)"), ":000");

    // `find` is a string op: a non-[u8] operand is an error, not a miss. (C
    // returned nil, so `isnil(find(...))` answered "not found" for something
    // that was never searchable.)
    assert!(expr("find(\"abc\", [22, 1668])").starts_with("ERR"));
    assert!(expr("find([2], [1, 2, 3])").starts_with("ERR"));
    assert_eq!(expr("find(\"b\", \"abc\")"), "1");
    assert_eq!(expr("isnil(find(\"z\", \"abc\"))"), "true");

    // A union column's cases each carry a full-length payload, but only the rows
    // the selector points at are real. The printed ascription must not describe
    // a case that owns no row — its contents are filler, and the twins disagreed
    // on what that filler was.
    assert_eq!(expr("cat([([] : [i64])], [\"\"])"), "([([] : [i64]), \"\"] : [[i64]])");
    assert_eq!(expr("cat([\"\"], [[1]])"), "([\"\", [1]] : [[u8]])");
    // ...while cases that *do* own rows are still all reported
    assert_eq!(expr("cat([1], [2.5])"), "([1, 2.5] : [i64|f64])");
    assert_eq!(expr("cat([{a=1}], [\"\"])"), "([{ a = 1 }, \"\"] : [{a: i64}|[u8]])");
    assert_eq!(expr("([true, 5] : [bit|i64])"), "([true, 5] : [bit|i64])");

    // The parser folds `-` over a numeric literal into the literal, so printing
    // `neg(lit)` in prefix form does not re-read as the same node: `-0` and
    // `-nan` fold away, and `--1` does not lex. Over a literal, print the call
    // form; everywhere else the prefix form is exact.
    for src in ["neg(0)", "neg(1)", "neg(nan)", "neg(inf)", "neg(-inf)", "neg(-1)",
                "neg(neg(2))", "neg(neg(nan))", "neg(-0.0)", "neg(abs(3))", "-1", "-0.0",
                "neg(neg(abs(3)))", "neg(neg(neg(abs(3))))", "neg(\"\\xff\\xfe\")",
                "neg([1, 2])", "neg(1_000)"] {
        let once = parse_print(&format!("pub let a = {src};"));
        assert_eq!(once, parse_print(&once), "printing {src} is not idempotent");
    }
    assert_eq!(parse_print("pub let a = neg(0);"), "pub let a = neg(0);\n");
    // a rendered *vector* literal does not absorb the sign, so it keeps the prefix
    assert_eq!(parse_print("pub let a = neg([1, 2]);"), "pub let a = -[1, 2];\n");
    // ...and a negative literal binds like the prefix operator, so a postfix
    // after it needs parens: `-1[i]` would re-read as `neg(1[i])`.
    for src in ["(-0.0)[iota(0)]", "(-1)[iota(0)]", "[1, 2][-1]"] {
        let once = parse_print(&format!("pub let a = {src};"));
        assert_eq!(once, parse_print(&once), "printing {src} is not idempotent");
    }
    assert_eq!(parse_print("pub let a = (-1)[iota(0)];"), "pub let a = (-1)[iota(0)];\n");

    // `tojson` writes bytes, not re-encoded code points: the UTF-8 of a string
    // has to survive unchanged. (Pushing each byte into a String as a `char`
    // turned "café" into "cafÃ©".)
    assert_eq!(expr("tojson(\"café\")"), "\"\\\"café\\\"\"");
    assert_eq!(expr("fromjson(tojson(\"café\"))"), "\"café\"");
    assert_eq!(expr("tojson([\"é\", \"日本\"])"), "\"[\\\"é\\\",\\\"日本\\\"]\"");
    assert_eq!(expr("fromjson(tojson({ a = \"é\" }))"), "{ a = \"é\" }");

    // Truncated source must be a parse *error*, not a panic. The parser used to
    // index past the end of the token stream once it ran off it, which the
    // `parse` builtin made reachable at runtime from any string.
    for bad in ["[nil", "[1", "[", "(", "{", "let x = [1", "[1,", "fun f(x: i64) -> ",
                "try 1 else", "if true then 1", "{ a =", "(1 :", "mod m {",
                "typ T = i64 where"] {
        assert!(parse::parse_unit(bad).is_err(), "expected a parse error for {bad:?}");
        let quoted = bad.replace('\\', "\\\\").replace('"', "\\\"");
        assert_eq!(expr(&format!("try unparse(parse(\"{quoted}\")) else \"ERR\"")), "\"ERR\"");
    }
    // a `-` written in source is folded at parse time, so it still prints bare
    assert_eq!(parse_print("pub let a = -1;"), "pub let a = -1;\n");
    // ...and over a non-literal the prefix form is kept
    assert_eq!(parse_print("pub let a = neg(abs(3));"), "pub let a = -abs(3);\n");
}

#[test]
fn string_ops() {
    // strings are [u8], so the vector ops just work
    assert_eq!(expr("len(\"h\\xc3\\xa9llo\")"), "6"); // byte length, not chars
    assert_eq!(expr("cat(\"foo\", \"bar\")"), "\"foobar\"");
    assert_eq!(expr("\"hello\"[[0, 1, 4]]"), "\"heo\""); // byte index
    assert_eq!(expr("\"hello\"[\"hello\" > 'n']"), "\"o\""); // byte filter
    // string-specific builtins
    assert_eq!(expr("find(\"world\", \"hello world\")"), "6");
    assert_eq!(expr("find(\"z\", \"abc\")"), "nil");
    assert_eq!(expr("split(\",\", \"a,b,,c\")"), "[\"a\", \"b\", \"\", \"c\"]");
    assert_eq!(expr("join(\"-\", [\"x\", \"y\", \"z\"])"), "\"x-y-z\"");
    // whole-string ordering via grade/sort of a [[u8]] column
    assert_eq!(expr("[\"c\", \"a\", \"b\"][grade([\"c\", \"a\", \"b\"])]"), "[\"a\", \"b\", \"c\"]");
}

// ---------- round trips ----------

fn parse_print(src: &str) -> String {
    let ds = parse::parse_unit(src).expect("parse");
    print::fmt_program(&ds)
}

#[test]
fn text_roundtrip_is_idempotent() {
    let tour = std::fs::read_to_string("examples/tour.sn").unwrap();
    let once = parse_print(&tour);
    let twice = parse_print(&once);
    assert_eq!(once, twice, "reprint is not idempotent");
}

#[test]
fn binary_roundtrip_preserves_values() {
    let tour = std::fs::read_to_string("examples/tour.sn").unwrap();
    let mut l = snel::FileLoader::new("examples".into()); // tour uses `use text`
    let v = eval_unit(&mut l, &tour).expect("eval");
    let v2 = snel::bin_roundtrip(&v).expect("bin roundtrip");
    assert_eq!(print::fmt_val(&v), print::fmt_val(&v2));
}

#[test]
fn binary_roundtrip_chunk_encodings() {
    // long homogeneous / RLE-friendly / null-heavy columns exercise chunking
    let cases = [
        "pub let a = iota(1000)",
        "pub let b = map(fun(x: i64) -> i64 = 7, iota(600))",
        "pub let c = [1.5, 2.5, 3.5]",
        "pub let d = select(map(fun(x:i64)->bit = x % 2 = 0, iota(500)), iota(500), nil)",
    ];
    for src in cases {
        let mut l = NoLoader;
        let v = eval_unit(&mut l, src).expect(src);
        let v2 = snel::bin_roundtrip(&v).unwrap_or_else(|e| panic!("{}: {}", src, e));
        assert_eq!(print::fmt_val(&v), print::fmt_val(&v2), "case {}", src);
    }
}

#[test]
fn f64_text_roundtrip() {
    // canonical spelling is stable under reprint
    for x in ["0.0", "-0.0", "3.0", "0.1", "1.0e100", "1.5e-10", "inf", "-inf", "nan", "123.456"] {
        assert_eq!(expr(x), x, "f64 {}", x);
    }
    // non-canonical inputs normalize but re-parse to the same value
    assert_eq!(expr("1e100"), "1.0e100");
    assert_eq!(expr("expr_reparse_marker"), "ERR: check error (line 1): unbound name `expr_reparse_marker`");
}
