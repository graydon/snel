// Differential-fuzz corpus generator. Emits random *closed* Snel programs
// drawn from most of the grammar and most of the builtin repertoire. The
// language is total (no recursion, no eval), so every generated program
// terminates; type errors are fine — the two interpreters must agree on the
// error too, not just on success values.
//
//   fuzz gen N SEED      print N programs separated by a NUL byte
//   fuzz one SEED        print one program
//   fuzz bytes           read raw bytes on stdin, print the program they steer
//   fuzz cover N SEED    report which builtins and features N programs reach
//   fuzz lsp SEED        print a framed LSP session over one generated program
//
// Generation is *type-directed and scope-aware*: the generator tracks the
// approximate type of every binding it has made, so it can refer back to them
// and mostly produce programs that get past the checker and actually evaluate.
// (Roughly one production in twelve is deliberately ill-typed, to keep the
// checker's error paths under test as well.)
//
// The `bytes` mode is what makes this usable as a coverage-guided libfuzzer
// target: each choice consumes one input byte, so libfuzzer's byte-level
// mutations map onto grammar-level choices, and the corpus it evolves is a
// corpus of interesting *programs*. See fuzz/fuzz_targets/.

use std::io::{Read, Write};

// ---------- randomness: a seed, or a fuzzer's byte string ----------

pub struct Rng {
    s: u64,
    b: Vec<u8>,
    i: usize,
}

impl Rng {
    pub fn from_seed(seed: u64) -> Rng {
        Rng { s: seed | 1, b: Vec::new(), i: 0 }
    }

    // Drive generation from raw bytes. When they run out we fall back to a
    // deterministic xorshift, so a short input still yields a whole program.
    pub fn from_bytes(b: &[u8]) -> Rng {
        let mut s: u64 = 0x9E37_79B9_7F4A_7C15;
        for &x in b.iter().take(8) {
            s = s.rotate_left(8) ^ u64::from(x);
        }
        Rng { s: s | 1, b: b.to_vec(), i: 0 }
    }

    fn next(&mut self) -> u64 {
        if self.i < self.b.len() {
            // Low byte is the input byte itself, so a one-byte mutation moves
            // exactly one grammar choice; the high bits stay well mixed.
            let x = self.b[self.i];
            self.i += 1;
            self.s = self.s.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(u64::from(x));
            return u64::from(x) | (self.s & !0xFF);
        }
        let mut x = self.s;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.s = x;
        x
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    fn chance(&mut self, n: usize) -> bool {
        self.below(n) == 0
    }

    fn pick<T: Copy>(&mut self, xs: &[T]) -> T {
        xs[self.below(xs.len())]
    }
}

// ---------- the shapes the generator reasons about ----------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum T {
    Int,
    Flt,
    Bit,
    Byte,
    IVec,
    FVec,
    BVec,
    Str,    // [u8]
    StrVec, // [[u8]]
    Rec,    // the canonical two-column table
    Fun,    // fun(i64) -> i64
}

use T::*;

const SCALARS: &[T] = &[Int, Flt, Bit, Byte];
const VECS: &[T] = &[IVec, FVec, BVec, Str, StrVec];
const ALL: &[T] = &[Int, Flt, Bit, Byte, IVec, FVec, BVec, Str, StrVec, Rec, Fun];

fn tyname(t: T) -> &'static str {
    match t {
        Int => "i64",
        Flt => "f64",
        Bit => "bit",
        Byte => "u8",
        IVec => "[i64]",
        FVec => "[f64]",
        BVec => "[bit]",
        Str => "[u8]",
        StrVec => "[[u8]]",
        Rec => "{ k: [i64], x: [i64] }",
        Fun => "fun(i64) -> i64",
    }
}

struct Gen {
    r: Rng,
    sc: Vec<(String, T)>,    // in-scope value bindings
    types: Vec<(String, T)>, // `type` names and the shape underneath
    mods: Vec<String>,       // non-parametric module names (each has .a : i64)
    n: usize,                // fresh-name counter
    used_std: bool,
}

impl Gen {
    fn fresh(&mut self, tag: &str) -> String {
        self.n += 1;
        format!("{}{}", tag, self.n)
    }

    fn bind(&mut self, name: String, t: T) {
        self.sc.push((name, t));
    }

    // A name in scope with the wanted shape, if there is one.
    fn var(&mut self, t: T) -> Option<String> {
        let hits: Vec<String> =
            self.sc.iter().filter(|(_, vt)| *vt == t).map(|(n, _)| n.clone()).collect();
        if hits.is_empty() {
            return None;
        }
        let i = self.r.below(hits.len());
        Some(hits[i].clone())
    }

    // ---------- literals ----------

    fn int_lit(&mut self) -> String {
        match self.r.below(8) {
            0 => format!("0x{:x}", self.r.below(4096)),
            1 => format!("0b{:b}", self.r.below(64)),
            2 => format!("1_{:03}", self.r.below(1000)),
            3 => {
                let v = self.r.below(21) as i64 - 10;
                if v < 0 {
                    format!("({v})")
                } else {
                    v.to_string()
                }
            }
            _ => self.r.below(40).to_string(),
        }
    }

    fn flt_lit(&mut self) -> String {
        match self.r.below(8) {
            0 => "inf".into(),
            1 => "(-inf)".into(),
            2 => "nan".into(),
            3 => format!("{}e{}", self.r.below(9) + 1, self.r.below(6) as i64 - 3),
            4 => "0.0".into(),
            5 => "(-0.0)".into(),
            _ => format!("{}.{}", self.r.below(20), self.r.below(100)),
        }
    }

    fn byte_lit(&mut self) -> String {
        match self.r.below(4) {
            0 => format!("'\\x{:02x}'", self.r.below(256)),
            1 => "'\\n'".into(),
            2 => "'\\\\'".into(),
            _ => format!("'{}'", self.r.pick(&["a", "z", "0", "m", " "])),
        }
    }

    fn str_lit(&mut self) -> String {
        let words = [
            "", "a", "ab", "hello", "a,b,c", "x/y", "foo", "café", "  ", "12_3", "\\n", "\\\"q\\\"",
            "\\xff\\xfe", "aaabbbcc", "the quick brown",
        ];
        format!("\"{}\"", self.r.pick(&words))
    }

    fn bitvec_lit(&mut self) -> String {
        let n = 1 + self.r.below(8);
        let bits: String = (0..n).map(|_| if self.r.chance(2) { '1' } else { '0' }).collect();
        format!(":{bits}")
    }

    // ---------- expressions ----------

    fn lit(&mut self, t: T) -> String {
        match t {
            Int => self.int_lit(),
            Flt => self.flt_lit(),
            Bit => self.r.pick(&["true", "false"]).to_string(),
            Byte => self.byte_lit(),
            Str => self.str_lit(),
            BVec => self.bitvec_lit(),
            IVec => {
                let n = 1 + self.r.below(5);
                let mut xs = Vec::new();
                for _ in 0..n {
                    // a nil makes it an [i64?] column, which is worth covering —
                    // but sparingly: it infects every scalar drawn out of it
                    if self.r.chance(14) {
                        xs.push("nil".to_string());
                    } else {
                        xs.push(self.int_lit());
                    }
                }
                format!("[{}]", xs.join(", "))
            }
            FVec => {
                let n = 1 + self.r.below(4);
                let xs: Vec<String> = (0..n).map(|_| self.flt_lit()).collect();
                format!("[{}]", xs.join(", "))
            }
            StrVec => {
                let n = 1 + self.r.below(4);
                let xs: Vec<String> = (0..n).map(|_| self.str_lit()).collect();
                format!("[{}]", xs.join(", "))
            }
            Rec => {
                let n = 1 + self.r.below(4);
                let ks: Vec<String> = (0..n).map(|_| self.r.below(4).to_string()).collect();
                let xs: Vec<String> = (0..n).map(|_| self.int_lit()).collect();
                format!("{{ k = [{}], x = [{}] }}", ks.join(", "), xs.join(", "))
            }
            Fun => {
                let b = self.gen(Int, 1);
                format!("fun(a: i64) -> i64 = {b}")
            }
        }
    }

    // A general expression of (approximately) shape `t`.
    fn gen(&mut self, t: T, d: usize) -> String {
        // occasionally return something of the wrong shape, to exercise the
        // checker's rejection paths as well as its acceptance paths. Kept rare:
        // a unit that fails the checker never reaches the evaluator at all.
        if self.r.chance(40) {
            let other = self.r.pick(ALL);
            if other != t {
                return self.gen(other, d.min(1));
            }
        }
        if d == 0 || self.r.chance(4) {
            if self.r.chance(2) {
                if let Some(v) = self.var(t) {
                    return v;
                }
            }
            return self.lit(t);
        }
        let e = self.produce(t, d - 1);
        // wrap in a pipe, an ascription, or a block now and then
        match self.r.below(14) {
            0 => format!("({e} : {})", tyname(t)),
            1 => format!("do let {} = {e}; {} end", "q", "q"),
            2 => format!("(let q = {e}; q)"),
            3 => format!("try {e} else {}", self.lit(t)),
            _ => e,
        }
    }

    fn produce(&mut self, t: T, d: usize) -> String {
        match t {
            Int => self.gen_int(d),
            Flt => self.gen_flt(d),
            Bit => self.gen_bit(d),
            Byte => self.gen_byte(d),
            IVec => self.gen_ivec(d),
            FVec => self.gen_fvec(d),
            BVec => self.gen_bvec(d),
            Str => self.gen_str(d),
            StrVec => self.gen_strvec(d),
            Rec => self.gen_rec(d),
            Fun => self.gen_fun(d),
        }
    }

    fn gen_int(&mut self, d: usize) -> String {
        match self.r.below(22) {
            0 => {
                let op = self.r.pick(&["+", "-", "*", "%", "/"]);
                format!("({} {} {})", self.gen(Int, d), op, self.gen(Int, d))
            }
            1 => format!("sum({})", self.gen(IVec, d)),
            2 => format!("prod({})", self.gen(IVec, d)),
            3 => format!("min({})", self.gen(IVec, d)),
            4 => format!("max({})", self.gen(IVec, d)),
            5 => { let vt = self.r.pick(VECS); format!("len({})", self.gen(vt, d)) }
            6 => format!("abs({})", self.gen(Int, d)),
            7 => format!("neg({})", self.gen(Int, d)),
            8 => format!("sign({})", self.gen(Int, d)),
            9 => format!("ftoi({})", self.gen(Flt, d)),
            10 => format!("ord({})", self.gen(Byte, d)),
            11 => format!("at({}, {})", self.r.below(4), self.gen(IVec, d)),
            12 => format!("first({})", self.gen(IVec, d)),
            13 => format!("last({})", self.gen(IVec, d)),
            14 => format!("sum({})", self.gen(BVec, d)),
            15 => {
                let f = self.gen(Fun, d);
                format!("fold(fun(a: i64, x: i64) -> i64 = ({f})(a + x), 0, {})", self.gen(IVec, d))
            }
            16 => format!("if {} then {} else {}", self.gen(Bit, d), self.gen(Int, d), self.gen(Int, d)),
            17 => format!("try {} else {}", self.gen(Int, d), self.gen(Int, d)),
            18 => format!("{} |> at(0)", self.gen(IVec, d)),
            19 => {
                let m = self.mods.clone();
                if m.is_empty() {
                    format!("sum({})", self.gen(IVec, d))
                } else {
                    let i = self.r.below(m.len());
                    format!("{}.a", m[i])
                }
            }
            20 => format!("len(get(locals(), \"v1\"))"),
            _ => format!("at(0, ({}).x)", self.gen(Rec, d)),
        }
    }

    fn gen_flt(&mut self, d: usize) -> String {
        match self.r.below(10) {
            0 => {
                let op = self.r.pick(&["+", "-", "*", "/"]);
                format!("({} {} {})", self.gen(Flt, d), op, self.gen(Flt, d))
            }
            1 => format!("sqrt({})", self.gen(Flt, d)),
            2 => format!("floor({})", self.gen(Flt, d)),
            3 => format!("ceil({})", self.gen(Flt, d)),
            4 => format!("abs({})", self.gen(Flt, d)),
            5 => format!("itof({})", self.gen(Int, d)),
            6 => format!("sum({})", self.gen(FVec, d)),
            7 => format!("max({})", self.gen(FVec, d)),
            8 => format!("at(0, {})", self.gen(FVec, d)),
            _ => format!("neg({})", self.gen(Flt, d)),
        }
    }

    fn gen_bit(&mut self, d: usize) -> String {
        match self.r.below(14) {
            0 => {
                let op = self.r.pick(&["=", "<>", "<", "<=", ">", ">="]);
                format!("({} {} {})", self.gen(Int, d), op, self.gen(Int, d))
            }
            1 => {
                let op = self.r.pick(&["=", "<", ">="]);
                format!("({} {} {})", self.gen(Flt, d), op, self.gen(Flt, d))
            }
            2 => format!("not({})", self.gen(Bit, d)),
            3 => format!("and({}, {})", self.gen(Bit, d), self.gen(Bit, d)),
            4 => format!("or({}, {})", self.gen(Bit, d), self.gen(Bit, d)),
            5 => format!("all({})", self.gen(BVec, d)),
            6 => format!("any({})", self.gen(BVec, d)),
            7 => format!("in({}, {})", self.gen(Int, d), self.gen(IVec, d)),
            8 => {
                let t = self.r.pick(SCALARS);
                format!("({} is {})", self.gen(t, d), tyname(t))
            }
            9 => format!("({} is str)", self.gen(Str, d)),
            10 => format!("({} is sym)", self.gen(Str, d)),
            11 => {
                let ty = self.types.clone();
                if ty.is_empty() {
                    format!("({} is i64)", self.gen(Int, d))
                } else {
                    let i = self.r.below(ty.len());
                    let (n, s) = ty[i].clone();
                    format!("({} is {})", self.gen(s, d), n)
                }
            }
            12 => format!("isnil(find({}, {}))", self.gen(Str, d), self.gen(Str, d)),
            _ => format!("({} and {})", self.gen(Bit, d), self.gen(Bit, d)),
        }
    }

    fn gen_byte(&mut self, d: usize) -> String {
        match self.r.below(5) {
            0 => format!("chr({})", self.gen(Int, d)),
            1 => format!("at(0, {})", self.gen(Str, d)),
            2 => format!("first({})", self.gen(Str, d)),
            3 => format!("last({})", self.gen(Str, d)),
            _ => format!("max({})", self.gen(Str, d)),
        }
    }

    fn gen_ivec(&mut self, d: usize) -> String {
        match self.r.below(30) {
            0 => format!("iota({})", self.r.below(8)),
            1 => {
                let op = self.r.pick(&["+", "-", "*", "%"]);
                format!("({} {} {})", self.gen(IVec, d), op, self.gen(Int, d))
            }
            2 => format!("({} + {})", self.gen(IVec, d), self.gen(IVec, d)),
            3 => format!("cat({}, {})", self.gen(IVec, d), self.gen(IVec, d)),
            4 => format!("rev({})", self.gen(IVec, d)),
            5 => format!("distinct({})", self.gen(IVec, d)),
            6 => format!("grade({})", self.gen(IVec, d)),
            7 => format!("which({})", self.gen(BVec, d)),
            8 => format!("sums({})", self.gen(IVec, d)),
            9 => format!("prods({})", self.gen(IVec, d)),
            10 => format!("take({}, {})", self.r.below(6), self.gen(IVec, d)),
            11 => format!("drop({}, {})", self.r.below(6), self.gen(IVec, d)),
            12 => format!("rep({}, {})", self.r.below(5), self.gen(Int, d)),
            13 => format!("shift({}, 0, {})", self.r.below(7) as i64 - 3, self.gen(IVec, d)),
            14 => {
                format!("scatter([0, 1], [8, 9], {})", self.gen(IVec, d))
            }
            15 => {
                let v = self.gen(IVec, d);
                format!("{v}[{}]", self.gen(BVec, d))
            }
            16 => {
                let v = self.gen(IVec, d);
                format!("{v}[iota({})]", self.r.below(4))
            }
            17 => format!("map(fun(x: i64) -> i64 = {}, {})", self.gen(Int, d), self.gen(IVec, d)),
            18 => format!("map(abs, {})", self.gen(IVec, d)),
            19 => format!(
                "map2(fun(a: i64, b: i64) -> i64 = (a + b), {}, {})",
                self.gen(IVec, d),
                self.gen(IVec, d)
            ),
            20 => format!("filter(fun(x: i64) -> bit = (x > 0), {})", self.gen(IVec, d)),
            21 => format!("scan(fun(a: i64, x: i64) -> i64 = (a + x), 0, {})", self.gen(IVec, d)),
            22 => format!("select({}, {}, {})", self.gen(BVec, d), self.gen(IVec, d), self.gen(Int, d)),
            23 => format!("sums(select({}, 1, 0))", self.gen(BVec, d)),
            24 => format!("map(len, {})", self.gen(StrVec, d)),
            25 => format!("({}).k", self.gen(Rec, d)),
            26 => format!("map(sum, windows({}, {}))", 1 + self.r.below(3), self.gen(IVec, d)),
            27 => format!("map(len, partition(runs({v}), {v}))", v = self.gen(IVec, d)),
            28 => format!("{} |> take({})", self.gen(IVec, d), self.r.below(4)),
            _ => {
                let f = self.gen(Fun, d);
                format!("map({}, {})", f, self.gen(IVec, d))
            }
        }
    }

    fn gen_fvec(&mut self, d: usize) -> String {
        match self.r.below(8) {
            0 => format!("({} + {})", self.gen(FVec, d), self.gen(FVec, d)),
            1 => format!("({} * {})", self.gen(FVec, d), self.gen(Flt, d)),
            2 => format!("sqrt({})", self.gen(FVec, d)),
            3 => format!("floor({})", self.gen(FVec, d)),
            4 => format!("itof({})", self.gen(IVec, d)),
            5 => format!("cat({}, {})", self.gen(FVec, d), self.gen(FVec, d)),
            6 => format!("rev({})", self.gen(FVec, d)),
            _ => format!("sums({})", self.gen(FVec, d)),
        }
    }

    fn gen_bvec(&mut self, d: usize) -> String {
        match self.r.below(16) {
            0 => {
                let op = self.r.pick(&["=", "<>", "<", "<=", ">", ">="]);
                format!("({} {} {})", self.gen(IVec, d), op, self.gen(Int, d))
            }
            1 => format!("({} > {})", self.gen(IVec, d), self.gen(IVec, d)),
            2 => format!("not({})", self.gen(BVec, d)),
            3 => format!("and({}, {})", self.gen(BVec, d), self.gen(BVec, d)),
            4 => format!("or({}, {})", self.gen(BVec, d), self.gen(BVec, d)),
            5 => format!("isnil({})", self.gen(IVec, d)),
            6 => format!("runs({})", self.gen(IVec, d)),
            7 => format!("member({}, {})", self.gen(IVec, d), self.gen(IVec, d)),
            8 => format!("matches({}, {})", self.gen(IVec, d), self.gen(IVec, d)),
            9 => format!("member({}, {})", self.gen(Str, d), self.gen(Str, d)),
            10 => format!("matches({}, {})", self.gen(Str, d), self.gen(Str, d)),
            11 => format!("({} is i64)", self.gen(IVec, d)),
            12 => format!("runs({})", self.gen(Str, d)),
            13 => format!("({} < {})", self.gen(Str, d), self.gen(Str, d)),
            14 => format!("rev({})", self.gen(BVec, d)),
            _ => format!("cat({}, {})", self.gen(BVec, d), self.gen(BVec, d)),
        }
    }

    fn gen_str(&mut self, d: usize) -> String {
        match self.r.below(20) {
            0 => format!("cat({}, {})", self.gen(Str, d), self.gen(Str, d)),
            1 => format!("join({}, {})", self.gen(Str, d), self.gen(StrVec, d)),
            2 => format!("rev({})", self.gen(Str, d)),
            3 => format!("take({}, {})", self.r.below(6), self.gen(Str, d)),
            4 => format!("drop({}, {})", self.r.below(6), self.gen(Str, d)),
            5 => {
                let s = self.gen(Str, d);
                format!("{s}[{}]", self.gen(BVec, d))
            }
            6 => format!("chr({})", self.gen(IVec, d)),
            7 => { let st = self.r.pick(ALL); format!("show({})", self.gen(st, d)) }
            8 => { let jt = self.r.pick(&[Int, Flt, Bit, IVec, FVec, Str, StrVec, Rec]); format!("try tojson({}) else \"\"", self.gen(jt, d)) }
            9 => format!("try tocsv({}) else \"\"", self.gen(Rec, d)),
            10 => format!("try unparse(parse({})) else \"\"", self.gen(Str, d)),
            11 => format!("encode({})", self.gen(IVec, d)),
            12 => format!("distinct({})", self.gen(Str, d)),
            13 => format!("{} |> drop(1)", self.gen(Str, d)),
            14 => ":asym".to_string(),
            15 => format!("select({}, {}, {})", self.gen(BVec, d), self.gen(Str, d), self.gen(Byte, d)),
            16 => format!("scatter([0], {}, {})", self.gen(Str, d), self.gen(Str, d)),
            17 => format!("show(reflect({}))", self.gen(Fun, d)),
            18 => format!("try unparse(decode(encode(parse({})))) else \"\"", self.gen(Str, d)),
            _ => self.str_lit(),
        }
    }

    fn gen_strvec(&mut self, d: usize) -> String {
        match self.r.below(8) {
            0 => format!("split({}, {})", self.gen(Str, d), self.gen(Str, d)),
            1 => format!("[{}, {}]", self.gen(Str, d), self.gen(Str, d)),
            2 => format!("rev({})", self.gen(StrVec, d)),
            3 => format!("distinct({})", self.gen(StrVec, d)),
            4 => format!("partition(runs({v}), {v})", v = self.gen(Str, d)),
            5 => format!("windows({}, {})", 1 + self.r.below(3), self.gen(Str, d)),
            6 => format!("cat({}, {})", self.gen(StrVec, d), self.gen(StrVec, d)),
            _ => format!("map(rev, {})", self.gen(StrVec, d)),
        }
    }

    fn gen_rec(&mut self, d: usize) -> String {
        match self.r.below(6) {
            0 => {
                let t = self.lit(Rec);
                format!("{t}[{}]", self.gen(BVec, d))
            }
            1 => format!("fromcsv(tocsv({}))", self.gen(Rec, d)),
            2 => format!("fromjson(tojson({}))", self.gen(Rec, d)),
            3 => {
                let t = self.gen(Rec, d);
                format!("{t}[iota({})]", self.r.below(3))
            }
            4 => format!("group({}, :k)", self.gen(Rec, d)),
            _ => self.lit(Rec),
        }
    }

    fn gen_fun(&mut self, d: usize) -> String {
        match self.r.below(6) {
            0 => "abs".to_string(),
            1 => "neg".to_string(),
            2 => "sign".to_string(),
            3 => {
                let b = self.gen(Int, d);
                format!("fun(a: i64) -> i64 = {b}")
            }
            4 => "fun(a: i64) -> i64 = (a * 2)".to_string(),
            _ => "fun(a: i64) -> i64 = sum(iota(abs(a) % 5))".to_string(),
        }
    }

    // ---------- declarations ----------

    fn decl(&mut self, out: &mut Vec<String>) {
        // a doc comment now and then (they are attached, printed, serialized)
        if self.r.chance(9) {
            out.push("-- a doc comment".to_string());
        }
        match self.r.below(20) {
            0..=7 => {
                // let, sometimes annotated, sometimes public
                let t = self.r.pick(ALL);
                let name = self.fresh("v");
                let d = 2 + self.r.below(2);
                let mut e = self.gen(t, d);
                if !self.r.chance(3) {
                    let fallback = self.lit(t);
                    e = format!("try {e} else {fallback}");
                }
                // `Fun` is left unannotated: a bare builtin is polymorphic and
                // has no value type to match. `[i64]` is annotated nil-admitting,
                // since the literals put nils in.
                let ann = match t {
                    Fun => String::new(),
                    IVec if self.r.chance(3) => ": [i64?]".to_string(),
                    _ if self.r.chance(3) => format!(": {}", tyname(t)),
                    _ => String::new(),
                };
                let vis = if self.r.chance(2) { "pub " } else { "" };
                out.push(format!("{vis}let {name}{ann} = {e};"));
                self.bind(name, t);
            }
            8..=10 => {
                // a user function, then a call to it
                let at = self.r.pick(SCALARS);
                let rt = self.r.pick(&[Int, Flt, Bit, Byte, IVec, FVec, BVec, Str, StrVec, Rec]);
                let f = self.fresh("f");
                let body = {
                    let p = "p".to_string();
                    self.bind(p, at);
                    let b = self.gen(rt, 2);
                    self.sc.pop();
                    b
                };
                out.push(format!("fun {f}(p: {}) -> {} = {body};", tyname(at), tyname(rt)));
                let name = self.fresh("v");
                let arg = self.gen(at, 1);
                let vis = if self.r.chance(2) { "pub " } else { "" };
                out.push(format!("{vis}let {name} = {f}({arg});"));
                self.bind(name, rt);
            }
            11..=13 => {
                // a predicate subtype, then an ascription / test through it
                let base = self.r.pick(&[Int, Flt, IVec, Str]);
                let n = self.fresh("T");
                let pred = self.gen(Bit, 1);
                out.push(format!(
                    "type {n} = {} where fun(w: {}) -> bit = {pred};",
                    tyname(base),
                    tyname(base)
                ));
                self.types.push((n.clone(), base));
                // A `type` naming another `type` — the composite case, whose inner
                // predicate is `true` so the probe tests composition itself
                // rather than dying on a refinement.
                if self.r.chance(2) {
                    let ok = self.fresh("T");
                    let n2 = self.fresh("T");
                    out.push(format!(
                        "type {ok} = {} where fun(w: {}) -> bit = true;",
                        tyname(base),
                        tyname(base)
                    ));
                    out.push(format!(
                        "type {n2} = {{ a: {ok} }} where fun(w: {{ a: {} }}) -> bit = true;",
                        tyname(base)
                    ));
                    let name = self.fresh("v");
                    let inner = self.gen(base, 1);
                    out.push(format!(
                        "pub let {name} = (fun(z: {n2}) -> {n2} = z)({{ a = {inner} }});"
                    ));
                }
                let name = self.fresh("v");
                let e = self.gen(base, 1);
                let fb = self.lit(base);
                out.push(format!("pub let {name} = try ({e} : {n}) else ({fb} : {});", tyname(base)));
                self.bind(name, base);
            }
            14..=15 => {
                // a union type and a mixed column through it
                let n = self.fresh("T");
                out.push(format!("type {n} = i64 | f64;"));
                let name = self.fresh("v");
                out.push(format!(
                    "pub let {name} = ([{}, {}, {}] : [{n}]);",
                    self.int_lit(),
                    self.flt_lit(),
                    self.int_lit()
                ));
                let name2 = self.fresh("v");
                out.push(format!("pub let {name2} = {name}[{name} is i64];"));
            }
            16..=17 => {
                // a module, plain or parametric, then a projection out of it
                let m = self.fresh("m");
                let e = self.gen(Int, 2);
                if self.r.chance(2) {
                    out.push(format!(
                        "mod {m} {{ pub let a = {e}; pub fun g(x: i64) -> i64 = (x + 1) }};"
                    ));
                    self.mods.push(m.clone());
                    let name = self.fresh("v");
                    out.push(format!("pub let {name} = {m}.g({m}.a);"));
                    self.bind(name, Int);
                } else {
                    out.push(format!(
                        "mod {m}(k: i64) {{ pub let a: i64 = (k + {e}) }};"
                    ));
                    let name = self.fresh("v");
                    out.push(format!("pub let {name} = {m}({}).a;", self.int_lit()));
                    self.bind(name, Int);
                }
            }
            18 => {
                // an import (the driver puts std.sn beside the program)
                if !self.used_std {
                    self.used_std = true;
                    out.push("use std;".to_string());
                    let name = self.fresh("v");
                    out.push(format!("pub let {name} = std.itoa(abs({}) % 500);", self.int_lit()));
                    self.bind(name, Str);
                } else {
                    let name = self.fresh("v");
                    let e = self.gen(IVec, 2);
                    out.push(format!("pub let {name} = {e};"));
                    self.bind(name, IVec);
                }
            }
            _ => {
                // err / try, and a bare expression declaration
                let name = self.fresh("v");
                let e = self.gen(Int, 2);
                out.push(format!("pub let {name} = try err {} else {e};", self.str_lit()));
                self.bind(name, Int);
                let bt = self.r.pick(ALL);
                out.push(format!("{};", self.gen(bt, 1)));
            }
        }
    }

    fn unit(&mut self) -> String {
        let n = 2 + self.r.below(5);
        let mut out = Vec::new();
        for _ in 0..n {
            self.decl(&mut out);
        }
        // make sure the unit exports something, so the printed value is not `{}`
        let t = self.r.pick(ALL);
        let e = self.gen(t, 2);
        let fallback = self.lit(t);
        out.push(format!("pub let result = try {e} else {fallback};"));
        out.join("\n")
    }
}

pub fn program_from_seed(seed: u64) -> String {
    gen_with(Rng::from_seed(seed))
}

pub fn program_from_bytes(b: &[u8]) -> String {
    gen_with(Rng::from_bytes(b))
}

fn gen_with(r: Rng) -> String {
    let mut g = Gen { r, sc: Vec::new(), types: Vec::new(), mods: Vec::new(), n: 0, used_std: false };
    g.unit()
}

// Every builtin and surface feature we want the corpus to reach, so `fuzz
// cover` can report what the generator is actually emitting.
const FEATURES: &[(&str, &str)] = &[
    ("add", "+"), ("sub", "-"), ("mul", "*"), ("div", "/"), ("rem", "%"),
    ("neg", "neg("), ("abs", "abs("), ("itof", "itof("), ("ftoi", "ftoi("),
    ("sqrt", "sqrt("), ("floor", "floor("), ("ceil", "ceil("), ("sign", "sign("),
    ("ord", "ord("), ("chr", "chr("), ("eq", "="), ("ne", "<>"), ("lt", "<"),
    ("le", "<="), ("gt", ">"), ("ge", ">="), ("and", "and("), ("or", "or("),
    ("not", "not("), ("len", "len("), ("cat", "cat("), ("iota", "iota("),
    ("grade", "grade("), ("sum", "sum("), ("prod", "prod("), ("min", "min("),
    ("max", "max("), ("isnil", "isnil("), ("all", "all("), ("any", "any("),
    ("rev", "rev("), ("take", "take("), ("drop", "drop("), ("first", "first("),
    ("last", "last("), ("which", "which("), ("distinct", "distinct("),
    ("in", "in("), ("map", "map("), ("map2", "map2("), ("fold", "fold("),
    ("scan", "scan("), ("filter", "filter("), ("group", "group("),
    ("select", "select("), ("find", "find("), ("split", "split("),
    ("join", "join("), ("locals", "locals("), ("reflect", "reflect("),
    ("show", "show("), ("encode", "encode("), ("decode", "decode("),
    ("parse", "parse("), ("unparse", "unparse("), ("at", "at("), ("rep", "rep("),
    ("scatter", "scatter("), ("shift", "shift("), ("sums", "sums("),
    ("prods", "prods("), ("member", "member("), ("matches", "matches("),
    ("runs", "runs("), ("partition", "partition("), ("windows", "windows("),
    ("tojson", "tojson("), ("fromjson", "fromjson("), ("tocsv", "tocsv("),
    ("fromcsv", "fromcsv("),
    // surface features
    ("let", "let "), ("pub", "pub "), ("fun", "fun "), ("type", "type "),
    ("mod", "mod "), ("use", "use "), ("if", "if "), ("try", "try "),
    ("err", "err "), ("is", " is "), ("ascription", " : "), ("pipe", "|>"),
    ("do-end", "do "), ("block", "(let "), ("doc-comment", "--"),
    ("union-type", " | "), ("record", "{ k ="), ("bitvec-lit", ":0"),
    ("sym-lit", ":asym"), ("hex-lit", "0x"), ("bin-lit", "0b"),
    ("sep-lit", "1_"), ("inf", "inf"), ("nan", "nan"), ("nil", "nil"),
    ("char-lit", "'"), ("escape", "\\x"), ("string", "\""),
    ("builtin-as-value", "map(abs"), ("index", "["), ("project", "."),
];

// A JSON string literal, for embedding a program in an LSP message.
fn json_str(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

// One full language-server session over a generated document: initialize, open,
// edit, hover, save, close, shut down. Written framed, ready to pipe into
// `snel lsp` (see tools/lspdiff.sh).
fn lsp_session(w: &mut impl Write, src: &str) {
    let doc = json_str(src);
    let msgs = [
        r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#.to_string(),
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#.to_string(),
        format!(
            r#"{{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{{"textDocument":{{"uri":"file:///p.sn","languageId":"snel","version":1,"text":{doc}}}}}}}"#
        ),
        format!(
            r#"{{"jsonrpc":"2.0","method":"textDocument/didChange","params":{{"textDocument":{{"uri":"file:///p.sn","version":2}},"contentChanges":[{{"text":{doc}}}]}}}}"#
        ),
        r#"{"jsonrpc":"2.0","id":2,"method":"textDocument/hover","params":{"textDocument":{"uri":"file:///p.sn"},"position":{"line":0,"character":5}}}"#.to_string(),
        r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///p.sn"}}}"#.to_string(),
        r#"{"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":"file:///p.sn"}}}"#.to_string(),
        r#"{"jsonrpc":"2.0","id":3,"method":"shutdown","params":{}}"#.to_string(),
        r#"{"jsonrpc":"2.0","method":"exit","params":{}}"#.to_string(),
    ];
    for m in msgs {
        write!(w, "Content-Length: {}\r\n\r\n{}", m.len(), m).ok();
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let out = std::io::stdout();
    let mut w = out.lock();
    match args.get(1).map(|s| s.as_str()) {
        Some("gen") => {
            let n: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
            let seed: u64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(1);
            for i in 0..n {
                let p = program_from_seed(seed.wrapping_add(i).wrapping_mul(2654435761));
                w.write_all(p.as_bytes()).ok();
                w.write_all(&[0]).ok();
            }
        }
        Some("one") => {
            let seed: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(1);
            print!("{}", program_from_seed(seed));
        }
        Some("lsp") => {
            let seed: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(1);
            lsp_session(&mut w, &program_from_seed(seed));
        }
        Some("bytes") => {
            let mut b = Vec::new();
            std::io::stdin().read_to_end(&mut b).ok();
            print!("{}", program_from_bytes(&b));
        }
        Some("cover") => {
            let n: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(500);
            let seed: u64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(1);
            let mut hits = vec![0usize; FEATURES.len()];
            for i in 0..n {
                let p = program_from_seed(seed.wrapping_add(i).wrapping_mul(2654435761));
                for (j, (_, pat)) in FEATURES.iter().enumerate() {
                    if p.contains(pat) {
                        hits[j] += 1;
                    }
                }
            }
            let mut missing = Vec::new();
            for (j, (name, _)) in FEATURES.iter().enumerate() {
                if hits[j] == 0 {
                    missing.push(*name);
                }
            }
            println!(
                "{} of {} features reached in {} programs",
                FEATURES.len() - missing.len(),
                FEATURES.len(),
                n
            );
            if !missing.is_empty() {
                println!("missing: {}", missing.join(", "));
            }
        }
        _ => {
            eprintln!("usage: fuzz gen N SEED | fuzz one SEED | fuzz bytes | fuzz cover N SEED | fuzz lsp SEED");
            std::process::exit(2);
        }
    }
}
