// Canonical text form: values, types, code. Everything printed here
// re-parses to an equal value/AST (round trip). Also the spec'd f64 routine.

use crate::ast::{op_infix, op_name, Ast, Node, Op, Ty};
use crate::value::{Bytes, Col, Payload, Tab, Val};

// ---------- f64 ----------

// Fewest significant digits (1..=17) whose correctly-rounded decimal
// reparses to identical bits; exponent form when decimal exp < -4 or >= 17.
pub fn fmt_f64(x: f64) -> String {
    if x.is_nan() {
        return "nan".into();
    }
    if x.is_infinite() {
        return if x < 0.0 { "-inf".into() } else { "inf".into() };
    }
    if x == 0.0 {
        return if x.is_sign_negative() { "-0.0".into() } else { "0.0".into() };
    }
    let neg = x < 0.0;
    let a = x.abs();
    let (digits, exp10) = (1..=17)
        .map(|p| {
            let s = format!("{:.*e}", p - 1, a); // e.g. "1.50e2"
            let (m, e) = s.split_once('e').unwrap();
            (m.replace('.', ""), e.parse::<i32>().unwrap())
        })
        .find(|(m, e)| decimal_to_f64(m, *e) == a)
        .unwrap();
    let digits = digits.trim_end_matches('0');
    let digits = if digits.is_empty() { "0" } else { digits };
    let mut out = String::new();
    if neg {
        out.push('-');
    }
    let nd = digits.len() as i32;
    if exp10 < -4 || exp10 >= 17 {
        out.push_str(&digits[..1]);
        out.push('.');
        out.push_str(if nd > 1 { &digits[1..] } else { "0" });
        out.push('e');
        out.push_str(&exp10.to_string());
    } else if exp10 >= nd - 1 {
        out.push_str(digits);
        out.extend(std::iter::repeat_n('0', (exp10 - nd + 1) as usize));
        out.push_str(".0");
    } else if exp10 >= 0 {
        out.push_str(&digits[..(exp10 + 1) as usize]);
        out.push('.');
        out.push_str(&digits[(exp10 + 1) as usize..]);
    } else {
        out.push_str("0.");
        out.extend(std::iter::repeat_n('0', (-exp10 - 1) as usize));
        out.push_str(digits);
    }
    out
}

// digits (as decimal string) * 10^(exp - len + 1), correctly rounded.
fn decimal_to_f64(digits: &str, exp10: i32) -> f64 {
    format!("{}e{}", digits, exp10 - digits.len() as i32 + 1).parse().unwrap()
}

pub fn parse_f64(s: &str) -> Option<f64> {
    s.parse::<f64>().ok().map(canon_f64)
}

// One canonical NaN bit pattern; applied at every construction site.
pub fn canon_f64(x: f64) -> f64 {
    if x.is_nan() {
        f64::NAN
    } else {
        x
    }
}

// ---------- u8, [u8] strings ----------

// A u8 renders as a char literal: printable ASCII directly, else an escape.
fn fmt_u8(v: u8) -> String {
    match v {
        b'\n' => "'\\n'".into(),
        b'\t' => "'\\t'".into(),
        b'\\' => "'\\\\'".into(),
        b'\'' => "'\\''".into(),
        0x20..=0x7e => format!("'{}'", v as char),
        _ => format!("'\\x{:02x}'", v),
    }
}

// A [u8] renders as a string literal when valid UTF-8, else as a vector of
// char (byte) literals.
fn fmt_u8s(bytes: &[u8]) -> String {
    match std::str::from_utf8(bytes) {
        Ok(s) => {
            let mut out = String::from("\"");
            for ch in s.chars() {
                match ch {
                    '\\' => out.push_str("\\\\"),
                    '"' => out.push_str("\\\""),
                    '\n' => out.push_str("\\n"),
                    '\t' => out.push_str("\\t"),
                    c if (c as u32) < 0x20 => out.push_str(&format!("\\x{:02x}", c as u32)),
                    c => out.push(c),
                }
            }
            out.push('"');
            out
        }
        Err(_) => {
            let cs: Vec<String> = bytes.iter().map(|b| fmt_u8(*b)).collect();
            format!("[{}]", cs.join(", "))
        }
    }
}

// ---------- number / bit-vector grouping ----------

// Insert `_` every 3 chars from the right of a run of digits.
fn group3(digits: &str) -> String {
    let n = digits.len();
    let mut out = String::with_capacity(n + n / 3);
    for (idx, ch) in digits.char_indices() {
        if idx > 0 && (n - idx) % 3 == 0 {
            out.push('_');
        }
        out.push(ch);
    }
    out
}

// Group the leading integer digits of a number's text (after an optional sign)
// every 3, leaving any fraction/exponent/`inf`/`nan` tail untouched.
fn group_number(s: &str) -> String {
    let (sign, rest) = s.strip_prefix('-').map_or(("", s), |r| ("-", r));
    let end = rest.bytes().position(|c| !c.is_ascii_digit()).unwrap_or(rest.len());
    if end == 0 {
        return s.to_string(); // inf / nan
    }
    format!("{}{}{}", sign, group3(&rest[..end]), &rest[end..])
}

// A [bit] column renders as `:1011`, index 0 first, `_` every 4 bits.
fn fmt_bits(b: &crate::value::Bits) -> String {
    let mut out = String::from(":");
    for i in 0..b.len {
        if i > 0 && i % 4 == 0 {
            out.push('_');
        }
        out.push(if b.get(i) { '1' } else { '0' });
    }
    out
}

// ---------- values ----------

pub fn fmt_val(v: &Val) -> String {
    match v {
        Val::Nil => "nil".into(),
        Val::Bit(b) => if *b { "true" } else { "false" }.into(),
        Val::I64(i) => group_number(&i.to_string()),
        Val::F64(f) => group_number(&fmt_f64(*f)),
        Val::U8(v) => fmt_u8(*v),
        Val::Vec(c) => fmt_col(c),
        Val::Tab(t) => fmt_tab(t),
        Val::Fun(c) => {
            let f = format!(
                "fun({}) -> {} = {}",
                c.params
                    .iter()
                    .map(|(x, t)| format!("{:?}: {}", x, fmt_ty(t)))
                    .collect::<Vec<_>>()
                    .join(", "),
                fmt_ty(&c.ret),
                fmt_node(&c.body, 0)
            );
            if c.env.len() == 0 {
                f
            } else {
                // Print the captured env as a let-sequence, so the closure
                // re-reads to an identical closure: the fun recaptures exactly
                // these bindings (env keys are precisely the body's free vars).
                let lets = c
                    .env
                    .keys
                    .iter()
                    .zip(&c.env.vals)
                    .map(|(k, val)| format!("let {:?} = {}", k, fmt_val(val)))
                    .collect::<Vec<_>>()
                    .join("; ");
                format!("({}; {})", lets, f)
            }
        }
        // a builtin value prints as its bare name; an io prim as `io.name`
        Val::Prim(name) => {
            if crate::ast::op_by_name(name.bytes()).is_some() {
                format!("{:?}", name)
            } else {
                format!("io.{:?}", name)
            }
        }
    }
}

pub fn col_elem(c: &Col, i: usize) -> Val {
    if let Some(p) = &c.present {
        if !p.get(i) {
            return Val::Nil;
        }
    }
    let case = c.sel.as_ref().map_or(0, |s| s[i] as usize);
    match &c.cases[case] {
        Payload::Bits(b) => Val::Bit(b.get(i)),
        Payload::I64s(v) => Val::I64(v[i]),
        Payload::F64s(v) => Val::F64(v[i]),
        Payload::U8s(b) => Val::U8(b.bytes()[i]),
        Payload::Vecs(v) => Val::Vec(v[i].clone()),
        Payload::Tabs(v) => Val::Tab(v[i].clone()),
    }
}

// Runtime element type of a column (for ascription printing).
pub fn col_ty(c: &Col) -> Ty {
    // Every case of a union column carries a full-length, aligned payload, but
    // only the rows the selector points at hold that case's real values — the
    // rest is filler whose contents are unobservable. So: read a case's shape
    // from a row that case actually owns, and skip a case the selector never
    // points at, rather than describing its filler.
    let owner = |case: usize| -> Option<usize> {
        match &c.sel {
            Some(sel) => sel.iter().position(|&s| s as usize == case),
            None => (case == 0 && c.len > 0).then_some(0),
        }
    };
    let case_ty = |i: usize, at: usize| -> Ty {
        match &c.cases[i] {
            Payload::Bits(_) => Ty::Bit,
            Payload::I64s(_) => Ty::I64,
            Payload::F64s(_) => Ty::F64,
            Payload::U8s(_) => Ty::U8,
            Payload::Vecs(v) => Ty::Vec(Box::new(match v.get(at) {
                Some(sub) => col_ty(sub),
                None => Ty::I64,
            })),
            Payload::Tabs(v) => tab_elem_ty_at(v, at),
        }
    };
    let mut ts: Vec<Ty> =
        (0..c.cases.len()).filter_map(|i| owner(i).map(|at| case_ty(i, at))).collect();
    if ts.is_empty() {
        // an empty column, or one that is all nil: nothing owns a row, so fall
        // back to describing the cases as declared
        ts = (0..c.cases.len()).map(|i| case_ty(i, 0)).collect();
    }
    if c.present.is_some() {
        ts.push(Ty::Nil);
    }
    if ts.len() == 1 {
        ts.pop().unwrap()
    } else {
        Ty::Union(ts)
    }
}

fn tab_elem_ty_at(v: &[std::rc::Rc<Tab>], i: usize) -> Ty {
    match v.get(i).or_else(|| v.first()) {
        None => Ty::Tab(vec![]),
        Some(t) => Ty::Tab(
            t.keys
                .iter()
                .zip(&t.vals)
                .map(|(k, val)| (k.clone(), val_ty(val)))
                .collect(),
        ),
    }
}

pub fn val_ty(v: &Val) -> Ty {
    match v {
        Val::Nil => Ty::Nil,
        Val::Bit(_) => Ty::Bit,
        Val::I64(_) => Ty::I64,
        Val::F64(_) => Ty::F64,
        Val::U8(_) => Ty::U8,
        Val::Vec(c) => Ty::Vec(Box::new(col_ty(c))),
        Val::Tab(t) => Ty::Tab(
            t.keys
                .iter()
                .zip(&t.vals)
                .map(|(k, val)| (k.clone(), val_ty(val)))
                .collect(),
        ),
        Val::Fun(c) => Ty::Fun(
            c.params.iter().map(|(_, t)| t.clone()).collect(),
            Box::new(c.ret.clone()),
        ),
        Val::Prim(name) => crate::io::sig(name.bytes())
            .map_or(Ty::Fun(vec![], Box::new(Ty::Nil)), |(a, r)| Ty::Fun(a, Box::new(r))),
    }
}

fn fmt_col(c: &Col) -> String {
    // A plain [u8] column prints as a string literal (or hex-byte vector).
    if c.present.is_none() && c.sel.is_none() {
        if let [Payload::U8s(b)] = c.cases.as_slice() {
            return fmt_u8s(b.bytes());
        }
        if let [Payload::Bits(b)] = c.cases.as_slice() {
            if c.len > 0 {
                return fmt_bits(b); // #1011
            }
        }
    }
    let elems: Vec<String> = (0..c.len).map(|i| fmt_val(&col_elem(c, i))).collect();
    let body = format!("[{}]", elems.join(", "));
    // Empty or union-typed columns need an ascription to re-check identically.
    if c.len == 0 || c.cases.len() > 1 {
        format!("({} : [{}])", body, fmt_ty(&col_ty(c)))
    } else {
        body
    }
}

fn fmt_tab(t: &Tab) -> String {
    if t.keys.is_empty() {
        return "{}".into();
    }
    let fields: Vec<String> = t
        .keys
        .iter()
        .zip(&t.vals)
        .map(|(k, v)| format!("{:?} = {}", k, fmt_val(v)))
        .collect();
    format!("{{ {} }}", fields.join(", "))
}

// ---------- types ----------

pub fn fmt_ty(t: &Ty) -> String {
    match t {
        Ty::Nil => "nil".into(),
        Ty::Bit => "bit".into(),
        Ty::I64 => "i64".into(),
        Ty::F64 => "f64".into(),
        Ty::U8 => "u8".into(),
        Ty::Vec(t) => format!("[{}]", fmt_ty(t)),
        Ty::Union(ts) => ts.iter().map(fmt_ty).collect::<Vec<_>>().join("|"),
        Ty::Tab(fs) => format!(
            "{{{}}}",
            fs.iter()
                .map(|(k, t)| format!("{:?}: {}", k, fmt_ty(t)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Ty::Fun(args, r) => format!(
            "fun({}) -> {}",
            args.iter().map(fmt_ty).collect::<Vec<_>>().join(", "),
            fmt_ty(r)
        ),
        Ty::Name(n) => format!("{:?}", n),
    }
}

// ---------- code ----------

// Precedence levels, loosest to tightest. Mirrors the parser.
fn op_prec(op: Op) -> u8 {
    match op {
        Op::Or => 2,
        Op::And => 3,
        Op::Eq | Op::Ne | Op::Lt | Op::Le | Op::Gt | Op::Ge => 4,
        Op::Add | Op::Sub => 5,
        Op::Mul | Op::Div | Op::Rem => 6,
        _ => 9,
    }
}

pub fn fmt_node(n: &Node, prec: u8) -> String {
    let (s, my) = fmt_ast(&n.ast);
    if my < prec {
        format!("({})", s)
    } else {
        s
    }
}

fn doc_prefix(doc: &Option<Bytes>) -> String {
    match doc {
        None => String::new(),
        Some(d) => d
            .as_str()
            .unwrap_or("")
            .lines()
            .map(|l| format!("-- {}\n", l))
            .collect(),
    }
}

// Does this predicate look like the one `type x = T` (no `where`) desugars to —
// `fun(_: T) -> bit = true`? Matched structurally, so no AST/format change is
// needed to remember that the source omitted the clause.
fn is_always_true(pred: &Node, base: &Ty) -> bool {
    match &pred.ast {
        Ast::Fun { params, ret, body } => {
            *ret == Ty::Bit
                && params.len() == 1
                && params[0].0.bytes() == b"_"
                && params[0].1 == *base
                && matches!(&body.ast, Ast::Lit(Val::Bit(true)))
        }
        _ => false,
    }
}

// Returns (text, precedence of outermost construct).
fn fmt_ast(a: &Ast) -> (String, u8) {
    match a {
        // A negative numeric literal renders with a leading `-`, which binds
        // like the prefix operator, not like an atom: without that, `(-1)[i]`
        // would print as `-1[i]` and re-read as `neg(1[i])`.
        Ast::Lit(v) => {
            let t = fmt_val(v);
            let p = if t.starts_with('-') { 7 } else { 10 };
            (t, p)
        }
        Ast::Var(x) => (format!("{:?}", x), 10),
        Ast::Proj(e, x) => (format!("{}.{:?}", fmt_node(e, 8), x), 8),
        Ast::Idx(e, i) => (format!("{}[{}]", fmt_node(e, 8), fmt_node(i, 0)), 8),
        Ast::App(f, args) => {
            // builtin operators print in surface form
            if let Ast::Var(name) = &f.ast {
                if let Some(op) = crate::ast::op_by_name(name.bytes()) {
                    if let Some(sym) = op_infix(op) {
                        if args.len() == 2 {
                            let p = op_prec(op);
                            return (
                                format!(
                                    "{} {} {}",
                                    fmt_node(&args[0], p),
                                    sym,
                                    fmt_node(&args[1], p + 1)
                                ),
                                p,
                            );
                        }
                    }
                    if op == Op::Neg && args.len() == 1 {
                        // Two ways a prefix `-` fails to re-read as this node,
                        // decided on the operand's *rendered text* (which is
                        // what the parser will see):
                        //   - text already starting with `-` would give `--`,
                        //     which does not lex;
                        //   - a numeric literal absorbs the `-` at parse time,
                        //     turning this node into a plain literal — and `-0`
                        //     and `-nan` lose the negation entirely.
                        // Both fall back to the call form. Everywhere else (a
                        // variable, a call, a vector literal) `-x` is exact. A
                        // `-` written in source is folded while parsing, so a
                        // negative literal still prints bare as `-1`.
                        let a = fmt_node(&args[0], 7);
                        let absorbs =
                            a.starts_with(|c: char| c.is_ascii_digit()) || a == "inf" || a == "nan";
                        if a.starts_with('-') || absorbs {
                            return (format!("neg({})", a), 8);
                        }
                        return (format!("-{}", a), 7);
                    }
                    if op == Op::Not && args.len() == 1 {
                        return (format!("not {}", fmt_node(&args[0], 7)), 7);
                    }
                    let inner: Vec<String> = args.iter().map(|a| fmt_node(a, 0)).collect();
                    return (format!("{}({})", op_name(op), inner.join(", ")), 8);
                }
            }
            let inner: Vec<String> = args.iter().map(|a| fmt_node(a, 0)).collect();
            (format!("{}({})", fmt_node(f, 8), inner.join(", ")), 8)
        }
        Ast::VecL(es) => (
            format!("[{}]", es.iter().map(|e| fmt_node(e, 0)).collect::<Vec<_>>().join(", ")),
            10,
        ),
        Ast::TabL(fs) => {
            if fs.is_empty() {
                ("{}".into(), 10)
            } else {
                (
                    format!(
                        "{{ {} }}",
                        fs.iter()
                            .map(|(k, e)| format!("{:?} = {}", k, fmt_node(e, 0)))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    10,
                )
            }
        }
        Ast::Fun { params, ret, body } => (
            format!(
                "fun({}) -> {} = {}",
                params
                    .iter()
                    .map(|(x, t)| format!("{:?}: {}", x, fmt_ty(t)))
                    .collect::<Vec<_>>()
                    .join(", "),
                fmt_ty(ret),
                fmt_node(body, 1)
            ),
            1,
        ),
        Ast::If(c, t, e) => (
            format!("if {} then {} else {}", fmt_node(c, 1), fmt_node(t, 1), fmt_node(e, 1)),
            1,
        ),
        Ast::Try(e, f) => (format!("try {} else {}", fmt_node(e, 1), fmt_node(f, 1)), 1),
        Ast::Err(e) => (format!("err {}", fmt_node(e, 1)), 1),
        Ast::Is(e, t) => (format!("{} is {}", fmt_node(e, 2), fmt_ty(t)), 1),
        Ast::As(e, t) => (format!("({} : {})", fmt_node(e, 0), fmt_ty(t)), 10),
        Ast::Seq(ds) => (
            format!(
                "({})",
                ds.iter().map(|d| fmt_node(d, 0)).collect::<Vec<_>>().join("; ")
            ),
            10,
        ),
        Ast::Let { x, ty, e, doc, public } => (
            format!(
                "{}{}let {:?}{} = {}",
                doc_prefix(doc),
                if *public { "pub " } else { "" },
                x,
                ty.as_ref().map_or(String::new(), |t| format!(": {}", fmt_ty(t))),
                fmt_node(e, 1)
            ),
            0,
        ),
        Ast::Type { x, base, pred, doc, public } => (
            format!(
                "{}{}type {:?} = {}{}",
                doc_prefix(doc),
                if *public { "pub " } else { "" },
                x,
                fmt_ty(base),
                // A bare alias carries the always-true predicate the parser
                // synthesizes for it; print it back as the alias it was written
                // as, not as the desugaring.
                if is_always_true(pred, base) {
                    String::new()
                } else {
                    format!(" where {}", fmt_node(pred, 1))
                }
            ),
            0,
        ),
        Ast::Use { x, url, doc } => (
            match url {
                Some(u) => format!(
                    "{}use {:?} = {}",
                    doc_prefix(doc),
                    x,
                    fmt_val(&Val::Vec(std::rc::Rc::new(crate::value::Col::u8s(u.bytes()))))
                ),
                None => format!("{}use {:?}", doc_prefix(doc), x),
            },
            0,
        ),
    }
}

// A program (unit body): declarations at top level, newline-separated.
pub fn fmt_program(ds: &[Node]) -> String {
    // `;` terminates each declaration (newlines are insignificant); the trailing
    // `;` on the last is allowed and keeps every line uniform.
    ds.iter().map(|d| fmt_node(d, 0) + ";\n").collect()
}
