// Vectorized builtins: column construction, broadcast arithmetic (COW
// in-place when uniquely referenced), total-order comparison, indexing,
// grade/group. All loops live here; the evaluator stays scalar.

use crate::ast::{Op, Ty};
use crate::print::{canon_f64, col_elem, col_ty, fmt_ty, val_ty};
use crate::value::{Bits, Bytes, Col, Payload, Tab, Val};
use std::cmp::Ordering;
use std::rc::Rc;

pub type R<T> = Result<T, String>; // message only; eval adds spans

// ---------- total order ----------

// True iff c is a plain [u8] column (one Bytes payload, no nils, no union).
pub fn is_u8_col(c: &Col) -> bool {
    c.present.is_none() && c.sel.is_none() && matches!(c.cases.as_slice(), [Payload::U8s(_)])
}

// The bytes of a plain [u8] column (or its elements, byte by byte, otherwise).
pub fn col_bytes(c: &Col) -> Vec<u8> {
    if let [Payload::U8s(b)] = c.cases.as_slice() {
        if c.present.is_none() && c.sel.is_none() {
            return b.bytes().to_vec();
        }
    }
    (0..c.len)
        .map(|i| match col_elem(c, i) {
            Val::U8(b) => b,
            _ => 0,
        })
        .collect()
}

// One order per type: nil least, then the value order. Vectors compare
// lexicographically by element (so string / nested columns sort and group).
// Cross-kind compare uses a fixed rank; it only arises inside union columns.
pub fn cmp_val(a: &Val, b: &Val) -> Ordering {
    fn rank(v: &Val) -> u8 {
        match v {
            Val::Nil => 0,
            Val::Bit(_) => 1,
            Val::I64(_) => 2,
            Val::F64(_) => 3,
            Val::U8(_) => 4,
            Val::Vec(_) => 5,
            Val::Tab(_) => 6,
            Val::Fun(_) => 8,
            Val::Prim(_) => 9,
        }
    }
    match (a, b) {
        (Val::Nil, Val::Nil) => Ordering::Equal,
        (Val::Bit(x), Val::Bit(y)) => x.cmp(y),
        (Val::I64(x), Val::I64(y)) => x.cmp(y),
        (Val::F64(x), Val::F64(y)) => x.total_cmp(y),
        (Val::U8(x), Val::U8(y)) => x.cmp(y),
        (Val::Vec(x), Val::Vec(y)) => {
            for i in 0..x.len.min(y.len) {
                let o = cmp_val(&col_elem(x, i), &col_elem(y, i));
                if o != Ordering::Equal {
                    return o;
                }
            }
            x.len.cmp(&y.len)
        }
        _ => rank(a).cmp(&rank(b)),
    }
}

// ---------- column construction ----------
// case kinds: 1 bit, 2 i64, 3 f64, 4 u8, 5 vec ([[T]]), 6 tab.
// A [u8] column's Bytes payload is immutable, so cases are built in a mutable
// `Build` and frozen once the buffer is complete.

enum Build {
    Bit(Bits),
    I64(Vec<i64>),
    F64(Vec<f64>),
    U8(Vec<u8>),
    Vec(Vec<Rc<Col>>),
    Tab(Vec<Rc<Tab>>),
}

fn empty_build(kind: u8, n: usize) -> Build {
    match kind {
        1 => Build::Bit(Bits::new(n, false)),
        2 => Build::I64(vec![0; n]),
        3 => Build::F64(vec![0.0; n]),
        4 => Build::U8(vec![0u8; n]),
        5 => Build::Vec(vec![Rc::new(Col::u8s(&[])); n]),
        _ => Build::Tab(vec![Rc::new(Tab::default()); n]),
    }
}

fn set_build(b: &mut Build, i: usize, v: &Val) {
    match (b, v) {
        (Build::Bit(a), Val::Bit(x)) => a.set(i, *x),
        (Build::I64(a), Val::I64(x)) => a[i] = *x,
        (Build::F64(a), Val::F64(x)) => a[i] = canon_f64(*x),
        (Build::U8(a), Val::U8(x)) => a[i] = *x,
        (Build::Vec(a), Val::Vec(c)) => a[i] = c.clone(),
        (Build::Tab(a), Val::Tab(x)) => a[i] = x.clone(),
        _ => unreachable!(),
    }
}

fn freeze(b: Build) -> Payload {
    match b {
        Build::Bit(a) => Payload::Bits(a),
        Build::I64(a) => Payload::I64s(a),
        Build::F64(a) => Payload::F64s(a),
        Build::U8(a) => Payload::U8s(Bytes::new(&a)),
        Build::Vec(a) => Payload::Vecs(a),
        Build::Tab(a) => Payload::Tabs(a),
    }
}

pub fn col_from_vals(vals: Vec<Val>) -> R<Col> {
    let n = vals.len();
    let mut kinds: Vec<u8> = Vec::new();
    let mut has_nil = false;
    for v in &vals {
        let k = kind_of(v);
        if v == &Val::Nil {
            has_nil = true;
            continue;
        }
        if k == 0 {
            return Err("vec elements must be prims, strings, vecs, or tabs".into());
        }
        if !kinds.contains(&k) {
            kinds.push(k);
        }
    }
    if kinds.is_empty() {
        kinds.push(2); // empty / all-nil column defaults to i64 payload
    }
    let mut builds: Vec<Build> = kinds.iter().map(|k| empty_build(*k, n)).collect();
    let mut present = Bits::new(n, true);
    let mut sel: Vec<u8> = vec![0; n];
    for (i, v) in vals.iter().enumerate() {
        match v {
            Val::Nil => present.set(i, false),
            _ => {
                let k = kind_of(v);
                let c = kinds.iter().position(|x| *x == k).unwrap();
                sel[i] = c as u8;
                set_build(&mut builds[c], i, v);
            }
        }
    }
    Ok(Col {
        len: n,
        present: if has_nil { Some(present) } else { None },
        sel: if kinds.len() > 1 { Some(sel) } else { None },
        cases: builds.into_iter().map(freeze).collect(),
    })
}

fn kind_of(v: &Val) -> u8 {
    match v {
        Val::Bit(_) => 1,
        Val::I64(_) => 2,
        Val::F64(_) => 3,
        Val::U8(_) => 4,
        Val::Vec(_) => 5,
        Val::Tab(_) => 6,
        _ => 0,
    }
}

fn ty_kind(t: &Ty) -> Option<u8> {
    match t {
        Ty::Bit => Some(1),
        Ty::I64 => Some(2),
        Ty::F64 => Some(3),
        Ty::U8 => Some(4),
        Ty::Vec(_) => Some(5),
        Ty::Tab(_) => Some(6),
        Ty::Name(_) => None, // resolved by checker before runtime coercion
        _ => None,
    }
}

// Coerce a column to the representation of element type `t` (already
// checked compatible): reorder/extend cases to the type's case order.
pub fn coerce_col(c: &Col, t: &Ty) -> R<Col> {
    let want: Vec<&Ty> = match t {
        Ty::Union(ts) => ts.iter().filter(|t| **t != Ty::Nil).collect(),
        other => vec![other],
    };
    let admits_nil = t.admits_nil();
    let kinds: Vec<u8> = want
        .iter()
        .map(|t| ty_kind(t).ok_or_else(|| format!("bad vec element type {}", fmt_ty(t))))
        .collect::<R<Vec<u8>>>()?;
    let n = c.len;
    let mut builds: Vec<Build> = kinds.iter().map(|k| empty_build(*k, n)).collect();
    let mut present = Bits::new(n, true);
    let mut sel: Vec<u8> = vec![0; n];
    for i in 0..n {
        match col_elem(c, i) {
            Val::Nil => {
                if !admits_nil {
                    return Err(format!("nil element under non-nil type {}", fmt_ty(t)));
                }
                present.set(i, false);
            }
            v => {
                let k = kind_of(&v);
                let case = kinds
                    .iter()
                    .position(|x| *x == k)
                    .ok_or_else(|| format!("element {} does not fit type {}", crate::print::fmt_val(&v), fmt_ty(t)))?;
                sel[i] = case as u8;
                set_build(&mut builds[case], i, &v);
            }
        }
    }
    Ok(Col {
        len: n,
        present: if admits_nil { Some(present) } else { None },
        sel: if kinds.len() > 1 { Some(sel) } else { None },
        cases: builds.into_iter().map(freeze).collect(),
    })
}

// ---------- broadcast arithmetic ----------

fn is_simple(c: &Col) -> bool {
    c.sel.is_none() && c.cases.len() == 1
}

fn merged_present(a: Option<&Bits>, b: Option<&Bits>) -> Option<Bits> {
    match (a, b) {
        (None, None) => None,
        (Some(x), None) | (None, Some(x)) => Some(x.clone()),
        (Some(x), Some(y)) => {
            let mut w = x.clone();
            let yw: Vec<u64> = y.words().to_vec();
            for (i, yi) in yw.iter().enumerate() {
                w.and_word(i, *yi);
            }
            Some(w)
        }
    }
}

// Scalar arithmetic on two non-nil values of the same numeric kind.
pub fn arith2(op: Op, a: &Val, b: &Val) -> R<Val> {
    match (a, b) {
        (Val::Nil, _) | (_, Val::Nil) => Ok(Val::Nil),
        (Val::I64(x), Val::I64(y)) => {
            let v = match op {
                Op::Add => x.wrapping_add(*y),
                Op::Sub => x.wrapping_sub(*y),
                Op::Mul => x.wrapping_mul(*y),
                Op::Div => {
                    if *y == 0 || (*x == i64::MIN && *y == -1) {
                        return Err("division overflow".into());
                    }
                    x / y
                }
                Op::Rem => {
                    if *y == 0 || (*x == i64::MIN && *y == -1) {
                        return Err("division overflow".into());
                    }
                    x % y
                }
                _ => unreachable!(),
            };
            Ok(Val::I64(v))
        }
        (Val::F64(x), Val::F64(y)) => {
            let v = match op {
                Op::Add => x + y,
                Op::Sub => x - y,
                Op::Mul => x * y,
                Op::Div => x / y,
                Op::Rem => x % y,
                _ => unreachable!(),
            };
            Ok(Val::F64(canon_f64(v)))
        }
        _ => Err(format!(
            "cannot {:?} {} and {}",
            op,
            fmt_ty(&val_ty(a)),
            fmt_ty(&val_ty(b))
        )),
    }
}

pub fn arith(op: Op, a: Val, b: Val) -> R<Val> {
    match (a, b) {
        (Val::Vec(ca), Val::Vec(cb)) => {
            if ca.len != cb.len {
                return Err(format!("length mismatch: {} vs {}", ca.len, cb.len));
            }
            vec_arith(op, ca, cb)
        }
        (Val::Vec(ca), s) => {
            let cb = broadcast(&s, &ca).ok_or_else(|| bcast_err(op, &s, &ca))?;
            vec_arith(op, ca, Rc::new(cb))
        }
        (s, Val::Vec(cb)) => {
            let ca = broadcast(&s, &cb).ok_or_else(|| bcast_err(op, &s, &cb))?;
            vec_arith(op, Rc::new(ca), cb)
        }
        (a, b) => arith2(op, &a, &b),
    }
}

fn bcast_err(op: Op, s: &Val, c: &Col) -> String {
    format!("cannot {:?} {} and {}", op, fmt_ty(&val_ty(s)), fmt_ty(&col_ty(c)))
}

// Broadcast a scalar to a column matching `like`'s length. A nil scalar takes
// the peer's payload kind so nil propagates against any numeric column.
fn broadcast(v: &Val, like: &Col) -> Option<Col> {
    let n = like.len;
    Some(match v {
        Val::Nil => Col {
            len: n,
            present: Some(Bits::new(n, false)),
            sel: None,
            cases: vec![freeze(empty_build(like.cases[0].kind(), n))],
        },
        Val::Bit(b) => Col::simple(Payload::Bits(Bits::new(n, *b))),
        Val::I64(x) => Col::simple(Payload::I64s(vec![*x; n])),
        Val::F64(x) => Col::simple(Payload::F64s(vec![*x; n])),
        Val::Tab(t) => Col::simple(Payload::Tabs(vec![t.clone(); n])),
        _ => return None,
    })
}

fn vec_arith(op: Op, mut a: Rc<Col>, b: Rc<Col>) -> R<Val> {
    if !is_simple(&a) || !is_simple(&b) {
        return Err("no elementwise arithmetic on union columns".into());
    }
    let present = merged_present(a.present.as_ref(), b.present.as_ref());
    let guard_div = matches!(op, Op::Div | Op::Rem);
    // COW: reuse a's buffer when uniquely referenced and kinds match.
    let out = match (&a.cases[0], &b.cases[0]) {
        (Payload::I64s(_), Payload::I64s(ybuf)) => {
            let ybuf = ybuf.clone();
            let acol = Rc::make_mut(&mut a);
            let Payload::I64s(x) = &mut acol.cases[0] else { unreachable!() };
            for i in 0..x.len() {
                let live = present.as_ref().is_none_or(|p| p.get(i));
                if guard_div {
                    if live {
                        let v = arith2(op, &Val::I64(x[i]), &Val::I64(ybuf[i]))?;
                        let Val::I64(v) = v else { unreachable!() };
                        x[i] = v;
                    } else {
                        x[i] = 0;
                    }
                } else {
                    x[i] = match op {
                        Op::Add => x[i].wrapping_add(ybuf[i]),
                        Op::Sub => x[i].wrapping_sub(ybuf[i]),
                        Op::Mul => x[i].wrapping_mul(ybuf[i]),
                        _ => unreachable!(),
                    };
                    if !live {
                        x[i] = 0;
                    }
                }
            }
            Payload::I64s(std::mem::take(x))
        }
        (Payload::F64s(_), Payload::F64s(ybuf)) => {
            let ybuf = ybuf.clone();
            let acol = Rc::make_mut(&mut a);
            let Payload::F64s(x) = &mut acol.cases[0] else { unreachable!() };
            for i in 0..x.len() {
                let live = present.as_ref().is_none_or(|p| p.get(i));
                x[i] = if !live {
                    0.0
                } else {
                    canon_f64(match op {
                        Op::Add => x[i] + ybuf[i],
                        Op::Sub => x[i] - ybuf[i],
                        Op::Mul => x[i] * ybuf[i],
                        Op::Div => x[i] / ybuf[i],
                        Op::Rem => x[i] % ybuf[i],
                        _ => unreachable!(),
                    })
                };
            }
            Payload::F64s(std::mem::take(x))
        }
        _ => {
            return Err(format!(
                "cannot {:?} {} and {}",
                op,
                fmt_ty(&col_ty(&a)),
                fmt_ty(&col_ty(&b))
            ))
        }
    };
    Ok(Val::Vec(Rc::new(Col { len: b.len, present, sel: None, cases: vec![out] })))
}

// unary elementwise: neg abs itof ftoi (nil-propagating)
pub fn unary(op: Op, v: Val) -> R<Val> {
    fn scalar(op: Op, v: &Val) -> R<Val> {
        Ok(match (op, v) {
            (_, Val::Nil) => Val::Nil,
            (Op::Neg, Val::I64(x)) => Val::I64(x.wrapping_neg()),
            (Op::Neg, Val::F64(x)) => Val::F64(-x),
            (Op::Abs, Val::I64(x)) => Val::I64(x.wrapping_abs()),
            (Op::Abs, Val::F64(x)) => Val::F64(x.abs()),
            (Op::Itof, Val::I64(x)) => Val::F64(*x as f64),
            (Op::Ftoi, Val::F64(x)) => {
                if x.is_nan() || *x < -(2f64.powi(63)) || *x >= 2f64.powi(63) {
                    return Err("ftoi out of range".into());
                }
                Val::I64(*x as i64)
            }
            (Op::Sqrt, Val::F64(x)) => Val::F64(canon_f64(x.sqrt())),
            (Op::Floor, Val::F64(x)) => Val::F64(canon_f64(x.floor())),
            (Op::Ceil, Val::F64(x)) => Val::F64(canon_f64(x.ceil())),
            (Op::Sign, Val::I64(x)) => Val::I64(x.signum()),
            (Op::Sign, Val::F64(x)) if x.is_nan() => Val::F64(canon_f64(*x)),
            (Op::Sign, Val::F64(x)) => Val::F64(if *x > 0.0 { 1.0 } else if *x < 0.0 { -1.0 } else { 0.0 }),
            (Op::Ord, Val::U8(x)) => Val::I64(*x as i64),     // byte -> its 0..255 value
            (Op::Chr, Val::I64(x)) => Val::U8((*x & 0xff) as u8), // int -> low byte
            (_, v) => return Err(format!("cannot {:?} {}", op, fmt_ty(&val_ty(v)))),
        })
    }
    match v {
        Val::Vec(c) => {
            if !is_simple(&c) {
                return Err("no elementwise arithmetic on union columns".into());
            }
            let vals: Vec<Val> = (0..c.len)
                .map(|i| scalar(op, &col_elem(&c, i)))
                .collect::<R<Vec<_>>>()?;
            Ok(Val::Vec(Rc::new(col_from_vals(vals)?)))
        }
        v => scalar(op, &v),
    }
}

// comparisons: total, return bit / [bit]
pub fn compare(op: Op, a: Val, b: Val) -> R<Val> {
    fn decide(op: Op, o: Ordering) -> bool {
        match op {
            Op::Eq => o == Ordering::Equal,
            Op::Ne => o != Ordering::Equal,
            Op::Lt => o == Ordering::Less,
            Op::Le => o != Ordering::Greater,
            Op::Gt => o == Ordering::Greater,
            Op::Ge => o != Ordering::Less,
            _ => unreachable!(),
        }
    }
    match (a, b) {
        (Val::Vec(ca), Val::Vec(cb)) => {
            if ca.len != cb.len {
                return Err(format!("length mismatch: {} vs {}", ca.len, cb.len));
            }
            let bits: Bits = (0..ca.len)
                .map(|i| decide(op, cmp_val(&col_elem(&ca, i), &col_elem(&cb, i))))
                .collect();
            Ok(Val::Vec(Rc::new(Col::simple(Payload::Bits(bits)))))
        }
        (Val::Vec(ca), s) => {
            let bits: Bits = (0..ca.len).map(|i| decide(op, cmp_val(&col_elem(&ca, i), &s))).collect();
            Ok(Val::Vec(Rc::new(Col::simple(Payload::Bits(bits)))))
        }
        (s, Val::Vec(cb)) => {
            let bits: Bits = (0..cb.len).map(|i| decide(op, cmp_val(&s, &col_elem(&cb, i)))).collect();
            Ok(Val::Vec(Rc::new(Col::simple(Payload::Bits(bits)))))
        }
        (a, b) => Ok(Val::Bit(decide(op, cmp_val(&a, &b)))),
    }
}

// and/or/not on bit / [bit]
pub fn boolean(op: Op, args: &[Val]) -> R<Val> {
    fn as_bits(v: &Val) -> Option<(usize, &Bits)> {
        if let Val::Vec(c) = v {
            if let Payload::Bits(b) = &c.cases[0] {
                if c.sel.is_none() && c.present.is_none() {
                    return Some((c.len, b));
                }
            }
        }
        None
    }
    match (op, args) {
        (Op::Not, [Val::Bit(x)]) => Ok(Val::Bit(!x)),
        (Op::Not, [v]) => {
            let (n, b) = as_bits(v).ok_or("not: expected bit or [bit]")?;
            let mut out = b.clone();
            out.not_inplace();
            let _ = n;
            Ok(Val::Vec(Rc::new(Col::simple(Payload::Bits(out)))))
        }
        (_, [Val::Bit(x), Val::Bit(y)]) => Ok(Val::Bit(if op == Op::And { *x && *y } else { *x || *y })),
        (_, [a, b]) => {
            let bits = |v: &Val, n: usize| -> R<Bits> {
                match v {
                    Val::Bit(x) => Ok(Bits::new(n, *x)),
                    _ => as_bits(v).map(|(_, b)| b.clone()).ok_or_else(|| "expected bit or [bit]".to_string()),
                }
            };
            let n = as_bits(a).or(as_bits(b)).map(|(n, _)| n).ok_or("expected [bit]")?;
            if let (Some((la, _)), Some((lb, _))) = (as_bits(a), as_bits(b)) {
                if la != lb {
                    return Err(format!("length mismatch: {} vs {}", la, lb));
                }
            }
            let mut x = bits(a, n)?;
            let y = bits(b, n)?;
            let yw: Vec<u64> = y.words().to_vec();
            for (i, yi) in yw.iter().enumerate() {
                if op == Op::And {
                    x.and_word(i, *yi);
                } else {
                    x.or_word(i, *yi);
                }
            }
            Ok(Val::Vec(Rc::new(Col::simple(Payload::Bits(x)))))
        }
        _ => Err("bad boolean operands".into()),
    }
}

// ---------- indexing ----------

pub fn index(target: &Val, ix: &Val) -> R<Val> {
    match target {
        Val::Vec(c) => index_col(c, ix).map(|c| Val::Vec(Rc::new(c))),
        Val::Tab(t) => {
            let mut out = Tab::default();
            let mut rowlen = None;
            for ((k, v), d) in t.keys.iter().zip(&t.vals).zip(&t.docs) {
                match v {
                    Val::Vec(c) if *rowlen.get_or_insert(c.len) == c.len => {
                        out.bind(k.clone(), Val::Vec(Rc::new(index_col(c, ix)?)), d.clone())
                    }
                    _ => return Err("row selection needs a tab of equal-length vecs".into()),
                }
            }
            Ok(Val::Tab(Rc::new(out)))
        }
        _ => Err("only vecs and tabs can be indexed".into()),
    }
}

// ---------- string ops on [u8] ----------
// Strings are [u8] (real vectors), so len / cat / index / grade already work
// via the generic vector ops. These are the string-specific ones.

fn as_u8s(v: &Val) -> R<Vec<u8>> {
    match v {
        Val::Vec(c) if is_u8_col(c) => Ok(col_bytes(c)),
        _ => Err("expected a string ([u8])".into()),
    }
}
fn u8s_val(b: &[u8]) -> Val {
    Val::Vec(Rc::new(Col::u8s(b)))
}

// Byte offset of the first occurrence of `needle` in `hay`, else nil. An empty
// needle matches at 0.
pub fn find(hay: &Val, needle: &Val) -> R<Val> {
    let (h, n) = (as_u8s(hay)?, as_u8s(needle)?);
    if n.is_empty() {
        return Ok(Val::I64(0));
    }
    Ok(match h.windows(n.len()).position(|w| w == &n[..]) {
        Some(i) => Val::I64(i as i64),
        None => Val::Nil,
    })
}

pub fn split(s: &Val, sep: &Val) -> R<Val> {
    let (h, d) = (as_u8s(s)?, as_u8s(sep)?);
    if d.is_empty() {
        return Err("split: empty separator".into());
    }
    let mut parts: Vec<Val> = Vec::new();
    let mut start = 0;
    let mut i = 0;
    while i + d.len() <= h.len() {
        if h[i..i + d.len()] == d[..] {
            parts.push(u8s_val(&h[start..i]));
            i += d.len();
            start = i;
        } else {
            i += 1;
        }
    }
    parts.push(u8s_val(&h[start..]));
    Ok(Val::Vec(Rc::new(col_from_vals(parts)?)))
}

pub fn join(sep: &Val, parts: &Val) -> R<Val> {
    let d = as_u8s(sep)?;
    let Val::Vec(parts) = parts else {
        return Err("join needs (str, [str])".into());
    };
    let mut out: Vec<u8> = Vec::new();
    for i in 0..parts.len {
        if i > 0 {
            out.extend_from_slice(&d);
        }
        out.extend_from_slice(&as_u8s(&col_elem(parts, i))?);
    }
    Ok(u8s_val(&out))
}

fn index_col(c: &Col, ix: &Val) -> R<Col> {
    let picks: Vec<usize> = match ix {
        Val::Vec(icol) => match (&icol.cases[0], icol.sel.is_none()) {
            (Payload::Bits(b), true) => {
                if icol.len != c.len {
                    return Err(format!("mask length {} vs vec length {}", icol.len, c.len));
                }
                (0..icol.len)
                    .filter(|i| b.get(*i) && icol.present.as_ref().is_none_or(|p| p.get(*i)))
                    .collect()
            }
            (Payload::I64s(v), true) => {
                if icol.present.is_some() {
                    return Err("index vector may not contain nil".into());
                }
                v.iter()
                    .map(|i| {
                        if *i < 0 || *i as usize >= c.len {
                            Err(format!("index {} out of bounds for length {}", i, c.len))
                        } else {
                            Ok(*i as usize)
                        }
                    })
                    .collect::<R<Vec<_>>>()?
            }
            _ => return Err("index must be [i64] or [bit]".into()),
        },
        _ => return Err("index must be [i64] or [bit]".into()),
    };
    let vals: Vec<Val> = picks.iter().map(|i| col_elem(c, *i)).collect();
    let mut out = col_from_vals(vals)?;
    // preserve the column's static element type (case order, nil admission)
    out = coerce_col(&out, &col_ty(c))?;
    Ok(out)
}

// ---------- aggregates & higher-order ----------

pub fn sum(c: &Col) -> R<Val> {
    if !is_simple(c) {
        return Err("sum needs a numeric or bit vec".into());
    }
    match &c.cases[0] {
        Payload::Bits(b) => Ok(Val::I64(
            (0..c.len)
                .filter(|i| c.present.as_ref().is_none_or(|p| p.get(*i)) && b.get(*i))
                .count() as i64,
        )),
        Payload::I64s(v) => {
            let mut acc: i64 = 0;
            for i in 0..c.len {
                if c.present.as_ref().is_none_or(|p| p.get(i)) {
                    acc = acc.wrapping_add(v[i]);
                }
            }
            Ok(Val::I64(acc))
        }
        Payload::F64s(v) => {
            let mut acc = 0.0;
            for i in 0..c.len {
                if c.present.as_ref().is_none_or(|p| p.get(i)) {
                    acc += v[i];
                }
            }
            Ok(Val::F64(canon_f64(acc)))
        }
        _ => Err("sum needs a numeric or bit vec".into()),
    }
}

pub fn minmax(c: &Col, want_min: bool) -> R<Val> {
    let mut best: Option<Val> = None;
    for i in 0..c.len {
        let v = col_elem(c, i);
        if v == Val::Nil {
            continue;
        }
        best = Some(match best {
            None => v,
            Some(b) => {
                let o = cmp_val(&v, &b);
                if (want_min && o == Ordering::Less) || (!want_min && o == Ordering::Greater) {
                    v
                } else {
                    b
                }
            }
        });
    }
    Ok(best.unwrap_or(Val::Nil))
}

pub fn grade(c: &Col) -> Val {
    let mut ix: Vec<i64> = (0..c.len as i64).collect();
    ix.sort_by(|a, b| cmp_val(&col_elem(c, *a as usize), &col_elem(c, *b as usize)));
    Val::Vec(Rc::new(Col::simple(Payload::I64s(ix))))
}

pub fn iota(n: i64) -> R<Val> {
    if n < 0 {
        return Err("iota of negative length".into());
    }
    Ok(Val::Vec(Rc::new(Col::simple(Payload::I64s((0..n).collect())))))
}

pub fn isnil(v: &Val) -> Val {
    match v {
        Val::Vec(c) => {
            let bits: Bits = (0..c.len)
                .map(|i| c.present.as_ref().is_some_and(|p| !p.get(i)))
                .collect();
            Val::Vec(Rc::new(Col::simple(Payload::Bits(bits))))
        }
        Val::Nil => Val::Bit(true),
        _ => Val::Bit(false),
    }
}

pub fn cat(a: &Val, b: &Val) -> R<Val> {
    match (a, b) {
        (Val::Vec(x), Val::Vec(y)) => {
            let vals: Vec<Val> = (0..x.len)
                .map(|i| col_elem(x, i))
                .chain((0..y.len).map(|i| col_elem(y, i)))
                .collect();
            let out = col_from_vals(vals)?;
            let union = crate::parse::union_of(vec![col_ty(x), col_ty(y)]);
            Ok(Val::Vec(Rc::new(coerce_col(&out, &union)?)))
        }
        _ => Err("cat needs two vecs".into()),
    }
}

// ---------- sequence analysis ----------
// Vectorized, general (any element type), composable: the four mask-producers
// pair with which/sum/and/or/not; the two [[T]]-producers pair with map.

fn bit_col(bits: Bits) -> Val {
    Val::Vec(Rc::new(Col::simple(Payload::Bits(bits))))
}

// mask over v: is each element equal (total order) to some element of `set`?
pub fn member(set: &Val, v: &Val) -> R<Val> {
    let s = as_vec(set, "member")?;
    let c = as_vec(v, "member")?;
    let elems: Vec<Val> = (0..s.len).map(|i| col_elem(s, i)).collect();
    let bits: Bits = (0..c.len)
        .map(|i| {
            let e = col_elem(c, i);
            elems.iter().any(|x| cmp_val(x, &e) == Ordering::Equal)
        })
        .collect();
    Ok(bit_col(bits))
}

// mask over hay: does `needle` occur as a contiguous subsequence starting here?
// (the all-positions generalization of `find`; empty needle matches everywhere)
pub fn matches(needle: &Val, hay: &Val) -> R<Val> {
    let n = as_vec(needle, "matches")?;
    let h = as_vec(hay, "matches")?;
    let pat: Vec<Val> = (0..n.len).map(|i| col_elem(n, i)).collect();
    let m = pat.len();
    let bits: Bits = (0..h.len)
        .map(|i| {
            i + m <= h.len
                && pat.iter().enumerate().all(|(j, p)| cmp_val(p, &col_elem(h, i + j)) == Ordering::Equal)
        })
        .collect();
    Ok(bit_col(bits))
}

// mask: run-start boundaries — index 0, and each i where v[i] != v[i-1].
pub fn runs(v: &Val) -> R<Val> {
    let c = as_vec(v, "runs")?;
    let bits: Bits = (0..c.len)
        .map(|i| i == 0 || cmp_val(&col_elem(c, i), &col_elem(c, i - 1)) != Ordering::Equal)
        .collect();
    Ok(bit_col(bits))
}

// cut v into segments: a new segment begins at index 0 and at each set bit of
// `starts` (lossless — the segments concatenate back to v).
pub fn partition(starts: &Val, v: &Val) -> R<Val> {
    let m = as_vec(starts, "partition")?;
    let c = as_vec(v, "partition")?;
    if m.len != c.len {
        return Err("partition: mask and vector must be the same length".into());
    }
    let mut segs: Vec<Val> = Vec::new();
    let mut cur: Vec<Val> = Vec::new();
    for i in 0..c.len {
        if i > 0 && col_elem(m, i) == Val::Bit(true) {
            segs.push(from_elems(std::mem::take(&mut cur))?);
        }
        cur.push(col_elem(c, i));
    }
    if c.len > 0 {
        segs.push(from_elems(cur)?);
    }
    from_elems(segs)
}

// all overlapping length-k contiguous sub-vectors (len(v)-k+1 of them).
pub fn windows(k: i64, v: &Val) -> R<Val> {
    let c = as_vec(v, "windows")?;
    if k < 1 {
        return Err("windows: k must be >= 1".into());
    }
    let k = k as usize;
    let mut ws: Vec<Val> = Vec::new();
    if k <= c.len {
        for i in 0..=(c.len - k) {
            ws.push(from_elems((i..i + k).map(|j| col_elem(c, j)).collect())?);
        }
    }
    from_elems(ws)
}

fn as_vec<'a>(v: &'a Val, who: &str) -> R<&'a Col> {
    match v {
        Val::Vec(c) => Ok(c),
        _ => Err(format!("{who} needs a vec")),
    }
}
fn from_elems(vals: Vec<Val>) -> R<Val> {
    col_from_vals(vals).map(|c| Val::Vec(Rc::new(c)))
}
fn present(c: &Col, i: usize) -> bool {
    c.present.as_ref().is_none_or(|p| p.get(i))
}

pub fn rev(v: &Val) -> R<Val> {
    let c = as_vec(v, "rev")?;
    from_elems((0..c.len).rev().map(|i| col_elem(c, i)).collect())
}

// take/drop count from the front; the count is clamped to [0, len].
pub fn take(n: i64, v: &Val) -> R<Val> {
    let c = as_vec(v, "take")?;
    let k = n.clamp(0, c.len as i64) as usize;
    slice(c, (0..k).map(|i| col_elem(c, i)).collect())
}
pub fn drop(n: i64, v: &Val) -> R<Val> {
    let c = as_vec(v, "drop")?;
    let k = n.clamp(0, c.len as i64) as usize;
    slice(c, (k..c.len).map(|i| col_elem(c, i)).collect())
}

// Build a vector of the given element type, so an empty result still carries
// its type (an empty slice of a [u8] is a [u8], not an untyped empty column).
fn slice_of(ty: &Ty, vals: Vec<Val>) -> R<Val> {
    Ok(Val::Vec(Rc::new(coerce_col(&col_from_vals(vals)?, ty)?)))
}
fn slice(c: &Col, vals: Vec<Val>) -> R<Val> {
    slice_of(&col_ty(c), vals)
}

// element at a scalar index (the scalar counterpart of gather `v[idxs]`).
pub fn at(v: &Val, i: i64) -> R<Val> {
    let c = as_vec(v, "at")?;
    if i < 0 || i as usize >= c.len {
        return Err(format!("at: index {} out of bounds for length {}", i, c.len));
    }
    Ok(col_elem(c, i as usize))
}

// n copies of a scalar, as a typed vector (the vector-model constant).
pub fn rep(n: i64, x: &Val) -> R<Val> {
    if n < 0 {
        return Err("rep of negative length".into());
    }
    slice_of(&val_ty(x), (0..n).map(|_| x.clone()).collect())
}

// `base` with base[idx[k]] := vals[k] for each k (later writes win); `vals`
// may be a scalar, broadcast to every index. The vectorized indexed amend.
pub fn scatter(base: &Val, idx: &Val, vals: &Val) -> R<Val> {
    let bc = as_vec(base, "scatter")?;
    let ic = as_vec(idx, "scatter")?;
    if let Val::Vec(vc) = vals {
        if vc.len != ic.len {
            return Err(format!("scatter: {} indices but {} values", ic.len, vc.len));
        }
    }
    let mut out: Vec<Val> = (0..bc.len).map(|i| col_elem(bc, i)).collect();
    for k in 0..ic.len {
        let j = match col_elem(ic, k) {
            Val::I64(j) => j,
            _ => return Err("scatter indices must be [i64]".into()),
        };
        if j < 0 || j as usize >= bc.len {
            return Err(format!("scatter: index {} out of bounds for length {}", j, bc.len));
        }
        out[j as usize] = match vals {
            Val::Vec(vc) => col_elem(vc, k),
            scalar => scalar.clone(),
        };
    }
    slice_of(&col_ty(bc), out)
}

// shift by k with a fill: out[i] = v[i+k] when in range, else `fill`. Positive k
// looks to the right (a left shift), negative to the left. A stencil primitive.
pub fn shift(v: &Val, k: i64, fill: &Val) -> R<Val> {
    let c = as_vec(v, "shift")?;
    let n = c.len as i64;
    let vals: Vec<Val> = (0..n)
        .map(|i| {
            let j = i + k;
            if j >= 0 && j < n { col_elem(c, j as usize) } else { fill.clone() }
        })
        .collect();
    slice_of(&col_ty(c), vals)
}

// prefix scan of a numeric vector: sums([1,2,3])=[1,3,6], prods([1,2,3])=[1,2,6].
fn prefix(v: &Val, who: &str, id: i64, idf: f64, comb: fn(i64, i64) -> i64, combf: fn(f64, f64) -> f64) -> R<Val> {
    let c = as_vec(v, who)?;
    if !is_simple(c) {
        return Err(format!("{who} needs a numeric vec"));
    }
    match &c.cases[0] {
        Payload::I64s(_) => {
            let mut acc = id;
            let out: Vec<i64> = (0..c.len)
                .map(|i| {
                    if let Val::I64(x) = col_elem(c, i) {
                        acc = comb(acc, x);
                    }
                    acc
                })
                .collect();
            Ok(Val::Vec(Rc::new(Col::simple(Payload::I64s(out)))))
        }
        Payload::F64s(_) => {
            let mut acc = idf;
            let out: Vec<f64> = (0..c.len)
                .map(|i| {
                    if let Val::F64(x) = col_elem(c, i) {
                        acc = combf(acc, x);
                    }
                    canon_f64(acc)
                })
                .collect();
            Ok(Val::Vec(Rc::new(Col::simple(Payload::F64s(out)))))
        }
        _ => Err(format!("{who} needs a numeric vec")),
    }
}
pub fn sums(v: &Val) -> R<Val> {
    prefix(v, "sums", 0, 0.0, i64::wrapping_add, |a, b| a + b)
}
pub fn prods(v: &Val) -> R<Val> {
    prefix(v, "prods", 1, 1.0, i64::wrapping_mul, |a, b| a * b)
}

pub fn first(v: &Val) -> R<Val> {
    let c = as_vec(v, "first")?;
    (c.len > 0).then(|| col_elem(c, 0)).ok_or_else(|| "first of empty vec".into())
}
pub fn last(v: &Val) -> R<Val> {
    let c = as_vec(v, "last")?;
    (c.len > 0).then(|| col_elem(c, c.len - 1)).ok_or_else(|| "last of empty vec".into())
}

// indices where a mask is set (1b): `which([1b,0b,1b]) = [0, 2]`.
pub fn which(mask: &Val) -> R<Val> {
    let c = as_vec(mask, "which")?;
    let ix: Vec<i64> = (0..c.len).filter(|&i| col_elem(c, i) == Val::Bit(true)).map(|i| i as i64).collect();
    Ok(Val::Vec(Rc::new(Col::simple(Payload::I64s(ix)))))
}

// unique elements, first-appearance order (order-equality, as `=`).
pub fn distinct(v: &Val) -> R<Val> {
    let c = as_vec(v, "distinct")?;
    let mut kept: Vec<Val> = Vec::new();
    for i in 0..c.len {
        let e = col_elem(c, i);
        if !kept.iter().any(|k| cmp_val(k, &e) == Ordering::Equal) {
            kept.push(e);
        }
    }
    from_elems(kept)
}

// scalar membership: is `x` an element of `v`?
// `in(x, v)`: does the set `v` contain the scalar `x`? (see `member` for the
// elementwise mask version)
pub fn contains(x: &Val, v: &Val) -> R<Val> {
    let c = as_vec(v, "in")?;
    Ok(Val::Bit((0..c.len).any(|i| cmp_val(&col_elem(c, i), x) == Ordering::Equal)))
}

pub fn all(v: &Val) -> R<Val> {
    let c = as_vec(v, "all")?;
    Ok(Val::Bit((0..c.len).all(|i| col_elem(c, i) == Val::Bit(true))))
}
pub fn any(v: &Val) -> R<Val> {
    let c = as_vec(v, "any")?;
    Ok(Val::Bit((0..c.len).any(|i| col_elem(c, i) == Val::Bit(true))))
}

pub fn prod(c: &Col) -> R<Val> {
    if !is_simple(c) {
        return Err("prod needs a numeric vec".into());
    }
    match &c.cases[0] {
        Payload::I64s(v) => {
            let mut acc: i64 = 1;
            for i in 0..c.len {
                if present(c, i) {
                    acc = acc.wrapping_mul(v[i]);
                }
            }
            Ok(Val::I64(acc))
        }
        Payload::F64s(v) => {
            let mut acc = 1.0;
            for i in 0..c.len {
                if present(c, i) {
                    acc *= v[i];
                }
            }
            Ok(Val::F64(canon_f64(acc)))
        }
        _ => Err("prod needs a numeric vec".into()),
    }
}

pub fn group(t: &Rc<Tab>, key: &[u8]) -> R<Val> {
    let kcol = match t.get(key) {
        Some(Val::Vec(c)) => c.clone(),
        _ => return Err(format!("group: no vec column `{:?}`", Bytes::new(key))),
    };
    // distinct keys in first-appearance order
    let mut keys: Vec<Val> = Vec::new();
    let mut buckets: Vec<Vec<i64>> = Vec::new();
    for i in 0..kcol.len {
        let v = col_elem(&kcol, i);
        match keys.iter().position(|k| cmp_val(k, &v) == Ordering::Equal) {
            Some(j) => buckets[j].push(i as i64),
            None => {
                keys.push(v);
                buckets.push(vec![i as i64]);
            }
        }
    }
    let rows: Vec<Val> = buckets
        .into_iter()
        .map(|ix| {
            let ixv = Val::Vec(Rc::new(Col::simple(Payload::I64s(ix))));
            index(&Val::Tab(t.clone()), &ixv)
        })
        .collect::<R<Vec<_>>>()?;
    let mut out = Tab::default();
    let keycol = coerce_col(&col_from_vals(keys)?, &col_ty(&kcol))?;
    out.bind(Bytes::new(key), Val::Vec(Rc::new(keycol)), None);
    out.bind(Bytes::str("rows"), Val::Vec(Rc::new(col_from_vals(rows)?)), None);
    Ok(Val::Tab(Rc::new(out)))
}

// vectorized if: mask selects elementwise between t and e (broadcast scalars)
pub fn select(mask: &Col, t: Val, e: Val) -> R<Val> {
    let n = mask.len;
    let get = |v: &Val, i: usize| -> R<Val> {
        match v {
            Val::Vec(c) => {
                if c.len != n {
                    return Err(format!("length mismatch: {} vs {}", c.len, n));
                }
                Ok(col_elem(c, i))
            }
            s => Ok(s.clone()),
        }
    };
    let (None, Payload::Bits(b)) = (&mask.sel, &mask.cases[0]) else {
        return Err("if condition must be bit or [bit]".into());
    };
    let vals: Vec<Val> = (0..n)
        .map(|i| {
            let on = b.get(i) && mask.present.as_ref().is_none_or(|p| p.get(i));
            get(if on { &t } else { &e }, i)
        })
        .collect::<R<Vec<_>>>()?;
    Ok(Val::Vec(Rc::new(col_from_vals(vals)?)))
}
