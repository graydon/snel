// One binary format for every value — hence for code, since code is tabs.
// Fixed-width buffers are written in 256-element chunks, each with a 1-byte
// encoding tag; the encoder picks the smallest. Also here: the fixed
// bijections type <-> value and AST <-> tab.

use crate::ast::{Ast, Node, Span, Ty};
use crate::value::{Bytes, Bits, Clo, Col, Payload, Sym, Tab, Val};
use std::rc::Rc;

pub type R<T> = Result<T, String>;

// ---------- value tags ----------
const T_NIL: u8 = 0;
const T_BIT0: u8 = 1;
const T_BIT1: u8 = 2;
const T_I64: u8 = 3;
const T_F64: u8 = 4;
const T_U8: u8 = 5;
const T_VEC: u8 = 6;
const T_TAB: u8 = 7;
const T_FUN: u8 = 8;
const T_PRIM: u8 = 9;

const CHUNK: usize = 256;

// ---------- encode ----------

pub fn encode_val(v: &Val, out: &mut Vec<u8>) {
    match v {
        Val::Nil => out.push(T_NIL),
        Val::Bit(false) => out.push(T_BIT0),
        Val::Bit(true) => out.push(T_BIT1),
        Val::I64(x) => {
            out.push(T_I64);
            out.extend_from_slice(&x.to_le_bytes());
        }
        Val::F64(x) => {
            out.push(T_F64);
            out.extend_from_slice(&x.to_bits().to_le_bytes());
        }
        Val::U8(b) => {
            out.push(T_U8);
            out.push(*b);
        }
        Val::Vec(c) => {
            out.push(T_VEC);
            encode_col(c, out);
        }
        Val::Tab(t) => {
            out.push(T_TAB);
            encode_tab(t, out);
        }
        Val::Fun(c) => {
            out.push(T_FUN);
            put_u32(c.params.len() as u32, out);
            for (x, t) in &c.params {
                put_bin(x, out);
                encode_val(&ty_to_val(t), out);
            }
            encode_val(&ty_to_val(&c.ret), out);
            encode_val(&ast_to_val(&c.body), out);
            encode_tab(&c.env, out);
        }
        Val::Prim(name) => {
            out.push(T_PRIM);
            put_bin(name, out);
        }
    }
}

fn put_u32(x: u32, out: &mut Vec<u8>) {
    out.extend_from_slice(&x.to_le_bytes());
}
fn put_bin(b: &Bytes, out: &mut Vec<u8>) {
    put_u32(b.bytes().len() as u32, out);
    out.extend_from_slice(b.bytes());
}

fn encode_tab(t: &Tab, out: &mut Vec<u8>) {
    put_u32(t.keys.len() as u32, out);
    for ((k, v), d) in t.keys.iter().zip(&t.vals).zip(&t.docs) {
        put_bin(k, out);
        match d {
            None => out.push(0),
            Some(doc) => {
                out.push(1);
                put_bin(doc, out);
            }
        }
        encode_val(v, out);
    }
}

fn encode_col(c: &Col, out: &mut Vec<u8>) {
    put_u32(c.len as u32, out);
    let mut flags = 0u8;
    if c.present.is_some() {
        flags |= 1;
    }
    if c.sel.is_some() {
        flags |= 2;
    }
    out.push(flags);
    out.push(c.cases.len() as u8);
    for p in &c.cases {
        out.push(p.kind());
    }
    if let Some(p) = &c.present {
        encode_bits(p, out);
    }
    if let Some(s) = &c.sel {
        encode_u8s(s, out);
    }
    for p in &c.cases {
        match p {
            Payload::Bits(b) => encode_bits(b, out),
            Payload::I64s(v) => encode_i64s(v, out),
            Payload::F64s(v) => encode_f64s(v, out),
            Payload::U8s(b) => encode_u8s(b.bytes(), out), // byte-packed chunks
            Payload::Vecs(v) => v.iter().for_each(|sub| encode_col(sub, out)),
            Payload::Tabs(v) => v.iter().for_each(|t| encode_tab(t, out)),
        }
    }
}

// bit chunks: 0=raw bytes (LSB-first, tail zeroed), 1=all zeros, 2=all ones
fn encode_bits(b: &Bits, out: &mut Vec<u8>) {
    let mut i = 0;
    while i < b.len || (b.len == 0 && i == 0) {
        let n = (b.len - i).min(CHUNK);
        let slice: Vec<bool> = (i..i + n).map(|j| b.get(j)).collect();
        if slice.iter().all(|x| !*x) {
            out.push(1);
        } else if slice.iter().all(|x| *x) {
            out.push(2);
        } else {
            out.push(0);
            let mut bytes = vec![0u8; n.div_ceil(8)];
            for (j, x) in slice.iter().enumerate() {
                if *x {
                    bytes[j / 8] |= 1 << (j % 8);
                }
            }
            out.extend_from_slice(&bytes);
        }
        i += n;
        if b.len == 0 {
            break;
        }
    }
    if b.len == 0 {
        // emitted nothing above; zero-length bitmap has zero chunks
        out.pop();
    }
}

// u8 chunks: 0=raw, 1=rle(u16 nruns; runs of u8 len-1, u8 val)
fn encode_u8s(v: &[u8], out: &mut Vec<u8>) {
    for chunk in v.chunks(CHUNK) {
        let runs = rle_runs(chunk);
        let rle_size = 2 + runs.len() * 2;
        if rle_size < chunk.len() {
            out.push(1);
            out.extend_from_slice(&(runs.len() as u16).to_le_bytes());
            for (len, val) in runs {
                out.push(len - 1);
                out.push(val);
            }
        } else {
            out.push(0);
            out.extend_from_slice(chunk);
        }
    }
}

fn rle_runs<T: Copy + PartialEq>(chunk: &[T]) -> Vec<(u8, T)> {
    let mut runs: Vec<(u8, T)> = Vec::new();
    for x in chunk {
        match runs.last_mut() {
            Some((n, v)) if *v == *x && *n < 255 => *n += 1,
            _ => runs.push((1, *x)),
        }
    }
    runs
}

fn zigzag(x: i64) -> u64 {
    ((x << 1) ^ (x >> 63)) as u64
}
fn unzigzag(x: u64) -> i64 {
    ((x >> 1) as i64) ^ -((x & 1) as i64)
}

// i64 chunks: 0=raw (8B LE each), 1=rle (u16 nruns; u8 len-1, i64),
// 2=packed (u8 width; zigzag LE truncated to width bytes; width 0 = all 0)
fn encode_i64s(v: &[i64], out: &mut Vec<u8>) {
    for chunk in v.chunks(CHUNK) {
        let raw = chunk.len() * 8;
        let runs = rle_runs(chunk);
        let rle = 2 + runs.len() * 9;
        let width = chunk
            .iter()
            .map(|x| {
                let z = zigzag(*x);
                (8 - z.leading_zeros() / 8) as usize
            })
            .max()
            .unwrap_or(0);
        let packed = 1 + chunk.len() * width;
        let best = raw.min(rle).min(packed);
        if best == raw {
            out.push(0);
            chunk.iter().for_each(|x| out.extend_from_slice(&x.to_le_bytes()));
        } else if best == rle {
            out.push(1);
            out.extend_from_slice(&(runs.len() as u16).to_le_bytes());
            for (len, val) in runs {
                out.push(len - 1);
                out.extend_from_slice(&val.to_le_bytes());
            }
        } else {
            out.push(2);
            out.push(width as u8);
            for x in chunk {
                out.extend_from_slice(&zigzag(*x).to_le_bytes()[..width]);
            }
        }
    }
}

// f64 chunks: 0=raw, 1=rle (by bit pattern)
fn encode_f64s(v: &[f64], out: &mut Vec<u8>) {
    for chunk in v.chunks(CHUNK) {
        let bits: Vec<u64> = chunk.iter().map(|x| x.to_bits()).collect();
        let runs = rle_runs(&bits);
        let rle = 2 + runs.len() * 9;
        if rle < chunk.len() * 8 {
            out.push(1);
            out.extend_from_slice(&(runs.len() as u16).to_le_bytes());
            for (len, val) in runs {
                out.push(len - 1);
                out.extend_from_slice(&val.to_le_bytes());
            }
        } else {
            out.push(0);
            bits.iter().for_each(|x| out.extend_from_slice(&x.to_le_bytes()));
        }
    }
}

// ---------- decode ----------

pub struct Rd<'a> {
    pub b: &'a [u8],
    pub i: usize,
}

impl<'a> Rd<'a> {
    pub fn new(b: &'a [u8]) -> Rd<'a> {
        Rd { b, i: 0 }
    }
    fn u8(&mut self) -> R<u8> {
        let x = *self.b.get(self.i).ok_or("truncated")?;
        self.i += 1;
        Ok(x)
    }
    fn take(&mut self, n: usize) -> R<&'a [u8]> {
        let s = self.b.get(self.i..self.i + n).ok_or("truncated")?;
        self.i += n;
        Ok(s)
    }
    fn u16(&mut self) -> R<u16> {
        Ok(u16::from_le_bytes(self.take(2)?.try_into().unwrap()))
    }
    fn u32(&mut self) -> R<u32> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }
    fn i64(&mut self) -> R<i64> {
        Ok(i64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }
    fn bin(&mut self) -> R<Bytes> {
        let n = self.u32()? as usize;
        Ok(Bytes::new(self.take(n)?))
    }
}

pub fn decode_val(r: &mut Rd) -> R<Val> {
    match r.u8()? {
        T_NIL => Ok(Val::Nil),
        T_BIT0 => Ok(Val::Bit(false)),
        T_BIT1 => Ok(Val::Bit(true)),
        T_I64 => Ok(Val::I64(r.i64()?)),
        T_F64 => Ok(Val::F64(crate::print::canon_f64(f64::from_bits(r.i64()? as u64)))),
        T_U8 => Ok(Val::U8(r.u8()?)),
        T_VEC => Ok(Val::Vec(Rc::new(decode_col(r)?))),
        T_TAB => Ok(Val::Tab(Rc::new(decode_tab(r)?))),
        T_FUN => {
            let np = r.u32()? as usize;
            let mut params = Vec::with_capacity(np);
            for _ in 0..np {
                let x = r.bin()?;
                let t = val_to_ty(&decode_val(r)?).ok_or("bad param type")?;
                params.push((x, t));
            }
            let ret = val_to_ty(&decode_val(r)?).ok_or("bad return type")?;
            let body = val_to_ast(&decode_val(r)?)?;
            let env = decode_tab(r)?;
            Ok(Val::Fun(Rc::new(Clo { params, ret, body: Rc::new(body), env: Rc::new(env) })))
        }
        T_PRIM => Ok(Val::Prim(r.bin()?)),
        t => Err(format!("bad value tag {}", t)),
    }
}

fn decode_tab(r: &mut Rd) -> R<Tab> {
    let n = r.u32()? as usize;
    let mut t = Tab::default();
    for _ in 0..n {
        let k = r.bin()?;
        let doc = if r.u8()? == 1 { Some(r.bin()?) } else { None };
        let v = decode_val(r)?;
        t.bind(k, v, doc);
    }
    Ok(t)
}

fn decode_col(r: &mut Rd) -> R<Col> {
    let len = r.u32()? as usize;
    let flags = r.u8()?;
    let ncases = r.u8()? as usize;
    if ncases == 0 || ncases > 6 {
        return Err("bad case count".into());
    }
    let kinds: Vec<u8> = (0..ncases).map(|_| r.u8()).collect::<R<Vec<_>>>()?;
    let present = if flags & 1 != 0 { Some(decode_bits(r, len)?) } else { None };
    let sel = if flags & 2 != 0 { Some(decode_u8s(r, len)?) } else { None };
    let mut cases = Vec::with_capacity(ncases);
    for k in kinds {
        cases.push(match k {
            1 => Payload::Bits(decode_bits(r, len)?),
            2 => Payload::I64s(decode_i64s(r, len)?),
            3 => Payload::F64s(decode_f64s(r, len)?),
            4 => Payload::U8s(Bytes::new(&decode_u8s(r, len)?)),
            5 => Payload::Vecs((0..len).map(|_| decode_col(r).map(Rc::new)).collect::<R<Vec<_>>>()?),
            6 => Payload::Tabs((0..len).map(|_| decode_tab(r).map(Rc::new)).collect::<R<Vec<_>>>()?),
            k => return Err(format!("bad payload kind {}", k)),
        });
    }
    if let Some(s) = &sel {
        if s.iter().any(|c| *c as usize >= ncases) {
            return Err("selector out of range".into());
        }
    }
    Ok(Col { len, present, sel, cases })
}

fn decode_bits(r: &mut Rd, len: usize) -> R<Bits> {
    let mut b = Bits::default();
    let mut i = 0;
    while i < len {
        let n = (len - i).min(CHUNK);
        match r.u8()? {
            1 => (0..n).for_each(|_| b.push(false)),
            2 => (0..n).for_each(|_| b.push(true)),
            0 => {
                let bytes = r.take(n.div_ceil(8))?;
                for j in 0..n {
                    b.push(bytes[j / 8] >> (j % 8) & 1 != 0);
                }
            }
            t => return Err(format!("bad bit chunk tag {}", t)),
        }
        i += n;
    }
    Ok(b)
}

fn decode_u8s(r: &mut Rd, len: usize) -> R<Vec<u8>> {
    let mut out = Vec::with_capacity(len);
    while out.len() < len {
        let n = (len - out.len()).min(CHUNK);
        match r.u8()? {
            0 => out.extend_from_slice(r.take(n)?),
            1 => {
                let nruns = r.u16()? as usize;
                for _ in 0..nruns {
                    let rl = r.u8()? as usize + 1;
                    let v = r.u8()?;
                    out.extend(std::iter::repeat_n(v, rl));
                }
            }
            t => return Err(format!("bad u8 chunk tag {}", t)),
        }
    }
    if out.len() != len {
        return Err("chunk length mismatch".into());
    }
    Ok(out)
}

fn decode_i64s(r: &mut Rd, len: usize) -> R<Vec<i64>> {
    let mut out = Vec::with_capacity(len);
    while out.len() < len {
        let n = (len - out.len()).min(CHUNK);
        match r.u8()? {
            0 => {
                for _ in 0..n {
                    out.push(r.i64()?);
                }
            }
            1 => {
                let nruns = r.u16()? as usize;
                for _ in 0..nruns {
                    let rl = r.u8()? as usize + 1;
                    let v = r.i64()?;
                    out.extend(std::iter::repeat_n(v, rl));
                }
            }
            2 => {
                let w = r.u8()? as usize;
                if w > 8 {
                    return Err("bad pack width".into());
                }
                for _ in 0..n {
                    let mut buf = [0u8; 8];
                    buf[..w].copy_from_slice(r.take(w)?);
                    out.push(unzigzag(u64::from_le_bytes(buf)));
                }
            }
            t => return Err(format!("bad i64 chunk tag {}", t)),
        }
    }
    if out.len() != len {
        return Err("chunk length mismatch".into());
    }
    Ok(out)
}

fn decode_f64s(r: &mut Rd, len: usize) -> R<Vec<f64>> {
    let mut out = Vec::with_capacity(len);
    while out.len() < len {
        let n = (len - out.len()).min(CHUNK);
        match r.u8()? {
            0 => {
                for _ in 0..n {
                    out.push(f64::from_bits(r.i64()? as u64));
                }
            }
            1 => {
                let nruns = r.u16()? as usize;
                for _ in 0..nruns {
                    let rl = r.u8()? as usize + 1;
                    let v = f64::from_bits(r.i64()? as u64);
                    out.extend(std::iter::repeat_n(v, rl));
                }
            }
            t => return Err(format!("bad f64 chunk tag {}", t)),
        }
    }
    if out.len() != len {
        return Err("chunk length mismatch".into());
    }
    Ok(out)
}

// ---------- identifiers as [u8] strings ----------
// The AST-as-tab encoding is all data now: identifiers (node kinds, names,
// type names) are [u8] strings, not a distinct sym kind.

pub fn vstr(b: &[u8]) -> Val {
    Val::Vec(Rc::new(Col::u8s(b)))
}
fn str_bytes(v: &Val) -> Option<Bytes> {
    match v {
        Val::Vec(c) if crate::ops::is_u8_col(c) => Some(Bytes::new(&crate::ops::col_bytes(c))),
        _ => None,
    }
}

// ---------- type <-> value ----------

// Types encode as values: prims and named types as strings; every compound as
// a tagged tab. Uniform tagging avoids the vec-in-vec that `[union]` would need.
pub fn ty_to_val(t: &Ty) -> Val {
    let tagged = |kind: &str, fields: Vec<(&str, Val)>| {
        let mut t = tag(kind);
        for (k, v) in fields {
            t.bind(Bytes::str(k), v, None);
        }
        Val::Tab(Rc::new(t))
    };
    match t {
        Ty::Nil => vstr(b"nil"),
        Ty::Bit => vstr(b"bit"),
        Ty::I64 => vstr(b"i64"),
        Ty::F64 => vstr(b"f64"),
        Ty::U8 => vstr(b"u8"),
        Ty::Name(n) => vstr(n.bytes()),
        Ty::Vec(t) => tagged("vec_t", vec![("e", ty_to_val(t))]),
        Ty::Union(ts) => tagged("union_t", vec![("e", vec_of(ts.iter().map(ty_to_val).collect()))]),
        Ty::Tab(fs) => tagged(
            "rec_t",
            vec![
                ("k", vec_of(fs.iter().map(|(k, _)| vstr(k.bytes())).collect())),
                ("t", vec_of(fs.iter().map(|(_, t)| ty_to_val(t)).collect())),
            ],
        ),
        Ty::Fun(args, r) => tagged(
            "fun_t",
            vec![("a", vec_of(args.iter().map(ty_to_val).collect())), ("r", ty_to_val(r))],
        ),
    }
}

fn vec_of(vals: Vec<Val>) -> Val {
    Val::Vec(Rc::new(crate::ops::col_from_vals(vals).expect("homogeneous encoding")))
}

fn vec_tys(v: &Val) -> Option<Vec<Ty>> {
    match v {
        Val::Vec(c) => (0..c.len).map(|i| val_to_ty(&crate::print::col_elem(c, i))).collect(),
        _ => None,
    }
}

pub fn val_to_ty(v: &Val) -> Option<Ty> {
    if let Some(b) = str_bytes(v) {
        return Some(match b.bytes() {
            b"nil" => Ty::Nil,
            b"bit" => Ty::Bit,
            b"i64" => Ty::I64,
            b"f64" => Ty::F64,
            b"u8" => Ty::U8,
            _ => Ty::Name(b.clone()),
        });
    }
    match v {
        Val::Tab(t) => match t.get(b"n").and_then(str_bytes) {
            Some(n) => match n.bytes() {
                b"vec_t" => Some(Ty::Vec(Box::new(val_to_ty(t.get(b"e")?)?))),
                b"union_t" => Some(Ty::Union(vec_tys(t.get(b"e")?)?)),
                b"fun_t" => Some(Ty::Fun(vec_tys(t.get(b"a")?)?, Box::new(val_to_ty(t.get(b"r")?)?))),
                b"rec_t" => {
                    let ks = match t.get(b"k")? {
                        Val::Vec(c) => (0..c.len)
                            .map(|i| str_bytes(&crate::print::col_elem(c, i)))
                            .collect::<Option<Vec<_>>>()?,
                        _ => return None,
                    };
                    let ts = vec_tys(t.get(b"t")?)?;
                    if ks.len() != ts.len() {
                        return None;
                    }
                    Some(Ty::Tab(ks.into_iter().zip(ts).collect()))
                }
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

// ---------- AST <-> tab ----------

fn tag(kind: &str) -> Tab {
    let mut t = Tab::default();
    t.bind(Bytes::str("n"), vstr(kind.as_bytes()), None);
    t
}

fn node_val(t: Tab) -> Val {
    Val::Tab(Rc::new(t))
}

pub fn ast_to_val(n: &Node) -> Val {
    let v = |x: &Node| ast_to_val(x);
    let nodes = |xs: &[Node]| vec_of(xs.iter().map(ast_to_val).collect());
    match &n.ast {
        Ast::Lit(x) => {
            let mut t = tag("lit");
            t.bind(Bytes::str("v"), x.clone(), None);
            node_val(t)
        }
        Ast::Var(x) => {
            let mut t = tag("var");
            t.bind(Bytes::str("x"), vstr(x.bytes()), None);
            node_val(t)
        }
        Ast::Proj(e, x) => {
            let mut t = tag("proj");
            t.bind(Bytes::str("e"), v(e), None);
            t.bind(Bytes::str("x"), vstr(x.bytes()), None);
            node_val(t)
        }
        Ast::Idx(e, i) => {
            let mut t = tag("idx");
            t.bind(Bytes::str("e"), v(e), None);
            t.bind(Bytes::str("i"), v(i), None);
            node_val(t)
        }
        Ast::App(f, args) => {
            let mut t = tag("app");
            t.bind(Bytes::str("f"), v(f), None);
            t.bind(Bytes::str("a"), nodes(args), None);
            node_val(t)
        }
        Ast::VecL(es) => {
            let mut t = tag("vec");
            t.bind(Bytes::str("e"), nodes(es), None);
            node_val(t)
        }
        Ast::TabL(fs) => {
            let mut t = tag("tab");
            t.bind(Bytes::str("k"), vec_of(fs.iter().map(|(k, _)| vstr(k.bytes())).collect()), None);
            t.bind(Bytes::str("e"), nodes(&fs.iter().map(|(_, e)| e.clone()).collect::<Vec<_>>()), None);
            node_val(t)
        }
        Ast::Fun { params, ret, body } => {
            let mut t = tag("fun");
            let ps: Vec<Val> = params
                .iter()
                .map(|(x, pt)| {
                    let mut p = Tab::default();
                    p.bind(Bytes::str("x"), vstr(x.bytes()), None);
                    p.bind(Bytes::str("t"), ty_to_val(pt), None);
                    Val::Tab(Rc::new(p))
                })
                .collect();
            t.bind(Bytes::str("p"), vec_of(ps), None);
            t.bind(Bytes::str("t"), ty_to_val(ret), None);
            t.bind(Bytes::str("e"), v(body), None);
            node_val(t)
        }
        Ast::If(c, a, b) => {
            let mut t = tag("if");
            t.bind(Bytes::str("c"), v(c), None);
            t.bind(Bytes::str("t"), v(a), None);
            t.bind(Bytes::str("e"), v(b), None);
            node_val(t)
        }
        Ast::Try(a, b) => {
            let mut t = tag("try");
            t.bind(Bytes::str("e1"), v(a), None);
            t.bind(Bytes::str("e2"), v(b), None);
            node_val(t)
        }
        Ast::Err(e) => {
            let mut t = tag("err");
            t.bind(Bytes::str("e"), v(e), None);
            node_val(t)
        }
        Ast::Is(e, ty) => {
            let mut t = tag("is");
            t.bind(Bytes::str("e"), v(e), None);
            t.bind(Bytes::str("t"), ty_to_val(ty), None);
            node_val(t)
        }
        Ast::As(e, ty) => {
            let mut t = tag("as");
            t.bind(Bytes::str("e"), v(e), None);
            t.bind(Bytes::str("t"), ty_to_val(ty), None);
            node_val(t)
        }
        Ast::Seq(ds) => {
            let mut t = tag("seq");
            t.bind(Bytes::str("d"), nodes(ds), None);
            node_val(t)
        }
        Ast::Let { x, ty, e, doc, public } => {
            let mut t = tag("let");
            t.bind(Bytes::str("x"), vstr(x.bytes()), None);
            if let Some(ty) = ty {
                t.bind(Bytes::str("t"), ty_to_val(ty), None);
            }
            t.bind(Bytes::str("e"), v(e), None);
            if let Some(d) = doc {
                t.bind(Bytes::str("doc"), vstr(d.bytes()), None);
            }
            if *public {
                t.bind(Bytes::str("pub"), Val::Bit(true), None);
            }
            node_val(t)
        }
        Ast::Typ { x, base, pred, doc, public } => {
            let mut t = tag("typ");
            t.bind(Bytes::str("x"), vstr(x.bytes()), None);
            t.bind(Bytes::str("t"), ty_to_val(base), None);
            t.bind(Bytes::str("p"), v(pred), None);
            if let Some(d) = doc {
                t.bind(Bytes::str("doc"), vstr(d.bytes()), None);
            }
            if *public {
                t.bind(Bytes::str("pub"), Val::Bit(true), None);
            }
            node_val(t)
        }
        Ast::Use { x, url, doc } => {
            let mut t = tag("use");
            t.bind(Bytes::str("x"), vstr(x.bytes()), None);
            if let Some(u) = url {
                t.bind(Bytes::str("url"), vstr(u.bytes()), None);
            }
            if let Some(d) = doc {
                t.bind(Bytes::str("doc"), vstr(d.bytes()), None);
            }
            node_val(t)
        }
    }
}

pub fn val_to_ast(v: &Val) -> R<Node> {
    let t = match v {
        Val::Tab(t) => t,
        _ => return Err("code node must be a tab".into()),
    };
    let kind = match t.get(b"n").and_then(str_bytes) {
        Some(b) => b,
        _ => return Err("code node needs field n".into()),
    };
    let get = |k: &[u8]| t.get(k).ok_or_else(|| format!("node `{:?}` missing field", kind));
    let node = |k: &[u8]| get(k).and_then(val_to_ast).map(Box::new);
    let sym = |k: &[u8]| -> R<Sym> { str_bytes(get(k)?).ok_or_else(|| "expected string field".into()) };
    let ty = |k: &[u8]| -> R<Ty> { val_to_ty(get(k)?).ok_or_else(|| "bad type encoding".into()) };
    let nodes = |k: &[u8]| -> R<Vec<Node>> {
        match get(k)? {
            Val::Vec(c) => (0..c.len).map(|i| val_to_ast(&crate::print::col_elem(c, i))).collect(),
            _ => Err("expected node vec".into()),
        }
    };
    let doc = t.get(b"doc").and_then(str_bytes);
    let public = matches!(t.get(b"pub"), Some(Val::Bit(true)));
    let ast = match kind.bytes() {
        b"lit" => Ast::Lit(get(b"v")?.clone()),
        b"var" => Ast::Var(sym(b"x")?),
        b"proj" => Ast::Proj(node(b"e")?, sym(b"x")?),
        b"idx" => Ast::Idx(node(b"e")?, node(b"i")?),
        b"app" => Ast::App(node(b"f")?, nodes(b"a")?),
        b"vec" => Ast::VecL(nodes(b"e")?),
        b"tab" => {
            let ks: Vec<Sym> = match get(b"k")? {
                Val::Vec(c) => (0..c.len)
                    .map(|i| str_bytes(&crate::print::col_elem(c, i)).ok_or("tab keys must be strings".to_string()))
                    .collect::<R<Vec<_>>>()?,
                _ => return Err("tab keys must be a vec".into()),
            };
            let es = nodes(b"e")?;
            if ks.len() != es.len() {
                return Err("tab node key/expr length mismatch".into());
            }
            Ast::TabL(ks.into_iter().zip(es).collect())
        }
        b"fun" => {
            let params: Vec<(Sym, Ty)> = match get(b"p")? {
                Val::Vec(c) => (0..c.len)
                    .map(|i| match crate::print::col_elem(c, i) {
                        Val::Tab(p) => {
                            let x = match p.get(b"x").and_then(str_bytes) {
                                Some(b) => b,
                                _ => return Err("bad param".to_string()),
                            };
                            let t = p.get(b"t").and_then(val_to_ty).ok_or("bad param type")?;
                            Ok((x, t))
                        }
                        _ => Err("bad param".to_string()),
                    })
                    .collect::<R<Vec<_>>>()?,
                _ => return Err("fun params must be a vec".into()),
            };
            Ast::Fun { params, ret: ty(b"t")?, body: Rc::new(*node(b"e")?) }
        }
        b"if" => Ast::If(node(b"c")?, node(b"t")?, node(b"e")?),
        b"try" => Ast::Try(node(b"e1")?, node(b"e2")?),
        b"err" => Ast::Err(node(b"e")?),
        b"is" => Ast::Is(node(b"e")?, ty(b"t")?),
        b"as" => Ast::As(node(b"e")?, ty(b"t")?),
        b"seq" => Ast::Seq(nodes(b"d")?),
        b"let" => Ast::Let {
            x: sym(b"x")?,
            ty: match t.get(b"t") {
                Some(v) => Some(val_to_ty(v).ok_or("bad type encoding")?),
                None => None,
            },
            e: node(b"e")?,
            doc,
            public,
        },
        b"typ" => Ast::Typ { x: sym(b"x")?, base: ty(b"t")?, pred: node(b"p")?, doc, public },
        b"use" => Ast::Use { x: sym(b"x")?, url: t.get(b"url").and_then(str_bytes), doc },
        k => return Err(format!("unknown node kind {:?}", Bytes::new(k))),
    };
    Ok(Node { ast, span: Span { lo: 0, hi: 0 } })
}
