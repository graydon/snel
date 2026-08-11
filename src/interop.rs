// Interop: JSON (nesting) and CSV (flat tables only). Mirrored by c/interop.c;
// both must produce byte-identical output.
//
// JSON mapping, in both directions:
//   nil <-> null            bit <-> true/false      i64/f64/u8 <-> number
//   [u8] <-> string         [T]  <-> array          tab <-> object
// A fun has no JSON form (an error). Reading a number yields i64 when it is
// integral and fits, else f64. Reading an array of mixed types yields a union
// column, exactly as the corresponding vector literal would.
//
// CSV is deliberately partial: it maps only a *flat* table — a tab whose fields
// are all equal-length vectors of scalars — because CSV has no way to nest.

use crate::ops::{col_bytes, col_from_vals, is_u8_col};
use crate::print::{col_elem, fmt_f64, parse_f64};
use crate::value::{Bytes, Col, Payload, Tab, Val};
use std::rc::Rc;

type R<T> = Result<T, String>;

fn u8s(b: &[u8]) -> Val {
    Val::Vec(Rc::new(Col::u8s(b)))
}

// ---------- JSON writing ----------

// The output is bytes, not a String: a `[u8]` is an arbitrary byte column, and
// the non-escaped bytes have to pass through *unchanged*. Pushing them into a
// String as `char` would re-encode each byte as its own code point, turning the
// UTF-8 of "café" into the UTF-8 of "cafÃ©".
fn write_json_str(bytes: &[u8], out: &mut Vec<u8>) {
    out.push(b'"');
    for &b in bytes {
        match b {
            b'"' => out.extend_from_slice(b"\\\""),
            b'\\' => out.extend_from_slice(b"\\\\"),
            b'\n' => out.extend_from_slice(b"\\n"),
            b'\t' => out.extend_from_slice(b"\\t"),
            b'\r' => out.extend_from_slice(b"\\r"),
            0x00..=0x1f => out.extend_from_slice(format!("\\u{:04x}", b).as_bytes()),
            _ => out.push(b), // utf-8 (and any other) bytes pass through
        }
    }
    out.push(b'"');
}

// A finite f64 renders in the language's canonical form; JSON has no inf/nan,
// so those are an error rather than a silently wrong `null`.
fn write_json_f64(x: f64, out: &mut Vec<u8>) -> R<()> {
    if !x.is_finite() {
        return Err("tojson: inf/nan have no JSON form".into());
    }
    out.extend_from_slice(fmt_f64(x).as_bytes());
    Ok(())
}

fn write_json(v: &Val, out: &mut Vec<u8>) -> R<()> {
    match v {
        Val::Nil => out.extend_from_slice(b"null"),
        Val::Bit(b) => out.extend_from_slice(if *b { b"true" as &[u8] } else { b"false" }),
        Val::I64(i) => out.extend_from_slice(i.to_string().as_bytes()),
        Val::U8(b) => out.extend_from_slice(b.to_string().as_bytes()),
        Val::F64(x) => write_json_f64(*x, out)?,
        Val::Vec(c) => {
            if is_u8_col(c) {
                write_json_str(&col_bytes(c), out);
            } else {
                out.push(b'[');
                for i in 0..c.len {
                    if i > 0 {
                        out.push(b',');
                    }
                    write_json(&col_elem(c, i), out)?;
                }
                out.push(b']');
            }
        }
        Val::Tab(t) => {
            out.push(b'{');
            for (i, (k, val)) in t.keys.iter().zip(&t.vals).enumerate() {
                if i > 0 {
                    out.push(b',');
                }
                write_json_str(k.bytes(), out);
                out.push(b':');
                write_json(val, out)?;
            }
            out.push(b'}');
        }
        Val::Fun(_) | Val::Prim(_) => return Err("tojson: a function has no JSON form".into()),
    }
    Ok(())
}

pub fn to_json(v: &Val) -> R<Val> {
    let mut s = Vec::new();
    write_json(v, &mut s)?;
    Ok(u8s(&s))
}

// ---------- JSON reading ----------

struct P<'a> {
    b: &'a [u8],
    i: usize,
}

impl<'a> P<'a> {
    fn ws(&mut self) {
        while self.i < self.b.len() && matches!(self.b[self.i], b' ' | b'\t' | b'\n' | b'\r') {
            self.i += 1;
        }
    }
    fn peek(&self) -> Option<u8> {
        self.b.get(self.i).copied()
    }
    fn lit(&mut self, s: &str) -> bool {
        if self.b[self.i..].starts_with(s.as_bytes()) {
            self.i += s.len();
            true
        } else {
            false
        }
    }
    fn string(&mut self) -> R<Vec<u8>> {
        self.i += 1; // opening quote
        let mut out = Vec::new();
        loop {
            let c = *self.b.get(self.i).ok_or("fromjson: unterminated string")?;
            self.i += 1;
            match c {
                b'"' => return Ok(out),
                b'\\' => {
                    let e = *self.b.get(self.i).ok_or("fromjson: bad escape")?;
                    self.i += 1;
                    match e {
                        b'"' => out.push(b'"'),
                        b'\\' => out.push(b'\\'),
                        b'/' => out.push(b'/'),
                        b'n' => out.push(b'\n'),
                        b't' => out.push(b'\t'),
                        b'r' => out.push(b'\r'),
                        b'b' => out.push(0x08),
                        b'f' => out.push(0x0c),
                        b'u' => {
                            let h = self
                                .b
                                .get(self.i..self.i + 4)
                                .and_then(|s| std::str::from_utf8(s).ok())
                                .and_then(|s| u32::from_str_radix(s, 16).ok())
                                .ok_or("fromjson: bad \\u escape")?;
                            self.i += 4;
                            // encode the code point as UTF-8 (lone surrogates -> U+FFFD)
                            let ch = char::from_u32(h).unwrap_or('\u{fffd}');
                            let mut buf = [0u8; 4];
                            out.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
                        }
                        _ => return Err("fromjson: bad escape".into()),
                    }
                }
                _ => out.push(c),
            }
        }
    }
    fn value(&mut self) -> R<Val> {
        self.ws();
        match self.peek().ok_or("fromjson: unexpected end of input")? {
            b'n' => {
                if self.lit("null") {
                    Ok(Val::Nil)
                } else {
                    Err("fromjson: expected null".into())
                }
            }
            b't' => {
                if self.lit("true") {
                    Ok(Val::Bit(true))
                } else {
                    Err("fromjson: expected true".into())
                }
            }
            b'f' => {
                if self.lit("false") {
                    Ok(Val::Bit(false))
                } else {
                    Err("fromjson: expected false".into())
                }
            }
            b'"' => Ok(u8s(&self.string()?)),
            b'[' => {
                self.i += 1;
                let mut items = Vec::new();
                self.ws();
                if self.peek() == Some(b']') {
                    self.i += 1;
                } else {
                    loop {
                        items.push(self.value()?);
                        self.ws();
                        match self.peek() {
                            Some(b',') => self.i += 1,
                            Some(b']') => {
                                self.i += 1;
                                break;
                            }
                            _ => return Err("fromjson: expected , or ] in array".into()),
                        }
                    }
                }
                col_from_vals(items).map(|c| Val::Vec(Rc::new(c)))
            }
            b'{' => {
                self.i += 1;
                let mut t = Tab::default();
                self.ws();
                if self.peek() == Some(b'}') {
                    self.i += 1;
                } else {
                    loop {
                        self.ws();
                        if self.peek() != Some(b'"') {
                            return Err("fromjson: expected a string key".into());
                        }
                        let k = self.string()?;
                        self.ws();
                        if self.peek() != Some(b':') {
                            return Err("fromjson: expected : after key".into());
                        }
                        self.i += 1;
                        let v = self.value()?;
                        t.bind(Bytes::new(&k), v, None);
                        self.ws();
                        match self.peek() {
                            Some(b',') => self.i += 1,
                            Some(b'}') => {
                                self.i += 1;
                                break;
                            }
                            _ => return Err("fromjson: expected , or } in object".into()),
                        }
                    }
                }
                Ok(Val::Tab(Rc::new(t)))
            }
            _ => self.number(),
        }
    }
    fn number(&mut self) -> R<Val> {
        let start = self.i;
        if self.peek() == Some(b'-') {
            self.i += 1;
        }
        let mut is_float = false;
        while let Some(c) = self.peek() {
            match c {
                b'0'..=b'9' => self.i += 1,
                b'.' | b'e' | b'E' | b'+' | b'-' => {
                    is_float = true;
                    self.i += 1;
                }
                _ => break,
            }
        }
        let text = std::str::from_utf8(&self.b[start..self.i])
            .map_err(|_| "fromjson: bad number".to_string())?;
        if text.is_empty() || text == "-" {
            return Err("fromjson: expected a value".into());
        }
        if !is_float {
            if let Ok(i) = text.parse::<i64>() {
                return Ok(Val::I64(i));
            }
        }
        parse_f64(text).map(Val::F64).ok_or_else(|| "fromjson: bad number".to_string())
    }
}

pub fn from_json(v: &Val) -> R<Val> {
    let bytes = match v {
        Val::Vec(c) if is_u8_col(c) => col_bytes(c),
        _ => return Err("fromjson needs a string ([u8])".into()),
    };
    let mut p = P { b: &bytes, i: 0 };
    let out = p.value()?;
    p.ws();
    if p.i != bytes.len() {
        return Err("fromjson: trailing input after the value".into());
    }
    Ok(out)
}

// ---------- CSV ----------
// Flat tables only: a tab whose fields are equal-length vectors of scalars.
// RFC4180-ish: `,` separates, `\r\n` or `\n` ends a record, a field is quoted
// when it contains a comma, quote, or newline, and `""` escapes a quote.

fn csv_field(v: &Val) -> R<String> {
    Ok(match v {
        Val::Nil => String::new(), // an empty field reads back as nil
        Val::Bit(b) => if *b { "true" } else { "false" }.into(),
        Val::I64(i) => i.to_string(),
        Val::U8(b) => b.to_string(),
        Val::F64(x) => {
            if !x.is_finite() {
                return Err("tocsv: inf/nan have no CSV form".into());
            }
            fmt_f64(*x)
        }
        Val::Vec(c) if is_u8_col(c) => String::from_utf8_lossy(&col_bytes(c)).into_owned(),
        _ => return Err("tocsv: fields must be scalars or strings (CSV cannot nest)".into()),
    })
}

fn csv_quote(s: &str, out: &mut String) {
    if s.contains([',', '"', '\n', '\r']) {
        out.push('"');
        for ch in s.chars() {
            if ch == '"' {
                out.push('"');
            }
            out.push(ch);
        }
        out.push('"');
    } else {
        out.push_str(s);
    }
}

pub fn to_csv(v: &Val) -> R<Val> {
    let t = match v {
        Val::Tab(t) => t,
        _ => return Err("tocsv needs a tab of equal-length vecs".into()),
    };
    let mut cols: Vec<&Rc<Col>> = Vec::new();
    for val in &t.vals {
        match val {
            Val::Vec(c) if !is_u8_col(c) => cols.push(c),
            // a [u8] field would be one string, not a column of rows
            _ => return Err("tocsv: every field must be a vec of scalars".into()),
        }
    }
    let rows = cols.first().map_or(0, |c| c.len);
    if cols.iter().any(|c| c.len != rows) {
        return Err("tocsv: all fields must have the same length".into());
    }
    let mut out = String::new();
    for (i, k) in t.keys.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        csv_quote(&String::from_utf8_lossy(k.bytes()), &mut out);
    }
    out.push('\n');
    for r in 0..rows {
        for (i, c) in cols.iter().enumerate() {
            if i > 0 {
                out.push(',');
            }
            csv_quote(&csv_field(&col_elem(c, r))?, &mut out);
        }
        out.push('\n');
    }
    Ok(u8s(out.as_bytes()))
}

// Split CSV text into records of fields, honoring quotes.
fn csv_records(b: &[u8]) -> R<Vec<Vec<String>>> {
    let mut recs: Vec<Vec<String>> = Vec::new();
    let mut rec: Vec<String> = Vec::new();
    let mut cur = String::new();
    let mut i = 0;
    let mut quoted = false;
    let mut any = false; // saw a field on this record
    while i < b.len() {
        let c = b[i];
        if quoted {
            if c == b'"' {
                if b.get(i + 1) == Some(&b'"') {
                    cur.push('"');
                    i += 2;
                    continue;
                }
                quoted = false;
                i += 1;
                continue;
            }
            cur.push(c as char);
            i += 1;
            continue;
        }
        match c {
            b'"' => {
                quoted = true;
                any = true;
                i += 1;
            }
            b',' => {
                rec.push(std::mem::take(&mut cur));
                any = true;
                i += 1;
            }
            b'\r' => i += 1,
            b'\n' => {
                if any || !cur.is_empty() {
                    rec.push(std::mem::take(&mut cur));
                    recs.push(std::mem::take(&mut rec));
                }
                any = false;
                i += 1;
            }
            _ => {
                cur.push(c as char);
                any = true;
                i += 1;
            }
        }
    }
    if quoted {
        return Err("fromcsv: unterminated quoted field".into());
    }
    if any || !cur.is_empty() {
        rec.push(cur);
        recs.push(rec);
    }
    Ok(recs)
}

// Infer a column from its text cells: all-integer -> [i64], all-numeric ->
// [f64], else [[u8]] strings. An empty cell is nil in a numeric column.
fn csv_column(cells: Vec<String>) -> R<Val> {
    let nonempty: Vec<&String> = cells.iter().filter(|s| !s.is_empty()).collect();
    let all_int = !nonempty.is_empty() && nonempty.iter().all(|s| s.parse::<i64>().is_ok());
    let all_num = !nonempty.is_empty()
        && nonempty.iter().all(|s| parse_f64(s).is_some_and(|x| x.is_finite()));
    let vals: Vec<Val> = cells
        .iter()
        .map(|s| {
            if all_int {
                if s.is_empty() {
                    Val::Nil
                } else {
                    Val::I64(s.parse().unwrap())
                }
            } else if all_num {
                if s.is_empty() {
                    Val::Nil
                } else {
                    Val::F64(parse_f64(s).unwrap())
                }
            } else {
                u8s(s.as_bytes())
            }
        })
        .collect();
    col_from_vals(vals).map(|c| Val::Vec(Rc::new(c)))
}

pub fn from_csv(v: &Val) -> R<Val> {
    let bytes = match v {
        Val::Vec(c) if is_u8_col(c) => col_bytes(c),
        _ => return Err("fromcsv needs a string ([u8])".into()),
    };
    let recs = csv_records(&bytes)?;
    let header = match recs.first() {
        Some(h) => h.clone(),
        None => return Ok(Val::Tab(Rc::new(Tab::default()))),
    };
    let mut t = Tab::default();
    for (ci, name) in header.iter().enumerate() {
        let cells: Vec<String> =
            recs[1..].iter().map(|r| r.get(ci).cloned().unwrap_or_default()).collect();
        t.bind(Bytes::new(name.as_bytes()), csv_column(cells)?, None);
    }
    Ok(Val::Tab(Rc::new(t)))
}

// keep Payload referenced for the Col::u8s path above
const _: fn() -> Payload = || Payload::I64s(Vec::new());
