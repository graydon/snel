// Lexer. Doc comments (full line `--` immediately before a declaration) are
// tokens; any other `--` comment is whitespace. Newlines are tokens so the
// parser can treat them as declaration separators outside brackets.

use crate::value::Bytes;

#[derive(Clone, PartialEq, Debug)]
pub enum Tok {
    Int(i128), // decimal/hex/binary; range-checked at the parser (lets -2^63 round-trip)
    U8Lit(u8), // 'c' char literal or '\xNN' hex byte
    BitVec(Bytes), // :1011 bit-vector literal: the '0'/'1' digits (`_` stripped)
    Float(f64),
    Str(Bytes),
    Name(Bytes),   // identifier or keyword
    Punct(&'static str),
    Doc(Bytes),    // doc comment text (joined lines, no leading `--`)
    Newline,
    Eof,
}

pub struct Lexed {
    pub toks: Vec<(Tok, u32)>, // token + byte offset
}

const PUNCTS: &[&str] = &[
    "->", "<=", ">=", "<>", "|>", "(", ")", "[", "]", "{", "}", ",", ";", ".",
    "=", "<", ">", "+", "-", "*", "/", "%", ":", "|", "?",
];

pub fn lex(src: &str) -> Result<Lexed, (String, u32)> {
    let b = src.as_bytes();
    let mut toks: Vec<(Tok, u32)> = Vec::new();
    let mut i = 0usize;
    let mut line_start = true; // only whitespace so far on this line
    while i < b.len() {
        let c = b[i];
        if c == b'\n' {
            toks.push((Tok::Newline, i as u32));
            i += 1;
            line_start = true;
            continue;
        }
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        if c == b'-' && b.get(i + 1) == Some(&b'-') {
            let start = i;
            let mut j = i + 2;
            while j < b.len() && b[j] != b'\n' {
                j += 1;
            }
            if line_start {
                // full-line comment: candidate doc line
                let text = src[i + 2..j].trim();
                // merge with a preceding Doc token (multi-line doc block)
                if let Some((Tok::Doc(prev), _)) = toks.last_mut() {
                    let mut s = prev.bytes().to_vec();
                    s.push(b'\n');
                    s.extend_from_slice(text.as_bytes());
                    *prev = Bytes::new(&s);
                } else {
                    toks.push((Tok::Doc(Bytes::str(text)), start as u32));
                }
                // swallow the newline so doc lines glue to the next decl
                if j < b.len() {
                    j += 1;
                }
            }
            i = j;
            continue;
        }
        line_start = false;
        // u8 char literal: 'c', an escape '\n' '\t' '\\' '\'', or a hex byte '\xNN'
        if c == b'\'' {
            let (v, adv) = match b.get(i + 1) {
                Some(b'\\') => {
                    let e = *b.get(i + 2).ok_or(("bad char literal".to_string(), i as u32))?;
                    match e {
                        b'n' => (b'\n', 3),
                        b't' => (b'\t', 3),
                        b'\\' => (b'\\', 3),
                        b'\'' => (b'\'', 3),
                        b'x' => {
                            let h = src
                                .get(i + 3..i + 5)
                                .filter(|s| s.bytes().all(|d| d.is_ascii_hexdigit()))
                                .ok_or(("bad \\x in char literal".to_string(), i as u32))?;
                            (u8::from_str_radix(h, 16).unwrap(), 5)
                        }
                        _ => return Err(("bad char escape".into(), i as u32)),
                    }
                }
                Some(&ch) if ch != b'\'' && ch != b'\n' => (ch, 2),
                _ => return Err(("bad char literal".into(), i as u32)),
            };
            if b.get(i + adv) != Some(&b'\'') {
                return Err(("char literal must be one char in single quotes".into(), i as u32));
            }
            toks.push((Tok::U8Lit(v), i as u32));
            i += adv + 1;
            continue;
        }
        // bit-vector literal: :1011 (a [bit]); `_` allowed. `:name` (below) stays
        // a symbol — only `:` directly followed by a 0/1 digit is a bit vector.
        if c == b':' && matches!(b.get(i + 1), Some(b'0' | b'1')) {
            let mut j = i + 1;
            while j < b.len() && matches!(b[j], b'0' | b'1' | b'_') {
                j += 1;
            }
            let bits: Vec<u8> = src[i + 1..j].bytes().filter(|c| *c != b'_').collect();
            toks.push((Tok::BitVec(Bytes::new(&bits)), i as u32));
            i = j;
            continue;
        }
        if c.is_ascii_digit() {
            // hex / binary integer literals: 0x… / 0b…, `_` allowed as a separator
            if c == b'0' && matches!(b.get(i + 1), Some(b'x' | b'b')) {
                let hex = b[i + 1] == b'x';
                let mut j = i + 2;
                while j < b.len()
                    && (b[j] == b'_'
                        || if hex { b[j].is_ascii_hexdigit() } else { matches!(b[j], b'0' | b'1') })
                {
                    j += 1;
                }
                let clean: String = src[i + 2..j].chars().filter(|c| *c != '_').collect();
                if clean.is_empty() {
                    return Err((format!("expected digits after 0{}", b[i + 1] as char), i as u32));
                }
                let val = i128::from_str_radix(&clean, if hex { 16 } else { 2 })
                    .map_err(|_| ("integer literal out of range".to_string(), i as u32))?;
                toks.push((Tok::Int(val), i as u32));
                i = j;
                continue;
            }
            let start = i;
            let mut j = i;
            let digit_ = |x: u8| x.is_ascii_digit() || x == b'_'; // `_` separator allowed
            while j < b.len() && digit_(b[j]) {
                j += 1;
            }
            let mut is_float = false;
            if j < b.len() && b[j] == b'.' && b.get(j + 1).is_some_and(|d| d.is_ascii_digit()) {
                is_float = true;
                j += 1;
                while j < b.len() && digit_(b[j]) {
                    j += 1;
                }
            }
            if j < b.len() && (b[j] == b'e' || b[j] == b'E') {
                let mut k = j + 1;
                if k < b.len() && (b[k] == b'+' || b[k] == b'-') {
                    k += 1;
                }
                if k < b.len() && b[k].is_ascii_digit() {
                    is_float = true;
                    j = k;
                    while j < b.len() && digit_(b[j]) {
                        j += 1;
                    }
                }
            }
            let text: String = src[start..j].chars().filter(|c| *c != '_').collect();
            let tok = if is_float {
                Tok::Float(crate::print::parse_f64(&text).ok_or(("bad float".to_string(), start as u32))?)
            } else {
                Tok::Int(text.parse::<i128>().map_err(|_| ("int out of range".to_string(), start as u32))?)
            };
            toks.push((tok, start as u32));
            i = j;
            continue;
        }
        if c.is_ascii_alphabetic() || c == b'_' {
            let start = i;
            let mut j = i;
            while j < b.len() && (b[j].is_ascii_alphanumeric() || b[j] == b'_') {
                j += 1;
            }
            toks.push((Tok::Name(Bytes::str(&src[start..j])), start as u32));
            i = j;
            continue;
        }
        if c == b'"' {
            let start = i;
            let mut out: Vec<u8> = Vec::new();
            let mut j = i + 1;
            loop {
                if j >= b.len() {
                    return Err(("unterminated string".into(), start as u32));
                }
                match b[j] {
                    b'"' => break,
                    b'\\' => {
                        j += 1;
                        let e = *b.get(j).ok_or(("bad escape".to_string(), j as u32))?;
                        match e {
                            b'\\' => out.push(b'\\'),
                            b'"' => out.push(b'"'),
                            b'n' => out.push(b'\n'),
                            b't' => out.push(b'\t'),
                            b'x' => {
                                let h = src.get(j + 1..j + 3).ok_or(("bad \\x".to_string(), j as u32))?;
                                out.push(u8::from_str_radix(h, 16).map_err(|_| ("bad \\x".to_string(), j as u32))?);
                                j += 2;
                            }
                            _ => return Err(("bad escape".into(), j as u32)),
                        }
                        j += 1;
                    }
                    x => {
                        out.push(x);
                        j += 1;
                    }
                }
            }
            toks.push((Tok::Str(Bytes::new(&out)), start as u32));
            i = j + 1;
            continue;
        }
        let rest = &src[i..];
        match PUNCTS.iter().find(|p| rest.starts_with(**p)) {
            Some(p) => {
                toks.push((Tok::Punct(p), i as u32));
                i += p.len();
            }
            None => return Err((format!("stray character {:?}", c as char), i as u32)),
        }
    }
    toks.push((Tok::Eof, b.len() as u32));
    Ok(Lexed { toks })
}
