// A small Language Server for Snel, over stdio (`snel lsp`). Mirrored by
// c/lsp.c; both produce byte-identical protocol output.
//
// It needs no external crate — the JSON codec is the language's own
// (src/interop.rs), so requests decode into ordinary Snel values and replies
// are written with the same escaping rules.
//
// Deliberately it only *parses and checks*; it never evaluates. An editor must
// not run a user's `io` effects on every keystroke, so diagnostics come from
// the parser and the static checker alone. That means `use` imports are not
// resolved here (they are gradual, as if unresolvable) — a missing import is
// reported by `snel run`, not by the editor.

use crate::value::Val;
use crate::{check, parse};
use std::collections::HashMap;
use std::io::{Read, Write};

// ---------- JSON helpers over Snel values ----------

fn field<'a>(v: &'a Val, k: &str) -> Option<&'a Val> {
    match v {
        Val::Tab(t) => t.get(k.as_bytes()),
        _ => None,
    }
}
fn as_str(v: Option<&Val>) -> Option<String> {
    match v {
        Some(Val::Vec(c)) if crate::ops::is_u8_col(c) => {
            Some(String::from_utf8_lossy(&crate::ops::col_bytes(c)).into_owned())
        }
        _ => None,
    }
}
fn as_i64(v: Option<&Val>) -> Option<i64> {
    match v {
        Some(Val::I64(i)) => Some(*i),
        Some(Val::F64(f)) => Some(*f as i64),
        _ => None,
    }
}
fn jstr(s: &str, out: &mut String) {
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

// ---------- positions ----------

// A byte offset into `src` as an LSP (line, utf-16 character) position.
fn position(src: &str, at: u32) -> (u32, u32) {
    let at = (at as usize).min(src.len());
    let line = src[..at].bytes().filter(|b| *b == b'\n').count();
    let line_start = src[..at].rfind('\n').map_or(0, |i| i + 1);
    let col: usize = src[line_start..at].chars().map(|c| c.len_utf16()).sum();
    (line as u32, col as u32)
}

// ---------- diagnostics ----------

// Parse + check only; never evaluate. Returns (message, byte offset).
fn diagnose(src: &str) -> Option<(String, u32)> {
    match parse::parse_unit(src) {
        Err(e) => Some((format!("parse error: {}", e.msg), e.at)),
        Ok(ds) => match check::check_unit(&ds, &[]) {
            Err(e) => Some((format!("check error: {}", e.msg), e.span.lo)),
            Ok(()) => None,
        },
    }
}

fn publish(uri: &str, src: &str, out: &mut impl Write) {
    let mut items = String::new();
    if let Some((msg, at)) = diagnose(src) {
        let (line, ch) = position(src, at);
        // the span end is unknown; underline to the end of the token/line
        let end = src[(at as usize).min(src.len())..]
            .find(|c: char| c.is_whitespace())
            .map_or(ch + 1, |n| ch + n.max(1) as u32);
        items.push_str(&format!(
            "{{\"range\":{{\"start\":{{\"line\":{},\"character\":{}}},\
             \"end\":{{\"line\":{},\"character\":{}}}}},\"severity\":1,\"source\":\"snel\",\
             \"message\":",
            line, ch, line, end
        ));
        jstr(&msg, &mut items);
        items.push('}');
    }
    let mut params = String::from("{\"uri\":");
    jstr(uri, &mut params);
    params.push_str(&format!(",\"diagnostics\":[{}]}}", items));
    notify("textDocument/publishDiagnostics", &params, out);
}

// ---------- hover ----------

// The identifier surrounding a (line, character) position.
fn word_at(src: &str, line: u32, character: u32) -> Option<String> {
    let l = src.lines().nth(line as usize)?;
    let b = l.as_bytes();
    // character is utf-16; for identifiers (ASCII) it coincides with bytes
    let i = (character as usize).min(b.len());
    let is_word = |c: u8| c.is_ascii_alphanumeric() || c == b'_';
    let mut s = i;
    while s > 0 && is_word(b[s - 1]) {
        s -= 1;
    }
    let mut e = i;
    while e < b.len() && is_word(b[e]) {
        e += 1;
    }
    if s == e {
        None
    } else {
        Some(l[s..e].to_string())
    }
}

fn hover_text(word: &str) -> Option<String> {
    if let Some(op) = crate::ast::op_by_name(word.as_bytes()) {
        let n = crate::ast::op_arity(op);
        return Some(format!(
            "**{}** — builtin, {} argument{}\n\nA language-level name: resolved directly, never shadowed.",
            word,
            n,
            if n == 1 { "" } else { "s" }
        ));
    }
    let kw = [
        ("let", "bind a name: `let x = e;`"),
        ("fun", "function literal or declaration: `fun f(x: T) -> T = e;`"),
        ("type", "named type: `type n = T;`, or a predicate subtype `type n = T where p;`"),
        ("mod", "module: sugar over a fun returning a tab of its `pub` names"),
        ("pub", "export this declaration from the unit"),
        ("use", "import another unit; resolved and typed at check time"),
        ("do", "block: `do d; …; e end`, the same as `( d; …; e )`"),
        ("end", "closes a `do` block"),
        ("if", "scalar, lazy conditional; use `select` for a `[bit]` mask"),
        ("try", "`try e else f` — recover from `err` (values roll back, effects do not)"),
        ("err", "raise an error, caught by an enclosing `try`"),
        ("is", "type test: scalar -> bit, vec vs a scalar type -> [bit]"),
        ("where", "attaches a predicate to a `type`"),
        ("nil", "the absent value"),
        ("true", "bit literal"),
        ("false", "bit literal"),
    ];
    kw.iter().find(|(k, _)| *k == word).map(|(k, d)| format!("**{}** — {}", k, d))
}

// ---------- protocol ----------

fn notify(method: &str, params: &str, out: &mut impl Write) {
    let body = format!("{{\"jsonrpc\":\"2.0\",\"method\":\"{}\",\"params\":{}}}", method, params);
    write!(out, "Content-Length: {}\r\n\r\n{}", body.len(), body).ok();
    out.flush().ok();
}

fn respond(id: &str, result: &str, out: &mut impl Write) {
    let body = format!("{{\"jsonrpc\":\"2.0\",\"id\":{},\"result\":{}}}", id, result);
    write!(out, "Content-Length: {}\r\n\r\n{}", body.len(), body).ok();
    out.flush().ok();
}

// Read one framed message; None at end of input.
fn read_message(inp: &mut impl Read) -> Option<Vec<u8>> {
    let mut header = Vec::new();
    let mut byte = [0u8; 1];
    loop {
        if inp.read(&mut byte).ok()? == 0 {
            return None;
        }
        header.push(byte[0]);
        if header.ends_with(b"\r\n\r\n") {
            break;
        }
        if header.len() > 1 << 16 {
            return None;
        }
    }
    let text = String::from_utf8_lossy(&header).to_lowercase();
    let len: usize = text
        .lines()
        .find_map(|l| l.strip_prefix("content-length:"))
        .and_then(|v| v.trim().parse().ok())?;
    let mut body = vec![0u8; len];
    let mut got = 0;
    while got < len {
        let n = inp.read(&mut body[got..]).ok()?;
        if n == 0 {
            return None;
        }
        got += n;
    }
    Some(body)
}

pub fn serve() -> i32 {
    let stdin = std::io::stdin();
    let mut inp = stdin.lock();
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    let mut docs: HashMap<String, String> = HashMap::new();

    while let Some(body) = read_message(&mut inp) {
        // decode with the language's own JSON reader
        let msg = match crate::interop::from_json(&Val::Vec(std::rc::Rc::new(
            crate::value::Col::u8s(&body),
        ))) {
            Ok(v) => v,
            Err(_) => continue,
        };
        let method = as_str(field(&msg, "method")).unwrap_or_default();
        // an id may be a number or a string; echo it back verbatim-ish
        let id = match field(&msg, "id") {
            Some(Val::I64(i)) => Some(i.to_string()),
            Some(v) => as_str(Some(v)).map(|s| {
                let mut q = String::new();
                jstr(&s, &mut q);
                q
            }),
            None => None,
        };
        let params = field(&msg, "params").cloned().unwrap_or(Val::Nil);

        match method.as_str() {
            "initialize" => {
                if let Some(id) = id {
                    respond(
                        &id,
                        "{\"capabilities\":{\"textDocumentSync\":1,\"hoverProvider\":true},\
                         \"serverInfo\":{\"name\":\"snel\",\"version\":\"0.1.0\"}}",
                        &mut out,
                    );
                }
            }
            "initialized" => {}
            "shutdown" => {
                if let Some(id) = id {
                    respond(&id, "null", &mut out);
                }
            }
            "exit" => return 0,
            "textDocument/didOpen" => {
                let td = field(&params, "textDocument");
                if let (Some(uri), Some(text)) = (
                    as_str(td.and_then(|t| field(t, "uri"))),
                    as_str(td.and_then(|t| field(t, "text"))),
                ) {
                    publish(&uri, &text, &mut out);
                    docs.insert(uri, text);
                }
            }
            "textDocument/didChange" => {
                // full sync (textDocumentSync: 1): the last change holds the text
                let uri = as_str(field(&params, "textDocument").and_then(|t| field(t, "uri")));
                let text = match field(&params, "contentChanges") {
                    Some(Val::Vec(c)) if c.len > 0 => {
                        let last = crate::print::col_elem(c, c.len - 1);
                        as_str(field(&last, "text"))
                    }
                    _ => None,
                };
                if let (Some(uri), Some(text)) = (uri, text) {
                    publish(&uri, &text, &mut out);
                    docs.insert(uri, text);
                }
            }
            "textDocument/didSave" => {
                if let Some(uri) = as_str(field(&params, "textDocument").and_then(|t| field(t, "uri")))
                {
                    if let Some(text) = docs.get(&uri) {
                        let text = text.clone();
                        publish(&uri, &text, &mut out);
                    }
                }
            }
            "textDocument/didClose" => {
                if let Some(uri) = as_str(field(&params, "textDocument").and_then(|t| field(t, "uri")))
                {
                    docs.remove(&uri);
                }
            }
            "textDocument/hover" => {
                if let Some(id) = id {
                    let uri =
                        as_str(field(&params, "textDocument").and_then(|t| field(t, "uri")))
                            .unwrap_or_default();
                    let pos = field(&params, "position");
                    let line = as_i64(pos.and_then(|p| field(p, "line"))).unwrap_or(0) as u32;
                    let ch = as_i64(pos.and_then(|p| field(p, "character"))).unwrap_or(0) as u32;
                    let text = docs.get(&uri).cloned().unwrap_or_default();
                    let md = word_at(&text, line, ch).and_then(|w| hover_text(&w));
                    match md {
                        Some(md) => {
                            let mut v = String::from("{\"contents\":{\"kind\":\"markdown\",\"value\":");
                            jstr(&md, &mut v);
                            v.push_str("}}");
                            respond(&id, &v, &mut out);
                        }
                        None => respond(&id, "null", &mut out),
                    }
                }
            }
            _ => {
                // unknown request: reply null so the client is not left waiting
                if let Some(id) = id {
                    respond(&id, "null", &mut out);
                }
            }
        }
    }
    0
}
