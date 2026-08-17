// Snel interpreter library. See SPEC.md. Binary entry point is main.rs.

pub mod ast;
pub mod check;
pub mod eval;
pub mod interop;
pub mod io;
pub mod lex;
pub mod lsp;
pub mod ops;
pub mod parse;
pub mod print;
pub mod value;
pub mod wire;

use std::rc::Rc;
use value::{Bytes, Sym, Tab, Val};

// FNV-1a 64 over source bytes (cache/interface hashing).
pub fn fnv1a(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in bytes {
        h ^= *b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

// The interactive REPL session runs like an implicit `main`: it gets `io`.
pub fn root_env() -> Rc<Tab> {
    let mut t = Tab::default();
    t.bind(Bytes::str("io"), io::io_tab(), None);
    Rc::new(t)
}

pub fn err_line(src: &str, at: u32) -> usize {
    let at = (at as usize).min(src.len());
    src[..at].bytes().filter(|b| *b == b'\n').count() + 1
}

pub fn fmt_err(phase: &str, src: &str, msg: &str, at: u32) -> String {
    format!("{} error (line {}): {}", phase, err_line(src, at), msg)
}

// Check + evaluate a unit body; return the tab of its pub names (all names,
// minus the root capability, if none are pub).
// Every unit evaluates *pure* — no ambient `io`. A program that wants effects
// exports `fun main(io) …`, which the CLI calls with the io capability (see
// `run_program`). The same unit can therefore be `use`d as a library and run
// as an app. Anything needing a capability takes it as a parameter.
pub fn eval_unit(loader: &mut dyn eval::Loader, src: &str) -> Result<Val, String> {
    let ds = parse::parse_unit(src).map_err(|e| fmt_err("parse", src, &e.msg, e.at))?;
    // resolve each top-level `use` to its interface type by loading the unit and
    // reading the module value's type — so imported names check precisely. A
    // load failure (missing file, import cycle, or an error in the imported
    // unit) is a compile error here, not a deferred runtime error.
    let mut imports: std::collections::HashMap<Vec<u8>, ast::Ty> = std::collections::HashMap::new();
    for d in &ds {
        if let ast::Ast::Use { x, url, .. } = &d.ast {
            let v = match url {
                Some(u) => loader.load_url(x, u),
                None => loader.load(x),
            }
            .map_err(|e| {
                let nm = String::from_utf8_lossy(x.bytes());
                fmt_err("check", src, &format!("cannot resolve `use {}`: {}", nm, e), d.span.lo)
            })?;
            imports.insert(x.bytes().to_vec(), print::val_ty(&v));
        }
    }
    check::check_unit_with(&ds, &[], &|n| imports.get(n.bytes()).cloned())
        .map_err(|e| fmt_err("check", src, &e.msg, e.span.lo))?;
    let mut env: Rc<Tab> = Rc::new(Tab::default());
    let mut pubs: Vec<Sym> = Vec::new();
    let mut cx = eval::Cx { loader };
    for d in &ds {
        eval::decl_step(&mut cx, &mut env, d).map_err(|e| fmt_err("eval", src, &e.msg, e.span.lo))?;
        if let ast::Ast::Let { x, public: true, .. } | ast::Ast::Type { x, public: true, .. } = &d.ast {
            pubs.push(x.clone());
        }
    }
    // the unit's value is the tab of its `pub` names (all names, if none pub)
    let mut t = Tab::default();
    if pubs.is_empty() {
        for ((k, v), d) in env.keys.iter().zip(&env.vals).zip(&env.docs) {
            t.bind(k.clone(), v.clone(), d.clone());
        }
    } else {
        for p in &pubs {
            let i = env.keys.iter().rposition(|k| k == p).unwrap();
            t.bind(p.clone(), env.vals[i].clone(), env.docs[i].clone());
        }
    }
    Ok(Val::Tab(Rc::new(t)))
}

// Run a unit as a program: evaluate it (pure), then if it exports `main`, call
// `main(io)` with the io capability and return that; otherwise the unit's value
// is its module tab. This is the only place `io` enters.
pub fn run_program(loader: &mut dyn eval::Loader, src: &str) -> Result<Val, String> {
    let unit = eval_unit(loader, src)?;
    if let Val::Tab(t) = &unit {
        if let Some(main @ (Val::Fun(_) | Val::Prim(_))) = t.get(b"main").cloned().as_ref() {
            let main = main.clone();
            let mut cx = eval::Cx { loader };
            let span = ast::Span { lo: 0, hi: 0 };
            return eval::apply(&mut cx, &main, &mut [io::io_tab()], span)
                .map_err(|e| format!("eval error: {}", e.msg));
        }
    }
    Ok(unit)
}

// Run a closure shipped as encoded bytes: decode it, apply it to this process's
// `io`, and return the closure's `[u8]` response verbatim. The binary, in-memory
// counterpart of `run_program` — the child side of subprocess eval (`snel
// apply`). The closure receives the real `io`, so restricting or interposing
// effects is done by wrapping it before it is shipped. The closure carries its
// own captured environment, so parent values travel with it; nothing crosses as
// source text.
pub fn apply_bin(input: &[u8], remote: bool) -> Result<Vec<u8>, String> {
    let mut rd = wire::Rd::new(input);
    let f = wire::decode_val(&mut rd).map_err(|e| format!("apply decode: {e}"))?;
    let mut loader = FileLoader::new(std::path::PathBuf::from(".")).with_remote(remote);
    let mut cx = eval::Cx { loader: &mut loader };
    let span = ast::Span { lo: 0, hi: 0 };
    let v = eval::apply(&mut cx, &f, &mut [io::io_tab()], span)
        .map_err(|e| format!("eval error: {}", e.msg))?;
    // the closure's result is its [u8] response body; ship those bytes as-is
    if let Val::Vec(c) = &v {
        if c.present.is_none() && c.sel.is_none() {
            if let value::Payload::U8s(b) = &c.cases[0] {
                return Ok(b.bytes().to_vec());
            }
        }
    }
    let mut out = Vec::new();
    wire::encode_val(&v, &mut out);
    Ok(out)
}

// Lazily loads units by chasing `use` through the file system; caches
// evaluated unit tabs and regenerates `.sni` interfaces on load.
pub struct FileLoader {
    pub dir: std::path::PathBuf,
    // whether `use x = "url"` may fetch: off unless the CLI passes --remote
    pub remote: bool,
    cache: std::collections::HashMap<Vec<u8>, Val>,
    stack: Vec<Vec<u8>>,
}

impl FileLoader {
    pub fn new(dir: std::path::PathBuf) -> FileLoader {
        FileLoader { dir, remote: false, cache: Default::default(), stack: Vec::new() }
    }
    pub fn with_remote(mut self, remote: bool) -> FileLoader {
        self.remote = remote;
        self
    }
}

// Fetch the source of a remote unit. `file:` needs nothing; `http(s):` is only
// available in a build with the `remote` feature, which shells out to the
// system `curl` rather than vendoring a TLS stack into the interpreter.
fn fetch_url(url: &str) -> Result<String, String> {
    if let Some(path) = url.strip_prefix("file://") {
        return std::fs::read_to_string(path).map_err(|e| format!("{}: {}", path, e));
    }
    if url.starts_with("http://") || url.starts_with("https://") {
        {
            let out = std::process::Command::new("curl")
                .args(["-sSL", "--fail", "--max-time", "30", url])
                .output()
                .map_err(|e| format!("curl: {} (is it installed?)", e))?;
            if !out.status.success() {
                return Err(format!(
                    "fetch failed: {}",
                    String::from_utf8_lossy(&out.stderr).trim()
                ));
            }
            return String::from_utf8(out.stdout).map_err(|_| "response is not utf-8".to_string());
        }
    }
    Err(format!("unsupported url scheme: {}", url))
}

impl eval::Loader for FileLoader {
    // `use x = "url"`: fetch, evaluate, and cache under the same name as a
    // local unit, so a URL import behaves exactly like a file one afterwards.
    fn load_url(&mut self, name: &Bytes, url: &Bytes) -> Result<Val, String> {
        let key = name.bytes().to_vec();
        if let Some(v) = self.cache.get(&key) {
            return Ok(v.clone());
        }
        let url = String::from_utf8_lossy(url.bytes()).into_owned();
        if !self.remote {
            return Err(format!("remote units are disabled (pass --remote to allow `{}`)", url));
        }
        if self.stack.contains(&key) {
            return Err(format!("import cycle through `{:?}`", name));
        }
        let src = fetch_url(&url)?;
        self.stack.push(key.clone());
        let v = eval_unit(self, &src).map_err(|e| format!("{}: {}", url, e));
        self.stack.pop();
        let v = v?;
        self.cache.insert(key, v.clone());
        Ok(v)
    }

    fn load(&mut self, name: &Bytes) -> Result<Val, String> {
        let key = name.bytes().to_vec();
        if let Some(v) = self.cache.get(&key) {
            return Ok(v.clone());
        }
        if self.stack.contains(&key) {
            return Err(format!("import cycle through `{:?}`", name));
        }
        let path = self.dir.join(format!("{}.sn", String::from_utf8_lossy(&key)));
        let src = std::fs::read_to_string(&path).map_err(|e| format!("{}: {}", path.display(), e))?;
        self.stack.push(key.clone());
        let v = eval_unit(self, &src).map_err(|e| format!("{}: {}", path.display(), e));
        self.stack.pop();
        let v = v?;
        std::fs::write(path.with_extension("sni"), render_sni(&src, &v)).ok();
        self.cache.insert(key, v.clone());
        Ok(v)
    }
}

// The derived interface text: source hash, then pub names with types and docs.
pub fn render_sni(src: &str, unit: &Val) -> String {
    let mut out = format!("-- {:016x}\n", fnv1a(src.as_bytes()));
    // the module doc, if any, leads the interface (blank line after it)
    if let Some(doc) = parse::module_doc(src) {
        for line in doc.as_str().unwrap_or("").lines() {
            out.push_str(&format!("-- {}\n", line));
        }
        out.push('\n');
    }
    if let Val::Tab(t) = unit {
        for ((k, v), d) in t.keys.iter().zip(&t.vals).zip(&t.docs) {
            if let Some(doc) = d {
                for line in doc.as_str().unwrap_or("").lines() {
                    out.push_str(&format!("-- {}\n", line));
                }
            }
            out.push_str(&format!("pub {:?} : {}\n", k, print::fmt_ty(&print::val_ty(v))));
        }
    }
    out
}

// Round-trip a value through the binary format.
pub fn bin_roundtrip(v: &Val) -> Result<Val, String> {
    let mut buf = Vec::new();
    wire::encode_val(v, &mut buf);
    let mut rd = wire::Rd::new(&buf);
    let out = wire::decode_val(&mut rd)?;
    if rd.i != buf.len() {
        return Err(format!("binary decode left {} trailing bytes", buf.len() - rd.i));
    }
    Ok(out)
}
