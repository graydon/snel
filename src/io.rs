// Effectful interpreter primitives. They are ordinary values (Val::Prim) that
// enter a program only as the `io` argument the CLI passes to `main` — code not
// handed `io` cannot perform effects (capability style). Every user function
// stays pure; try/else rolls back values, not external effects.

use crate::ast::Ty;
use crate::value::{Bytes, Col, Tab, Val};
use std::io::{Read, Write};
use std::rc::Rc;

// name -> (arg types, return type). Strings are [u8]; argv is [[u8]].
pub const PRIMS: &[(&str, &[PTy], PTy)] = &[
    ("read", &[PTy::Str], PTy::Str),                    // path -> bytes
    ("write", &[PTy::Str, PTy::Str], PTy::Nil),         // path, bytes -> nil
    ("args", &[], PTy::Strs),                           // -> [[u8]] argv
    ("env", &[], PTy::Env),                             // -> { NAME = value, … } (environ)
    ("exe", &[], PTy::Str),                             // -> path of the running interpreter
    // prog, argv, stdin, envs ("KEY=VALUE" each) -> stdout
    ("spawn", &[PTy::Str, PTy::Strs, PTy::Str, PTy::Strs], PTy::Str),
    // filesystem
    ("list", &[PTy::Str], PTy::Strs),                   // dir -> entry names
    ("stat", &[PTy::Str], PTy::Stat),                   // path -> { size, mtime, isdir }
    ("exists", &[PTy::Str], PTy::Bit),                  // path -> present?
    ("mkdir", &[PTy::Str], PTy::Nil),
    ("rmdir", &[PTy::Str], PTy::Nil),
    ("unlink", &[PTy::Str], PTy::Nil),
    ("rename", &[PTy::Str, PTy::Str], PTy::Nil),
    ("link", &[PTy::Str, PTy::Str], PTy::Nil),          // hard link
    // clock
    ("time", &[], PTy::I64),                            // -> milliseconds since the epoch
    ("sleep", &[PTy::I64], PTy::Nil),                   // sleep milliseconds
];

#[derive(Clone, Copy)]
pub enum PTy {
    Nil,
    Bit,
    I64,
    Str,  // a [u8]
    Strs, // a [[u8]]
    Env,  // a tab of env vars, keys unknown statically -> {}
    Stat, // { size: i64, mtime: i64, isdir: bit }
}

fn pty(t: PTy) -> Ty {
    let u8s = || Ty::Vec(Box::new(Ty::U8));
    match t {
        PTy::Nil => Ty::Nil,
        PTy::Bit => Ty::Bit,
        PTy::I64 => Ty::I64,
        PTy::Str => u8s(),
        PTy::Strs => Ty::Vec(Box::new(u8s())),
        PTy::Env => Ty::Tab(vec![]),
        PTy::Stat => Ty::Tab(vec![
            (Bytes::str("size"), Ty::I64),
            (Bytes::str("mtime"), Ty::I64),
            (Bytes::str("isdir"), Ty::Bit),
        ]),
    }
}

pub fn sig(name: &[u8]) -> Option<(Vec<Ty>, Ty)> {
    PRIMS
        .iter()
        .find(|(n, _, _)| n.as_bytes() == name)
        .map(|(_, a, r)| (a.iter().map(|t| pty(*t)).collect(), pty(*r)))
}

// The `io` tab: one Prim per primitive.
pub fn io_tab() -> Val {
    let mut t = Tab::default();
    for (n, _, _) in PRIMS {
        t.bind(Bytes::str(n), Val::Prim(Bytes::str(n)), None);
    }
    Val::Tab(Rc::new(t))
}

fn str_val(b: &[u8]) -> Val {
    Val::Vec(Rc::new(Col::u8s(b)))
}

// a [[u8]] column: each element is itself a [u8] column
fn strs_val(items: Vec<Vec<u8>>) -> Val {
    let elems: Vec<Val> = items.iter().map(|b| Val::Vec(Rc::new(Col::u8s(b)))).collect();
    Val::Vec(Rc::new(crate::ops::col_from_vals(elems).expect("homogeneous")))
}

pub fn call(name: &Bytes, args: Vec<Val>) -> Result<Val, String> {
    match name.bytes() {
        b"read" => {
            let path = as_string(&args, 0)?;
            std::fs::read(&path).map(|b| str_val(&b)).map_err(|e| e.to_string())
        }
        b"write" => {
            let path = as_string(&args, 0)?;
            let data = as_bytes(&args, 1)?;
            std::fs::write(&path, data).map(|_| Val::Nil).map_err(|e| e.to_string())
        }
        b"args" => Ok(strs_val(
            std::env::args().skip(1).map(|a| a.into_bytes()).collect(),
        )),
        b"env" => {
            let mut t = Tab::default();
            for (k, v) in std::env::vars_os() {
                t.bind(Bytes::new(k.to_string_lossy().as_bytes()), str_val(v.to_string_lossy().as_bytes()), None);
            }
            Ok(Val::Tab(Rc::new(t)))
        }
        b"exe" => std::env::current_exe()
            .map(|p| str_val(p.to_string_lossy().as_bytes()))
            .map_err(|e| e.to_string()),
        b"spawn" => spawn(&args),
        b"list" => {
            let path = as_string(&args, 0)?;
            let mut names = Vec::new();
            for e in std::fs::read_dir(&path).map_err(|e| e.to_string())? {
                names.push(e.map_err(|e| e.to_string())?.file_name().to_string_lossy().into_owned().into_bytes());
            }
            Ok(strs_val(names))
        }
        b"stat" => {
            let m = std::fs::metadata(as_string(&args, 0)?).map_err(|e| e.to_string())?;
            let mtime = m.modified().ok()
                .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
                .map_or(0, |d| d.as_secs() as i64);
            let mut t = Tab::default();
            t.bind(Bytes::str("size"), Val::I64(m.len() as i64), None);
            t.bind(Bytes::str("mtime"), Val::I64(mtime), None);
            t.bind(Bytes::str("isdir"), Val::Bit(m.is_dir()), None);
            Ok(Val::Tab(Rc::new(t)))
        }
        b"exists" => Ok(Val::Bit(std::path::Path::new(&as_string(&args, 0)?).exists())),
        b"mkdir" => nilify(std::fs::create_dir(as_string(&args, 0)?)),
        b"rmdir" => nilify(std::fs::remove_dir(as_string(&args, 0)?)),
        b"unlink" => nilify(std::fs::remove_file(as_string(&args, 0)?)),
        b"rename" => nilify(std::fs::rename(as_string(&args, 0)?, as_string(&args, 1)?)),
        b"link" => nilify(std::fs::hard_link(as_string(&args, 0)?, as_string(&args, 1)?)),
        b"time" => Ok(Val::I64(
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map_or(0, |d| d.as_millis() as i64),
        )),
        b"sleep" => {
            match args.first() {
                Some(Val::I64(ms)) if *ms > 0 => std::thread::sleep(std::time::Duration::from_millis(*ms as u64)),
                Some(Val::I64(_)) => {}
                _ => return Err("sleep needs an i64".into()),
            }
            Ok(Val::Nil)
        }
        _ => Err(format!("unknown primitive io.{:?}", name)),
    }
}

fn nilify(r: std::io::Result<()>) -> Result<Val, String> {
    r.map(|_| Val::Nil).map_err(|e| e.to_string())
}

// a [u8] argument as raw bytes
fn as_bytes(args: &[Val], i: usize) -> Result<Vec<u8>, String> {
    match args.get(i) {
        Some(Val::Vec(c)) if crate::ops::is_u8_col(c) => Ok(crate::ops::col_bytes(c)),
        _ => Err(format!("arg {} must be a string ([u8])", i)),
    }
}
fn as_string(args: &[Val], i: usize) -> Result<String, String> {
    Ok(String::from_utf8_lossy(&as_bytes(args, i)?).into_owned())
}

// a [[u8]] argument as a vector of byte strings
fn as_strings(args: &[Val], i: usize) -> Result<Vec<Vec<u8>>, String> {
    match args.get(i) {
        Some(Val::Vec(c)) => (0..c.len)
            .map(|j| match crate::print::col_elem(c, j) {
                Val::Vec(s) if crate::ops::is_u8_col(&s) => Ok(crate::ops::col_bytes(&s)),
                _ => Err(format!("arg {i} must be a [[u8]] of strings")),
            })
            .collect(),
        _ => Err(format!("arg {i} must be a [[u8]]")),
    }
}

fn spawn(args: &[Val]) -> Result<Val, String> {
    let prog = as_string(args, 0)?;
    let argv = as_strings(args, 1)?;
    let stdin = as_bytes(args, 2)?;
    use std::process::{Command, Stdio};
    let mut cmd = Command::new(&prog);
    cmd.args(argv.iter().map(|a| String::from_utf8_lossy(a).into_owned()))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped());
    // each env entry is "KEY=VALUE"; added on top of the inherited environment
    for entry in as_strings(args, 3)? {
        if let Some(eq) = entry.iter().position(|&b| b == b'=') {
            cmd.env(
                String::from_utf8_lossy(&entry[..eq]).into_owned(),
                String::from_utf8_lossy(&entry[eq + 1..]).into_owned(),
            );
        }
    }
    let mut child = cmd.spawn().map_err(|e| e.to_string())?;
    child.stdin.take().unwrap().write_all(&stdin).map_err(|e| e.to_string())?;
    let mut out = Vec::new();
    child.stdout.take().unwrap().read_to_end(&mut out).map_err(|e| e.to_string())?;
    child.wait().map_err(|e| e.to_string())?;
    Ok(str_val(&out))
}
