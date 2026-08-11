// Snel CLI. See SPEC.md.
//   snel               REPL
//   snel run FILE.sn   check + evaluate a unit, print the result tab
//   snel fmt FILE.sn   parse and reprint canonically
//   snel sni FILE.sn   print the derived interface
//   snel bin FILE.sn   evaluate, serialize, reload, and print (round-trip)
//   snel apply         decode a closure from stdin, apply it to io, write result
//   snel lsp           language server over stdio
//
//   --remote           allow `use x = "url"` to fetch (off by default)

use snel::eval::Cx;
use snel::value::{Sym, Val};
use snel::{eval_unit, fmt_err, render_sni, root_env, FileLoader};
use snel::{check, eval, parse, print};
use std::cell::Cell;
use std::path::{Path, PathBuf};

thread_local! {
    // set once from the command line; read where loaders are constructed
    static REMOTE: Cell<bool> = const { Cell::new(false) };
}
pub fn remote_enabled() -> bool {
    REMOTE.with(|r| r.get())
}

fn main() {
    let mut args: Vec<String> = std::env::args().collect();
    // `--remote` allows `use x = "url"` to fetch; off by default. `--no-remote`
    // is accepted so a wrapper can force it off explicitly.
    let remote = args.iter().any(|a| a == "--remote") && !args.iter().any(|a| a == "--no-remote");
    args.retain(|a| a != "--remote" && a != "--no-remote");
    REMOTE.with(|r| r.set(remote));
    let code = match args.get(1).map(|s| s.as_str()) {
        None => repl(),
        // `run` calls the unit's main(io) entrypoint; bin/sni use the pure module
        Some("run") => with_unit(&args, snel::run_program, |_, v| {
            println!("{}", print::fmt_val(&v));
            0
        }),
        Some("bin") => with_unit(&args, eval_unit, |_, v| match snel::bin_roundtrip(&v) {
            Ok(v2) => {
                println!("{}", print::fmt_val(&v2));
                if print::fmt_val(&v) != print::fmt_val(&v2) {
                    eprintln!("round-trip MISMATCH");
                    1
                } else {
                    0
                }
            }
            Err(e) => {
                eprintln!("bin error: {}", e);
                1
            }
        }),
        Some("sni") => with_unit(&args, eval_unit, |src, v| {
            print!("{}", render_sni(src, &v));
            0
        }),
        Some("fmt") => cmd_fmt(&args),
        // the child side of subprocess eval: decode a closure from stdin, apply
        // it to `io`, write its [u8] response to stdout. See examples/subeval.sn.
        Some("apply") => {
            use std::io::{Read, Write};
            let mut buf = Vec::new();
            if std::io::stdin().read_to_end(&mut buf).is_err() {
                eprintln!("apply: cannot read stdin");
                2
            } else {
                match snel::apply_bin(&buf, remote_enabled()) {
                    Ok(out) => {
                        std::io::stdout().write_all(&out).ok();
                        0
                    }
                    Err(e) => {
                        eprintln!("apply: {}", e);
                        1
                    }
                }
            }
        }
        // a language server over stdio
        Some("lsp") => snel::lsp::serve(),
        Some(other) => {
            eprintln!(
                "unknown command `{}` (run, fmt, sni, bin, apply, lsp, or no args for REPL)",
                other
            );
            2
        }
    };
    std::process::exit(code);
}

fn with_unit(
    args: &[String],
    eval: impl Fn(&mut dyn snel::eval::Loader, &str) -> Result<Val, String>,
    show: impl Fn(&str, Val) -> i32,
) -> i32 {
    let Some(path) = args.get(2) else {
        eprintln!("usage: snel {} FILE.sn", args.get(1).map(|s| s.as_str()).unwrap_or("run"));
        return 2;
    };
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("{}: {}", path, e);
            return 2;
        }
    };
    let dir = Path::new(path).parent().map(|p| p.to_path_buf()).unwrap_or_else(|| PathBuf::from("."));
    let mut loader = FileLoader::new(dir).with_remote(remote_enabled());
    match eval(&mut loader, &src) {
        Ok(v) => show(&src, v),
        Err(e) => {
            eprintln!("{}", e);
            1
        }
    }
}

fn cmd_fmt(args: &[String]) -> i32 {
    let Some(path) = args.get(2) else {
        eprintln!("usage: snel fmt FILE.sn");
        return 2;
    };
    let src = std::fs::read_to_string(path).unwrap_or_default();
    match parse::parse_unit(&src) {
        Ok(ds) => {
            print!("{}", print::fmt_program(&ds));
            0
        }
        Err(e) => {
            eprintln!("{}", fmt_err("parse", &src, &e.msg, e.at));
            1
        }
    }
}

fn repl() -> i32 {
    use std::io::{BufRead, Write};
    let mut env = root_env();
    let stdin = std::io::stdin();
    let mut loader = FileLoader::new(PathBuf::from(".")).with_remote(remote_enabled());
    eprintln!("snel repl — declarations or expressions; ctrl-d to exit");
    loop {
        print!("> ");
        std::io::stdout().flush().ok();
        let mut line = String::new();
        match stdin.lock().read_line(&mut line) {
            Ok(0) => return 0,
            Ok(_) => {}
            Err(_) => return 1,
        }
        if line.trim().is_empty() {
            continue;
        }
        let ds = match parse::parse_unit(&line) {
            Ok(ds) => ds,
            Err(e) => {
                println!("{}", fmt_err("parse", &line, &e.msg, e.at));
                continue;
            }
        };
        let names: Vec<Sym> = env.keys.clone();
        if let Err(e) = check::check_unit(&ds, &names) {
            println!("{}", fmt_err("check", &line, &e.msg, e.span.lo));
            continue;
        }
        let mut cx = Cx { loader: &mut loader };
        for d in &ds {
            match eval::decl_step(&mut cx, &mut env, d) {
                Ok(v) => println!("{}", print::fmt_val(&v)),
                Err(e) => {
                    println!("{}", fmt_err("eval", &line, &e.msg, e.span.lo));
                    break;
                }
            }
        }
    }
}
