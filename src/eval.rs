// Tree-walking evaluator: big-step under an environment tab, no substitution.
// Closures capture a trimmed env (free vars, preorder order). All vector loops
// live in ops.rs.

use crate::ast::{op_by_name, Ast, Node, Op, Span, Ty};
use crate::ops;
use crate::print::{col_elem, fmt_ty, fmt_val};
use crate::value::{Bytes, Bits, Clo, Payload, Sym, Tab, Val};
use std::rc::Rc;

pub struct EErr {
    pub msg: String,
    pub span: Span,
}

pub type EResult = Result<Val, EErr>;

pub trait Loader {
    fn load(&mut self, name: &Bytes) -> Result<Val, String>;
    // `use x = "url"`: load a unit named by a URL. Remote loading is optional
    // and off unless explicitly enabled, so the default is a clear refusal.
    fn load_url(&mut self, _name: &Bytes, url: &Bytes) -> Result<Val, String> {
        Err(format!("remote units are not enabled (`{}`)", String::from_utf8_lossy(url.bytes())))
    }
}

pub struct NoLoader;
impl Loader for NoLoader {
    fn load(&mut self, name: &Bytes) -> Result<Val, String> {
        Err(format!("no unit loader for `{:?}`", name))
    }
}

pub struct Cx<'a> {
    pub loader: &'a mut dyn Loader,
}

fn fail<T>(msg: impl Into<String>, span: Span) -> Result<T, EErr> {
    Err(EErr { msg: msg.into(), span })
}

pub fn eval(cx: &mut Cx, env: &Rc<Tab>, n: &Node) -> EResult {
    let sp = n.span;
    match &n.ast {
        Ast::Lit(v) => Ok(v.clone()),
        Ast::Var(x) => match env.get(x.bytes()) {
            Some(v) => Ok(v.clone()),
            None => {
                if op_by_name(x.bytes()).is_some() {
                    Ok(Val::Prim(x.clone())) // a builtin as a first-class value
                } else {
                    fail(format!("unbound name `{:?}`", x), sp)
                }
            }
        },
        Ast::Proj(e, x) => match eval(cx, env, e)? {
            Val::Tab(t) => match t.get(x.bytes()) {
                Some(v) => Ok(v.clone()),
                None => fail(format!("no field `{:?}`", x), sp),
            },
            v => fail(format!("cannot project `{:?}` from {}", x, fmt_ty(&crate::print::val_ty(&v))), sp),
        },
        Ast::Idx(e, i) => {
            let t = eval(cx, env, e)?;
            let ix = eval(cx, env, i)?;
            ops::index(&t, &ix).map_err(|m| EErr { msg: m, span: sp })
        }
        Ast::App(f, args) => {
            // Evaluate the args into a small stack buffer for the common low-arity
            // case (no heap allocation per call), falling back to a Vec otherwise.
            // builtins are reserved names -> dispatched directly, else it's a call.
            let builtin_op =
                if let Ast::Var(name) = &f.ast { op_by_name(name.bytes()) } else { None };
            let fv = match builtin_op {
                Some(_) => None,
                None => Some(eval(cx, env, f)?),
            };
            const N: usize = 4;
            if args.len() <= N {
                let mut buf: [Val; N] = [Val::Nil, Val::Nil, Val::Nil, Val::Nil];
                for (i, a) in args.iter().enumerate() {
                    buf[i] = eval(cx, env, a)?;
                }
                let slot = &mut buf[..args.len()];
                match builtin_op {
                    Some(op) => builtin(cx, env, op, slot, sp),
                    None => apply(cx, fv.as_ref().unwrap(), slot, sp),
                }
            } else {
                let mut vals =
                    args.iter().map(|a| eval(cx, env, a)).collect::<Result<Vec<_>, _>>()?;
                match builtin_op {
                    Some(op) => builtin(cx, env, op, &mut vals, sp),
                    None => apply(cx, fv.as_ref().unwrap(), &mut vals, sp),
                }
            }
        }
        Ast::VecL(es) => {
            let vals = es.iter().map(|e| eval(cx, env, e)).collect::<Result<Vec<_>, _>>()?;
            ops::col_from_vals(vals)
                .map(|c| Val::Vec(Rc::new(c)))
                .map_err(|m| EErr { msg: m, span: sp })
        }
        Ast::TabL(fs) => {
            let mut t = Tab::default();
            for (k, e) in fs {
                let v = eval(cx, env, e)?;
                t.bind(k.clone(), v, None);
            }
            Ok(Val::Tab(Rc::new(t)))
        }
        Ast::Fun { params, ret, body } => {
            // Capture the body's free names — and, transitively, the type names a
            // captured `type` refers to in its own base, so that resolving (and
            // coercing against) that type still works inside the closure.
            let mut captured = Tab::default();
            let mut want = free_vars(n);
            let mut i = 0;
            while i < want.len() {
                let x = want[i].clone();
                i += 1;
                let Some(v) = env.get(x.bytes()) else { continue };
                captured.bind(x, v.clone(), None);
                for d in type_deps(&v) {
                    if !want.contains(&d) {
                        want.push(d);
                    }
                }
            }
            Ok(Val::Fun(Rc::new(Clo {
                params: params.clone(),
                ret: ret.clone(),
                body: body.clone(),
                env: Rc::new(captured),
            })))
        }
        // Scalar, lazy conditional: only the taken branch runs. A [bit] mask is
        // not accepted here — use `select` for elementwise choice.
        Ast::If(c, t, e) => match eval(cx, env, c)? {
            Val::Bit(b) => eval(cx, env, if b { t } else { e }),
            _ => fail("if condition must be a scalar bit (use select for a [bit] mask)", sp),
        },
        Ast::Try(e, f) => match eval(cx, env, e) {
            Ok(v) => Ok(v),
            Err(_) => eval(cx, env, f),
        },
        Ast::Err(e) => {
            let v = eval(cx, env, e)?;
            // a string ([u8]) message is shown as its text; anything else printed
            let msg = match &v {
                Val::Vec(c) if crate::ops::is_u8_col(c) => {
                    String::from_utf8_lossy(&crate::ops::col_bytes(c)).into_owned()
                }
                v => fmt_val(v),
            };
            fail(msg, sp)
        }
        Ast::Is(e, t) => {
            let v = eval(cx, env, e)?;
            is_test(cx, env, &v, t, sp)
        }
        Ast::As(e, t) => {
            let v = eval(cx, env, e)?;
            coerce(cx, env, v, t, sp)
        }
        Ast::Seq(ds) => {
            let mut cur = env.clone();
            let mut last = Val::Nil;
            for d in ds {
                last = decl_step(cx, &mut cur, d)?;
            }
            Ok(last)
        }
        Ast::Let { .. } | Ast::Type { .. } | Ast::Use { .. } => {
            // a lone declaration evaluates to its bound value (REPL)
            let mut cur = env.clone();
            decl_step(cx, &mut cur, n)
        }
    }
}

// Evaluate one declaration, extending `env` with its binding. Returns the
// declared value (or the expression's value).
pub fn decl_step(cx: &mut Cx, env: &mut Rc<Tab>, d: &Node) -> EResult {
    match &d.ast {
        Ast::Let { x, ty, e, doc, .. } => {
            let mut v = eval(cx, env, e)?;
            if let Some(t) = ty {
                v = coerce(cx, env, v, t, d.span)?;
            }
            let t = Rc::make_mut(env);
            t.bind(x.clone(), v.clone(), doc.clone());
            Ok(v)
        }
        Ast::Type { x, base, pred, doc, .. } => {
            let p = eval(cx, env, pred)?;
            let mut t = Tab::default();
            t.bind(Bytes::str("type"), crate::wire::ty_to_val(base), None);
            t.bind(Bytes::str("pred"), p, None);
            let v = Val::Tab(Rc::new(t));
            Rc::make_mut(env).bind(x.clone(), v.clone(), doc.clone());
            Ok(v)
        }
        Ast::Use { x, url, doc } => {
            let v = match url {
                Some(u) => cx.loader.load_url(x, u),
                None => cx.loader.load(x),
            }
            .map_err(|m| EErr { msg: m, span: d.span })?;
            Rc::make_mut(env).bind(x.clone(), v.clone(), doc.clone());
            Ok(v)
        }
        _ => eval(cx, env, d),
    }
}

// A closure call's env doesn't escape (closures capture a trimmed copy), except
// when the body reflects via env(), which bumps the Rc strong count. So reuse
// whole `Rc<Tab>` frames from a pool — reclaiming both the Tab's Vecs and the Rc
// allocation — instead of allocating a fresh env per application.
thread_local! {
    static FRAME_POOL: std::cell::RefCell<Vec<Rc<Tab>>> = const { std::cell::RefCell::new(Vec::new()) };
}
fn frame_get() -> Rc<Tab> {
    FRAME_POOL.with(|p| p.borrow_mut().pop()).unwrap_or_else(|| Rc::new(Tab::default()))
}

// args is a mutable borrow (not an owned Vec) so hot callers pass a stack array
// and avoid a per-call allocation; arguments are *moved* out with mem::take (no
// clone), which keeps refcounts intact so make_mut/COW can still elide copies.
pub fn apply(cx: &mut Cx, f: &Val, args: &mut [Val], sp: Span) -> EResult {
    match f {
        Val::Fun(clo) => {
            if args.len() != clo.params.len() {
                return fail(
                    format!("arity: expected {} args, got {}", clo.params.len(), args.len()),
                    sp,
                );
            }
            let cenv = clo.env.clone();
            let mut envrc = frame_get(); // a uniquely-owned, reused Rc<Tab>
            {
                let env = Rc::get_mut(&mut envrc).unwrap(); // unique -> &mut Tab
                env.keys.extend(clo.env.keys.iter().cloned());
                env.vals.extend(clo.env.vals.iter().cloned());
                env.docs.extend(clo.env.docs.iter().cloned());
                for ((x, t), a) in clo.params.iter().zip(args.iter_mut()) {
                    let a = coerce(cx, &cenv, std::mem::take(a), t, sp)?;
                    env.bind(x.clone(), a, None);
                }
            }
            let r = eval(cx, &envrc, &clo.body)?;
            // reclaim the frame unless the body captured it (env() -> count > 1)
            if let Some(env) = Rc::get_mut(&mut envrc) {
                env.keys.clear();
                env.vals.clear();
                env.docs.clear();
                FRAME_POOL.with(|p| {
                    let mut p = p.borrow_mut();
                    if p.len() < 512 {
                        p.push(envrc);
                    }
                });
            }
            coerce(cx, &cenv, r, &clo.ret, sp) // the declared return type is enforced too
        }
        Val::Prim(name) => match op_by_name(name.bytes()) {
            // a first-class builtin routes straight to the builtin dispatch (no
            // closure, no AST); the static checker can't guarantee its arity
            // here, so check it now. Ops that read the ambient env (`locals`)
            // are degenerate as values — they see an empty env.
            Some(op) => {
                let want = crate::ast::op_arity(op);
                if args.len() != want {
                    let nm = String::from_utf8_lossy(name.bytes());
                    return fail(format!("`{}`: expected {} args, got {}", nm, want, args.len()), sp);
                }
                builtin(cx, &Rc::new(Tab::default()), op, args, sp)
            }
            None => crate::io::call(name, args.to_vec()).map_err(|m| EErr { msg: m, span: sp }),
        },
        v => fail(format!("cannot call {}", fmt_ty(&crate::print::val_ty(v))), sp),
    }
}

fn builtin(cx: &mut Cx, env: &Rc<Tab>, op: Op, args: &mut [Val], sp: Span) -> EResult {
    // The static checker validates builtin arity, so no runtime arity check is
    // needed; args are moved out with mem::take (preserving refcounts for COW).
    let bad = |m: String| EErr { msg: m, span: sp };
    use Op::*;
    match op {
        Add | Sub | Mul | Div | Rem => {
            let a = std::mem::take(&mut args[0]);
            let b = std::mem::take(&mut args[1]);
            ops::arith(op, a, b).map_err(bad)
        }
        Neg | Abs | Itof | Ftoi | Sqrt | Floor | Ceil | Sign | Ord | Chr => {
            ops::unary(op, std::mem::take(&mut args[0])).map_err(bad)
        }
        Eq | Ne | Lt | Le | Gt | Ge => {
            let a = std::mem::take(&mut args[0]);
            let b = std::mem::take(&mut args[1]);
            ops::compare(op, a, b).map_err(bad)
        }
        And | Or => {
            ops::boolean(op, args).map_err(bad)
        }
        Not => {
            ops::boolean(op, args).map_err(bad)
        }
        Len => {
            match &args[0] {
                Val::Vec(c) => Ok(Val::I64(c.len as i64)),
                v => fail(format!("len of {}", fmt_ty(&crate::print::val_ty(v))), sp),
            }
        }
        Cat => {
            ops::cat(&args[0], &args[1]).map_err(bad)
        }
        Find => {
            ops::find(&args[1], &args[0]).map_err(bad) // find(needle, haystack)
        }
        Split => {
            ops::split(&args[1], &args[0]).map_err(bad) // split(sep, s)
        }
        Join => {
            ops::join(&args[0], &args[1]).map_err(bad)
        }
        Iota => {
            match &args[0] {
                Val::I64(n) => ops::iota(*n).map_err(bad),
                _ => fail("iota needs an i64", sp),
            }
        }
        Grade => {
            match &args[0] {
                Val::Vec(c) => Ok(ops::grade(c)),
                _ => fail("grade needs a vec", sp),
            }
        }
        Sum => {
            match &args[0] {
                Val::Vec(c) => ops::sum(c).map_err(bad),
                _ => fail("sum needs a vec", sp),
            }
        }
        Prod => {
            match &args[0] {
                Val::Vec(c) => ops::prod(c).map_err(bad),
                _ => fail("prod needs a vec", sp),
            }
        }
        Min | Max => {
            match &args[0] {
                Val::Vec(c) => ops::minmax(c, op == Min).map_err(bad),
                _ => fail("min/max needs a vec", sp),
            }
        }
        Isnil => {
            Ok(ops::isnil(&args[0]))
        }
        All => {
            ops::all(&args[0]).map_err(bad)
        }
        Any => {
            ops::any(&args[0]).map_err(bad)
        }
        Rev => {
            ops::rev(&args[0]).map_err(bad)
        }
        First => {
            ops::first(&args[0]).map_err(bad)
        }
        Last => {
            ops::last(&args[0]).map_err(bad)
        }
        Which => {
            ops::which(&args[0]).map_err(bad)
        }
        Distinct => {
            ops::distinct(&args[0]).map_err(bad)
        }
        Take | Drop => {
            match &args[0] {
                Val::I64(n) if op == Take => ops::take(*n, &args[1]).map_err(bad),
                Val::I64(n) => ops::drop(*n, &args[1]).map_err(bad),
                _ => fail("take/drop needs (i64, vec)", sp),
            }
        }
        In => {
            ops::contains(&args[0], &args[1]).map_err(bad)
        }
        At => {
            match &args[0] {
                Val::I64(i) => ops::at(&args[1], *i).map_err(bad), // at(i, vec)
                _ => fail("at needs (i64, vec)", sp),
            }
        }
        Rep => {
            match &args[0] {
                Val::I64(n) => ops::rep(*n, &args[1]).map_err(bad),
                _ => fail("rep needs (i64, scalar)", sp),
            }
        }
        Scatter => {
            ops::scatter(&args[2], &args[0], &args[1]).map_err(bad) // scatter(idx, vals, base)
        }
        Shift => {
            match &args[0] {
                Val::I64(k) => ops::shift(&args[2], *k, &args[1]).map_err(bad), // shift(k, fill, vec)
                _ => fail("shift needs (i64, fill, vec)", sp),
            }
        }
        Sums => {
            ops::sums(&args[0]).map_err(bad)
        }
        Prods => {
            ops::prods(&args[0]).map_err(bad)
        }
        ToJson => {
            crate::interop::to_json(&args[0]).map_err(bad)
        }
        FromJson => {
            crate::interop::from_json(&args[0]).map_err(bad)
        }
        ToCsv => {
            crate::interop::to_csv(&args[0]).map_err(bad)
        }
        FromCsv => {
            crate::interop::from_csv(&args[0]).map_err(bad)
        }
        Member => {
            ops::member(&args[0], &args[1]).map_err(bad)
        }
        Matches => {
            ops::matches(&args[0], &args[1]).map_err(bad)
        }
        Runs => {
            ops::runs(&args[0]).map_err(bad)
        }
        Partition => {
            ops::partition(&args[0], &args[1]).map_err(bad)
        }
        Windows => {
            match &args[0] {
                Val::I64(k) => ops::windows(*k, &args[1]).map_err(bad),
                _ => fail("windows needs (i64, vec)", sp),
            }
        }
        Map => {
            let f = std::mem::take(&mut args[0]);
            let v = std::mem::take(&mut args[1]);
            match v {
                Val::Vec(c) => {
                    let outs: Vec<Val> = (0..c.len)
                        .map(|i| apply(cx, &f, &mut [col_elem(&c, i)], sp))
                        .collect::<Result<Vec<_>, _>>()?;
                    ops::col_from_vals(outs).map(|c| Val::Vec(Rc::new(c))).map_err(bad)
                }
                _ => fail("map needs (fun, vec)", sp),
            }
        }
        Map2 => {
            let f = std::mem::take(&mut args[0]);
            let a = std::mem::take(&mut args[1]);
            let b = std::mem::take(&mut args[2]);
            match (a, b) {
                (Val::Vec(ca), Val::Vec(cb)) => {
                    if ca.len != cb.len {
                        return fail(format!("map2 length mismatch: {} vs {}", ca.len, cb.len), sp);
                    }
                    let outs: Vec<Val> = (0..ca.len)
                        .map(|i| apply(cx, &f, &mut [col_elem(&ca, i), col_elem(&cb, i)], sp))
                        .collect::<Result<Vec<_>, _>>()?;
                    ops::col_from_vals(outs).map(|c| Val::Vec(Rc::new(c))).map_err(bad)
                }
                _ => fail("map2 needs (fun, vec, vec)", sp),
            }
        }
        Fold => {
            let f = std::mem::take(&mut args[0]);
            let mut acc = std::mem::take(&mut args[1]);
            let v = std::mem::take(&mut args[2]);
            match v {
                Val::Vec(c) => {
                    for i in 0..c.len {
                        acc = apply(cx, &f, &mut [std::mem::take(&mut acc), col_elem(&c, i)], sp)?;
                    }
                    Ok(acc)
                }
                _ => fail("fold needs (fun, init, vec)", sp),
            }
        }
        Scan => {
            let f = std::mem::take(&mut args[0]);
            let mut acc = std::mem::take(&mut args[1]);
            let v = std::mem::take(&mut args[2]);
            match v {
                Val::Vec(c) => {
                    let mut outs = Vec::with_capacity(c.len);
                    for i in 0..c.len {
                        acc = apply(cx, &f, &mut [std::mem::take(&mut acc), col_elem(&c, i)], sp)?;
                        outs.push(acc.clone());
                    }
                    ops::col_from_vals(outs).map(|c| Val::Vec(Rc::new(c))).map_err(bad)
                }
                _ => fail("scan needs (fun, init, vec)", sp),
            }
        }
        Filter => {
            let f = std::mem::take(&mut args[0]);
            let v = std::mem::take(&mut args[1]);
            match v {
                Val::Vec(c) => {
                    let mut kept = Vec::new();
                    for i in 0..c.len {
                        let e = col_elem(&c, i);
                        if apply(cx, &f, &mut [e.clone()], sp)? == Val::Bit(true) {
                            kept.push(e);
                        }
                    }
                    ops::col_from_vals(kept).map(|c| Val::Vec(Rc::new(c))).map_err(bad)
                }
                _ => fail("filter needs (fun, vec)", sp),
            }
        }
        Group => {
            let t = std::mem::take(&mut args[0]);
            let k = std::mem::take(&mut args[1]);
            match (&t, &k) {
                (Val::Tab(t), Val::Vec(c)) if ops::is_u8_col(c) => {
                    ops::group(t, &ops::col_bytes(c)).map_err(bad)
                }
                _ => fail("group needs (tab, 'key)", sp),
            }
        }
        // Branchless ternary — the language's conditional. A scalar bit picks
        // `a`/`b` whole; a `[bit]` mask picks elementwise. Both branches are
        // always evaluated (no short-circuit); nil selects `b`.
        Select => {
            let t = std::mem::take(&mut args[1]);
            let e = std::mem::take(&mut args[2]);
            match &args[0] {
                Val::Vec(m) => ops::select(m, t, e).map_err(bad),
                Val::Bit(true) => Ok(t),
                Val::Bit(false) | Val::Nil => Ok(e),
                _ => fail("select needs (bit or [bit], a, b)", sp),
            }
        }
        // Dynamic tab lookup by a runtime key: value, or nil if absent.
        Get => {
            match (&args[0], &args[1]) {
                (Val::Tab(t), Val::Vec(c)) if ops::is_u8_col(c) => {
                    Ok(t.get(&ops::col_bytes(c)).cloned().unwrap_or(Val::Nil))
                }
                _ => fail("get needs (tab, key)", sp),
            }
        }
        // Reflection (read-only): the current environment / a closure, as tabs.
        Env => {
            Ok(Val::Tab(env.clone()))
        }
        Reflect => {
            match std::mem::take(&mut args[0]) {
                Val::Fun(clo) => Ok(reflect_closure(&clo)),
                v => fail(format!("reflect needs a fun, got {}", fmt_ty(&crate::print::val_ty(&v))), sp),
            }
        }
        // ---- (de)serialization: value <-> text <-> binary, and source <-> AST ----
        Show => {
            Ok(u8s(crate::print::fmt_val(&args[0]).as_bytes()))
        }
        Encode => {
            let mut out = Vec::new();
            crate::wire::encode_val(&args[0], &mut out);
            Ok(u8s(&out))
        }
        Decode => {
            let bytes = as_u8s(&args[0], "decode", sp)?;
            let mut rd = crate::wire::Rd::new(&bytes);
            crate::wire::decode_val(&mut rd).map_err(bad)
        }
        Parse => {
            let bytes = as_u8s(&args[0], "parse", sp)?;
            let src = String::from_utf8_lossy(&bytes);
            match crate::parse::parse_unit(&src) {
                Ok(ds) => ops::col_from_vals(ds.iter().map(crate::wire::ast_to_val).collect())
                    .map(|c| Val::Vec(Rc::new(c)))
                    .map_err(bad),
                Err(e) => fail(format!("parse error: {}", e.msg), sp),
            }
        }
        Unparse => {
            match &args[0] {
                // a vec of declaration nodes -> a program's source
                Val::Vec(c) => {
                    let ds = (0..c.len)
                        .map(|i| crate::wire::val_to_ast(&col_elem(c, i)))
                        .collect::<Result<Vec<_>, _>>()
                        .map_err(bad)?;
                    Ok(u8s(crate::print::fmt_program(&ds).as_bytes()))
                }
                // a single AST node tab -> one expression's source
                Val::Tab(_) => {
                    let n = crate::wire::val_to_ast(&args[0]).map_err(bad)?;
                    Ok(u8s(crate::print::fmt_node(&n, 0).as_bytes()))
                }
                _ => fail("unparse needs an AST tab or a [tab] of declarations", sp),
            }
        }
    }
}

fn u8s(b: &[u8]) -> Val {
    Val::Vec(Rc::new(crate::value::Col::u8s(b)))
}
fn as_u8s(v: &Val, who: &str, sp: Span) -> Result<Vec<u8>, EErr> {
    match v {
        Val::Vec(c) if ops::is_u8_col(c) => Ok(ops::col_bytes(c)),
        _ => fail(format!("{who} needs a [u8]"), sp),
    }
}

// A closure reified as a tab: its code and captured environment as data.
fn reflect_closure(clo: &Clo) -> Val {
    let mut params = Tab::default();
    for (x, t) in &clo.params {
        params.bind(x.clone(), crate::wire::ty_to_val(t), None);
    }
    let mut t = Tab::default();
    t.bind(Bytes::str("params"), Val::Tab(Rc::new(params)), None);
    t.bind(Bytes::str("ret"), crate::wire::ty_to_val(&clo.ret), None);
    t.bind(Bytes::str("body"), crate::wire::ast_to_val(&clo.body), None);
    t.bind(Bytes::str("env"), Val::Tab(clo.env.clone()), None);
    Val::Tab(Rc::new(t))
}

// ---------- dynamic type tests & coercion ----------

// Resolve a named type in `env` to (base type, predicate).
fn resolve_type(env: &Rc<Tab>, n: &Sym, sp: Span) -> Result<(Ty, Val), EErr> {
    match env.get(n.bytes()) {
        Some(Val::Tab(t)) => {
            let base = t.get(b"type").and_then(crate::wire::val_to_ty);
            let pred = t.get(b"pred");
            match (base, pred) {
                (Some(b), Some(p)) => Ok((b, p.clone())),
                _ => fail(format!("`{:?}` is not a type", n), sp),
            }
        }
        _ => fail(format!("unbound type `{:?}`", n), sp),
    }
}

// Structural subtyping: is every value of type `a` also a value of type `b`?
// Records are width- and depth-covariant; funs are contravariant in arguments
// and covariant in results; a named refinement sits below its base. Used by
// coerce/scalar_is so a function's *signature* is checked, not just that it is
// callable — which is what makes self-application (`x(x)`) untypeable and so
// keeps evaluation terminating.
pub fn subtype(env: &Rc<Tab>, a: &Ty, b: &Ty, sp: Span) -> Result<bool, EErr> {
    if a == b {
        return Ok(true);
    }
    if let Ty::Union(bs) = b {
        for bi in bs {
            if subtype(env, a, bi, sp)? {
                return Ok(true);
            }
        }
    }
    match (a, b) {
        (Ty::Union(as_), _) => {
            for ai in as_ {
                if !subtype(env, ai, b, sp)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (Ty::Name(n), _) => {
            let base = if builtin_type(n.bytes()) {
                Ty::Vec(Box::new(Ty::U8))
            } else {
                resolve_type(env, n, sp)?.0
            };
            subtype(env, &base, b, sp)
        }
        (Ty::Vec(x), Ty::Vec(y)) => subtype(env, x, y, sp),
        (Ty::Tab(fa), Ty::Tab(fb)) => {
            for (k, tb) in fb {
                match fa.iter().find(|(k2, _)| k2 == k) {
                    Some((_, ta)) => {
                        if !subtype(env, ta, tb, sp)? {
                            return Ok(false);
                        }
                    }
                    None => return Ok(false),
                }
            }
            Ok(true)
        }
        (Ty::Fun(pa, ra), Ty::Fun(pb, rb)) => {
            if pa.len() != pb.len() {
                return Ok(false);
            }
            for (x, y) in pa.iter().zip(pb) {
                if !subtype(env, y, x, sp)? {
                    return Ok(false); // arguments are contravariant
                }
            }
            subtype(env, ra, rb, sp)
        }
        _ => Ok(false),
    }
}

fn scalar_is(cx: &mut Cx, env: &Rc<Tab>, v: &Val, t: &Ty, sp: Span) -> Result<bool, EErr> {
    Ok(match t {
        Ty::Nil => matches!(v, Val::Nil),
        Ty::Bit => matches!(v, Val::Bit(_)),
        Ty::I64 => matches!(v, Val::I64(_)),
        Ty::F64 => matches!(v, Val::F64(_)),
        Ty::U8 => matches!(v, Val::U8(_)),
        Ty::Tab(_) => matches!(v, Val::Tab(_)),
        // callable *and* signature-compatible — see subtype
        Ty::Fun(_, _) => {
            matches!(v, Val::Fun(_) | Val::Prim(_)) && subtype(env, &crate::print::val_ty(v), t, sp)?
        }
        Ty::Vec(_) => matches!(v, Val::Vec(_)),
        Ty::Union(ts) => {
            for t in ts {
                if scalar_is(cx, env, v, t, sp)? {
                    return Ok(true);
                }
            }
            false
        }
        Ty::Name(n) => {
            if let Some(ok) = native_refinement(n.bytes(), v) {
                ok
            } else {
                let (base, pred) = resolve_type(env, n, sp)?;
                if !scalar_is(cx, env, v, &base, sp)? {
                    false
                } else {
                    match apply(cx, &pred, &mut [v.clone()], sp)? {
                        Val::Bit(b) => b,
                        _ => return fail("predicate must return bit", sp),
                    }
                }
            }
        }
    })
}

// Built-in refinement types over [u8]: `str` (valid UTF-8) and `sym` (a
// non-empty identifier, [a-zA-Z0-9_], not starting with a digit). Native
// because a loopless language can't express the utf8 / charset scan.
pub fn builtin_type(name: &[u8]) -> bool {
    name == b"str" || name == b"sym"
}
fn native_refinement(name: &[u8], v: &Val) -> Option<bool> {
    let bytes = match v {
        Val::Vec(c) if crate::ops::is_u8_col(c) => crate::ops::col_bytes(c),
        _ => return matches!(name, b"str" | b"sym").then_some(false),
    };
    match name {
        b"str" => Some(std::str::from_utf8(&bytes).is_ok()),
        b"sym" => Some(crate::value::Bytes::new(&bytes).is_ident()),
        _ => None,
    }
}

fn is_test(cx: &mut Cx, env: &Rc<Tab>, v: &Val, t: &Ty, sp: Span) -> EResult {
    // A vec tested against a *scalar* element type tests elementwise (`col is
    // i64`); tested against a vector type (`s is str`) it is a whole-value test.
    match v {
        Val::Vec(c) if !is_vec_type(env, t, sp)? => {
            let mut bits = Bits::default();
            for i in 0..c.len {
                let e = col_elem(c, i);
                bits.push(scalar_is(cx, env, &e, t, sp)?);
            }
            Ok(Val::Vec(Rc::new(crate::value::Col::simple(Payload::Bits(bits)))))
        }
        v => Ok(Val::Bit(scalar_is(cx, env, v, t, sp)?)),
    }
}

// Does T denote a vector type (so `is`/testing applies to the whole value)?
fn is_vec_type(env: &Rc<Tab>, t: &Ty, sp: Span) -> Result<bool, EErr> {
    Ok(match t {
        Ty::Vec(_) => true,
        Ty::Name(n) if builtin_type(n.bytes()) => true, // str = [u8]
        Ty::Name(n) => is_vec_type(env, &resolve_type(env, n, sp)?.0, sp)?,
        _ => false,
    })
}

// Ascription: check v against T (running predicates), and normalize the
// representation of vecs (case order, nil bitmap) to T.
pub fn coerce(cx: &mut Cx, env: &Rc<Tab>, v: Val, t: &Ty, sp: Span) -> EResult {
    match (t, v) {
        // fast path: a scalar already of the exact prim type needs no coercion
        (Ty::I64, v @ Val::I64(_)) => Ok(v),
        (Ty::F64, v @ Val::F64(_)) => Ok(v),
        (Ty::Bit, v @ Val::Bit(_)) => Ok(v),
        (Ty::U8, v @ Val::U8(_)) => Ok(v),
        (Ty::Nil, v @ Val::Nil) => Ok(v),
        (Ty::Name(n), v) if native_refinement(n.bytes(), &v).is_some() => {
            if native_refinement(n.bytes(), &v) == Some(true) {
                Ok(v)
            } else {
                fail(format!("value fails type `{:?}`", n), sp)
            }
        }
        (Ty::Name(n), v) => {
            let (base, pred) = resolve_type(env, n, sp)?;
            let v = coerce(cx, env, v, &base, sp)?;
            match apply(cx, &pred, &mut [v.clone()], sp)? {
                Val::Bit(true) => Ok(v),
                Val::Bit(false) => fail(format!("value fails predicate `{:?}`", n), sp),
                _ => fail("predicate must return bit", sp),
            }
        }
        (Ty::Vec(et), Val::Vec(c)) => {
            // named element types: run predicate elementwise on the base rep
            let rep = strip_names(env, et, sp)?;
            let out = ops::coerce_col(&c, &rep).map_err(|m| EErr { msg: m, span: sp })?;
            if contains_name(et) {
                for i in 0..out.len {
                    let e = col_elem(&out, i);
                    if e != Val::Nil && !scalar_is(cx, env, &e, et, sp)? {
                        return fail(format!("element {} fails type {}", fmt_val(&e), fmt_ty(et)), sp);
                    }
                }
            }
            Ok(Val::Vec(Rc::new(out)))
        }
        (Ty::Tab(fields), Val::Tab(tv)) => {
            // width subtyping: required fields must exist and coerce; extras stay
            let mut out = (*tv).clone();
            for (k, ft) in fields {
                match tv.get(k.bytes()) {
                    Some(fv) => {
                        let cv = coerce(cx, env, fv.clone(), ft, sp)?;
                        out.bind(k.clone(), cv, None);
                    }
                    None => return fail(format!("missing field `{:?}`", k), sp),
                }
            }
            Ok(Val::Tab(Rc::new(out)))
        }
        (Ty::Union(ts), v) => {
            // Recurse into the matching member so aggregate members (e.g. the
            // `[i64]` in `[i64]?`) get their deep element/field checks, not just
            // a kind test. Prim members coerce trivially.
            for member in ts {
                if scalar_is(cx, env, &v, member, sp)? {
                    return coerce(cx, env, v, member, sp);
                }
            }
            fail(format!("value {} fails type {}", fmt_val(&v), fmt_ty(t)), sp)
        }
        (t, v) => {
            if scalar_is(cx, env, &v, t, sp)? {
                Ok(v)
            } else {
                fail(format!("value {} fails type {}", fmt_val(&v), fmt_ty(t)), sp)
            }
        }
    }
}

fn contains_name(t: &Ty) -> bool {
    match t {
        Ty::Name(_) => true,
        Ty::Union(ts) => ts.iter().any(contains_name),
        Ty::Vec(t) => contains_name(t),
        _ => false,
    }
}

// Replace named types with their bases (for representation purposes).
fn strip_names(env: &Rc<Tab>, t: &Ty, sp: Span) -> Result<Ty, EErr> {
    Ok(match t {
        Ty::Name(n) if builtin_type(n.bytes()) => Ty::Vec(Box::new(Ty::U8)), // str represents as [u8]
        Ty::Name(n) => {
            let (base, _) = resolve_type(env, n, sp)?;
            strip_names(env, &base, sp)?
        }
        Ty::Union(ts) => {
            let parts = ts.iter().map(|t| strip_names(env, t, sp)).collect::<Result<Vec<_>, _>>()?;
            crate::parse::union_of(parts)
        }
        Ty::Vec(t) => Ty::Vec(Box::new(strip_names(env, t, sp)?)),
        t => t.clone(),
    })
}

// ---------- free variables (for closure capture) ----------

// Free variables of a fun node: names the body references that are not
// params, builtins, or keywords — including type names. Preorder,
// first-occurrence order (pinned for cross-implementation determinism).
pub fn free_vars(n: &Node) -> Vec<Sym> {
    let mut out = Vec::new();
    let mut bound: Vec<Sym> = Vec::new();
    if let Ast::Fun { params, ret, body } = &n.ast {
        for (x, t) in params {
            ty_names(t, &bound, &mut out);
            bound.push(x.clone());
        }
        ty_names(ret, &bound, &mut out);
        walk(body, &mut bound, &mut out);
    }
    out
}

// The type names a `type` value's base refers to (empty for anything else).
// A `type` evaluates to a tab of its base type and its predicate; the base may
// name other `type`s, and those have to travel with it into a closure.
fn type_deps(v: &Val) -> Vec<Sym> {
    let mut out = Vec::new();
    if let Val::Tab(t) = v {
        if t.get(b"pred").is_some() {
            if let Some(base) = t.get(b"type").and_then(crate::wire::val_to_ty) {
                ty_names(&base, &[], &mut out);
            }
        }
    }
    out
}

fn note(x: &Sym, bound: &[Sym], out: &mut Vec<Sym>) {
    if op_by_name(x.bytes()).is_some() {
        return;
    }
    if bound.iter().any(|b| b == x) || out.iter().any(|o| o == x) {
        return;
    }
    out.push(x.clone());
}

fn ty_names(t: &Ty, bound: &[Sym], out: &mut Vec<Sym>) {
    match t {
        Ty::Name(n) => note(n, bound, out),
        Ty::Vec(t) => ty_names(t, bound, out),
        Ty::Union(ts) => ts.iter().for_each(|t| ty_names(t, bound, out)),
        Ty::Tab(fs) => fs.iter().for_each(|(_, t)| ty_names(t, bound, out)),
        Ty::Fun(args, r) => {
            args.iter().for_each(|t| ty_names(t, bound, out));
            ty_names(r, bound, out);
        }
        _ => {}
    }
}

fn walk(n: &Node, bound: &mut Vec<Sym>, out: &mut Vec<Sym>) {
    match &n.ast {
        Ast::Lit(_) => {}
        Ast::Var(x) => note(x, bound, out),
        Ast::Proj(e, _) | Ast::Err(e) => walk(e, bound, out),
        Ast::Idx(a, b) | Ast::Try(a, b) => {
            walk(a, bound, out);
            walk(b, bound, out);
        }
        Ast::App(f, args) => {
            walk(f, bound, out);
            args.iter().for_each(|a| walk(a, bound, out));
        }
        Ast::VecL(es) => es.iter().for_each(|e| walk(e, bound, out)),
        Ast::TabL(fs) => fs.iter().for_each(|(_, e)| walk(e, bound, out)),
        Ast::Fun { params, ret, body } => {
            let depth = bound.len();
            for (x, t) in params {
                ty_names(t, bound, out);
                bound.push(x.clone());
            }
            ty_names(ret, bound, out);
            walk(body, bound, out);
            bound.truncate(depth);
        }
        Ast::If(a, b, c) => {
            walk(a, bound, out);
            walk(b, bound, out);
            walk(c, bound, out);
        }
        Ast::Is(e, t) | Ast::As(e, t) => {
            walk(e, bound, out);
            ty_names(t, bound, out);
        }
        Ast::Seq(ds) => {
            let depth = bound.len();
            for d in ds {
                match &d.ast {
                    Ast::Let { x, ty, e, .. } => {
                        if let Some(t) = ty {
                            ty_names(t, bound, out);
                        }
                        walk(e, bound, out);
                        bound.push(x.clone());
                    }
                    Ast::Type { x, base, pred, .. } => {
                        ty_names(base, bound, out);
                        walk(pred, bound, out);
                        bound.push(x.clone());
                    }
                    Ast::Use { x, .. } => bound.push(x.clone()),
                    _ => walk(d, bound, out),
                }
            }
            bound.truncate(depth);
        }
        Ast::Let { ty, e, .. } => {
            if let Some(t) = ty {
                ty_names(t, bound, out);
            }
            walk(e, bound, out);
        }
        Ast::Type { base, pred, .. } => {
            ty_names(base, bound, out);
            walk(pred, bound, out);
        }
        Ast::Use { .. } => {}
    }
}
