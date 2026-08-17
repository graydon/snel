// Static type checker, run before evaluation. It infers a type for every
// expression and checks it, guaranteeing three things the language leans on:
// every name resolves to an *earlier* binding (no recursion, hence, with the
// application rule below, termination); every call is arity-correct; and every
// application is type-correct — the callee is a function and each argument is a
// subtype of the corresponding parameter. That last rule is what makes
// self-application (`x(x)`) untypeable, closing the one route to non-terminating
// recursion that first-class functions would otherwise open.
//
// Types are inferred as `Option<Ty>`: `None` means "statically unknown", used
// where the vectorised, nil-propagating value model is genuinely hard to type
// (most numeric/aggregate builtins). Unknown is permissive — it never forces a
// rejection — so the checker has no false positives while still catching the
// structural errors above. Exact conformance for ascriptions and parameter
// bindings (predicate subtypes, union/nil normalisation) remains where it must
// be exact: at the runtime `coerce` those forms compile to.

use crate::ast::{op_by_name, Ast, Node, Op, Span, Ty};
use crate::print::fmt_ty;
use crate::value::Sym;

pub struct CErr {
    pub msg: String,
    pub span: Span,
}

struct Scope<'a> {
    vars: Vec<(Sym, Option<Ty>)>, // term name -> type (None = unknown)
    types: Vec<(Sym, Ty)>,        // type name -> base (for refinements)
    // resolve a `use`d unit name to its interface (tab) type; None = unknown
    resolve_use: &'a dyn Fn(&Sym) -> Option<Ty>,
}

pub fn check_unit(ds: &[Node], toplevel: &[Sym]) -> Result<(), CErr> {
    check_unit_with(ds, toplevel, &|_| None)
}

// As `check_unit`, but with a resolver that supplies the interface type of a
// `use`d unit (so imported names type precisely instead of gradually). The
// caller loads the import and derives its type from the module value.
pub fn check_unit_with(
    ds: &[Node],
    toplevel: &[Sym],
    resolve_use: &dyn Fn(&Sym) -> Option<Ty>,
) -> Result<(), CErr> {
    let mut sc = Scope {
        vars: toplevel.iter().map(|n| (n.clone(), None)).collect(),
        types: Vec::new(),
        resolve_use,
    };
    for d in ds {
        check_decl(&mut sc, d)?;
    }
    Ok(())
}

fn err<T>(msg: impl Into<String>, span: Span) -> Result<T, CErr> {
    Err(CErr { msg: msg.into(), span })
}

fn name_of(b: &Sym) -> String {
    String::from_utf8_lossy(b.bytes()).into_owned()
}

// ---------- subtyping ----------

// Resolve a named type to its base (str/sym over [u8]; a `type` alias to its
// base). None if the name is not a known type — treated permissively by `sub`.
fn resolve_base(sc: &Scope, n: &Sym) -> Option<Ty> {
    if crate::eval::builtin_type(n.bytes()) {
        return Some(Ty::Vec(Box::new(Ty::U8)));
    }
    sc.types.iter().rev().find(|(x, _)| x == n).map(|(_, b)| b.clone())
}

// Structural subtyping: width/depth-covariant records, contravariant-arg /
// covariant-result funs, refinement below its base. An unresolvable named type
// is treated as compatible (permissive) so unknown module/`use` types never
// force a false rejection.
fn sub(sc: &Scope, a: &Ty, b: &Ty) -> bool {
    if a == b {
        return true;
    }
    if let Ty::Union(bs) = b {
        if bs.iter().any(|bi| sub(sc, a, bi)) {
            return true;
        }
    }
    match (a, b) {
        (Ty::Union(as_), _) => as_.iter().all(|ai| sub(sc, ai, b)),
        // An unresolvable type name rejects rather than permits: `check_ty`
        // already proves every annotated name resolves, so this only fires on
        // an impossible case, and rejecting there can never re-open recursion.
        (Ty::Name(n), _) => resolve_base(sc, n).map_or(false, |base| sub(sc, &base, b)),
        (_, Ty::Name(n)) => resolve_base(sc, n).map_or(false, |base| sub(sc, a, &base)),
        (Ty::Vec(x), Ty::Vec(y)) => sub(sc, x, y),
        (Ty::Tab(fa), Ty::Tab(fb)) => fb.iter().all(|(k, tb)| {
            fa.iter().find(|(k2, _)| k2 == k).map_or(false, |(_, ta)| sub(sc, ta, tb))
        }),
        (Ty::Fun(pa, ra), Ty::Fun(pb, rb)) => {
            pa.len() == pb.len()
                && pa.iter().zip(pb).all(|(x, y)| sub(sc, y, x))
                && sub(sc, ra, rb)
        }
        _ => false,
    }
}

// Follow names to a record type's fields, if any.
fn as_tab(sc: &Scope, t: &Ty) -> Option<Vec<(Sym, Ty)>> {
    match t {
        Ty::Tab(fs) => Some(fs.clone()),
        Ty::Name(n) => resolve_base(sc, n).and_then(|b| as_tab(sc, &b)),
        _ => None,
    }
}

// Follow a chain of `type` names down to the type underneath. Bounded, so a
// pathological alias that names itself cannot spin.
fn deref_name(sc: &Scope, t: &Ty) -> Option<Ty> {
    let mut cur = t.clone();
    for _ in 0..16 {
        match cur {
            Ty::Name(ref n) => cur = resolve_base(sc, n)?,
            other => return Some(other),
        }
    }
    None
}

fn is_vec_ty(sc: &Scope, t: &Ty) -> bool {
    match t {
        Ty::Vec(_) => true,
        Ty::Name(n) => {
            crate::eval::builtin_type(n.bytes())
                || matches!(resolve_base(sc, n), Some(b) if is_vec_ty(sc, &b))
        }
        _ => false,
    }
}

fn elem_of(t: &Ty) -> Ty {
    match t {
        Ty::Vec(e) => (**e).clone(),
        other => other.clone(),
    }
}

// Least upper bound where a mismatch is permissible (e.g. `select` branches):
// precise only when both agree, else gradual.
fn join(a: Option<Ty>, b: Option<Ty>) -> Option<Ty> {
    match (a, b) {
        (Some(a), Some(b)) if a == b => Some(a),
        _ => None,
    }
}

// `if`/`try` arms: the result is the arms' common type — the same type if they
// agree, or the wider one when one refines/subtypes the other (so `pos`/`i64`
// join to `i64`). Two *incompatible* known types are a hard error: mixing them
// across a conditional is almost always a bug; ascribe both arms to a union to
// opt in. One unknown arm stays gradual (we can't prove a mismatch).
fn branch_join(sc: &Scope, a: Option<Ty>, b: Option<Ty>, sp: Span) -> Result<Option<Ty>, CErr> {
    match (a, b) {
        (Some(x), Some(y)) => {
            if x == y || sub(sc, &x, &y) {
                Ok(Some(y)) // agree, or x refines/subtypes y -> the wider y
            } else if sub(sc, &y, &x) {
                Ok(Some(x))
            } else {
                err(
                    format!(
                        "branches have incompatible types ({} vs {}); ascribe both arms to a union if intended",
                        fmt_ty(&x),
                        fmt_ty(&y)
                    ),
                    sp,
                )
            }
        }
        _ => Ok(None),
    }
}

// ---------- inference ----------

fn check_ty(sc: &Scope, t: &Ty, sp: Span) -> Result<(), CErr> {
    match t {
        Ty::Name(n) => {
            if crate::eval::builtin_type(n.bytes()) || sc.types.iter().any(|(x, _)| x == n) {
                Ok(())
            } else {
                err(format!("unknown type `{}`", name_of(n)), sp)
            }
        }
        Ty::Vec(t) => check_ty(sc, t, sp),
        Ty::Union(ts) => ts.iter().try_for_each(|t| check_ty(sc, t, sp)),
        Ty::Tab(fs) => fs.iter().try_for_each(|(_, t)| check_ty(sc, t, sp)),
        Ty::Fun(args, r) => {
            args.iter().try_for_each(|t| check_ty(sc, t, sp))?;
            check_ty(sc, r, sp)
        }
        _ => Ok(()),
    }
}

// Elementwise typing: a scalar operation lifted over two structural functors,
// `[·]` (broadcast) and `·?` (nil-propagation). This types the monomorphic and
// nil cases precisely; a genuine multi-case union operand yields None (gradual),
// because using it would need occurrence typing to narrow first.
#[derive(PartialEq)]
enum Shape {
    Scalar,
    Vec,
    Unknown,
}

fn shape(sc: &Scope, t: &Ty) -> Shape {
    match t {
        Ty::Vec(_) => Shape::Vec,
        Ty::Nil | Ty::Bit | Ty::I64 | Ty::F64 | Ty::U8 => Shape::Scalar,
        Ty::Union(ts) => {
            if ts.iter().all(|t| shape(sc, t) == Shape::Scalar) {
                Shape::Scalar
            } else if ts.iter().all(|t| shape(sc, t) == Shape::Vec) {
                Shape::Vec
            } else {
                Shape::Unknown
            }
        }
        Ty::Name(n) => resolve_base(sc, n).map_or(Shape::Unknown, |b| shape(sc, &b)),
        _ => Shape::Unknown, // tab, fun
    }
}

// A clean numeric operand as (base ∈ {i64,f64}, is_vec, nilable), else None.
// A named type is resolved to its base first, so arithmetic and the numeric
// reductions see through a `type` alias over a numeric base (e.g. `pos = i64`).
fn peel_num(sc: &Scope, t: &Ty) -> Option<(Ty, bool, bool)> {
    fn scalar(sc: &Scope, t: &Ty) -> Option<(Ty, bool)> {
        match t {
            Ty::I64 | Ty::F64 => Some((t.clone(), false)),
            Ty::Union(ts) if ts.len() == 2 => match (&ts[0], &ts[1]) {
                (b @ (Ty::I64 | Ty::F64), Ty::Nil) | (Ty::Nil, b @ (Ty::I64 | Ty::F64)) => {
                    Some((b.clone(), true))
                }
                _ => None,
            },
            Ty::Name(n) => scalar(sc, &resolve_base(sc, n)?),
            _ => None,
        }
    }
    match t {
        Ty::Vec(e) => scalar(sc, e).map(|(b, n)| (b, true, n)),
        Ty::Name(n) => peel_num(sc, &resolve_base(sc, n)?),
        _ => scalar(sc, t).map(|(b, n)| (b, false, n)),
    }
}

fn recompose(base: Ty, is_vec: bool, nil: bool) -> Ty {
    let elem = if nil { crate::parse::union_of(vec![base, Ty::Nil]) } else { base };
    if is_vec {
        Ty::Vec(Box::new(elem))
    } else {
        elem
    }
}

// `a op b` where op is closed over a numeric base: result is that base, a vector
// if either operand is, nil-admitting if either operand is. Mismatched or
// non-clean operands (e.g. a real union) fall back to None.
fn num_binop(sc: &Scope, a: &Option<Ty>, b: &Option<Ty>) -> Option<Ty> {
    let (ba, va, na) = peel_num(sc, a.as_ref()?)?;
    let (bb, vb, nb) = peel_num(sc, b.as_ref()?)?;
    if ba != bb {
        return None;
    }
    Some(recompose(ba, va || vb, na || nb))
}

// bit / [bit]-producing ops (compare, boolean, isnil): [bit] if any operand is a
// vector, else bit; never nil (comparison is total). None if a shape is unclear.
fn bit_result(sc: &Scope, args: &[Option<Ty>]) -> Option<Ty> {
    let mut is_vec = false;
    for a in args {
        match shape(sc, a.as_ref()?) {
            Shape::Unknown => return None,
            Shape::Vec => is_vec = true,
            Shape::Scalar => {}
        }
    }
    Some(if is_vec { Ty::Vec(Box::new(Ty::Bit)) } else { Ty::Bit })
}

fn as_vec_ty(t: &Option<Ty>) -> Option<Ty> {
    matches!(t, Some(Ty::Vec(_))).then(|| t.clone()).flatten()
}
fn vec_elem(t: &Option<Ty>) -> Option<Ty> {
    match t {
        Some(Ty::Vec(e)) => Some((**e).clone()),
        _ => None,
    }
}
// Result type of a builtin given its argument types. None = gradual/unknown.
fn builtin_result(sc: &Scope, op: Op, args: &[Option<Ty>]) -> Option<Ty> {
    use Op::*;
    let vec = |t: Ty| Ty::Vec(Box::new(t));
    match op {
        Add | Sub | Mul | Div | Rem => num_binop(sc, &args[0], &args[1]),
        Neg | Abs | Sign => {
            let (b, v, n) = peel_num(sc, args[0].as_ref()?)?;
            Some(recompose(b, v, n))
        }
        Itof => {
            let (b, v, n) = peel_num(sc, args[0].as_ref()?)?;
            (b == Ty::I64).then(|| recompose(Ty::F64, v, n))
        }
        Ftoi | Sqrt | Floor | Ceil => {
            let (b, v, n) = peel_num(sc, args[0].as_ref()?)?;
            let out = if op == Ftoi { Ty::I64 } else { Ty::F64 };
            (b == Ty::F64).then(|| recompose(out, v, n))
        }
        // sum/prod reduce a numeric vector to its scalar base (nils are dropped,
        // so the result is never nil); min/max reduce to an element (like
        // first/last).
        Sum | Prod => {
            let (b, is_vec, _n) = peel_num(sc, args[0].as_ref()?)?;
            is_vec.then_some(b)
        }
        Min | Max => vec_elem(&args[0]),
        // cat concatenates two vectors; its elements are the union of the inputs'
        Cat => match (&args[0], &args[1]) {
            (Some(Ty::Vec(ea)), Some(Ty::Vec(eb))) => Some(Ty::Vec(Box::new(
                crate::parse::union_of(vec![(**ea).clone(), (**eb).clone()]),
            ))),
            _ => None,
        },
        Find => Some(crate::parse::union_of(vec![Ty::I64, Ty::Nil])), // position or nil
        Eq | Ne | Lt | Le | Gt | Ge | And | Or | Not | Isnil => bit_result(sc, args),
        All | Any | In => Some(Ty::Bit), // reductions / membership -> scalar bit
        Len => Some(Ty::I64),
        Iota | Grade | Which => Some(vec(Ty::I64)),
        Rev | Distinct => as_vec_ty(&args[0]),
        Take | Drop | Filter => as_vec_ty(&args[1]),
        First | Last => vec_elem(&args[0]),
        // map/map2/fold/scan/filter are typed in check_app (which sees the
        // function-argument node, so a bare builtin peels precisely)
        // select: a scalar-bit condition picks a whole branch (join of the two
        // branch types); a [bit] mask picks elementwise (vector of branch elems).
        Select if matches!(args[0], Some(Ty::Bit)) => join(args[1].clone(), args[2].clone()),
        Select => join(args[1].clone().map(|t| elem_of(&t)), args[2].clone().map(|t| elem_of(&t))).map(vec),
        Split => Some(vec(vec(Ty::U8))),
        Join | Show | Encode | Unparse | ToJson | ToCsv => Some(vec(Ty::U8)),
        // fromjson/fromcsv are shaped by their input data -> gradual (see _ arm)
        At => vec_elem(&args[1]),          // at(i, v): element of the vector
        Rep => args[1].clone().map(vec),   // n copies of a scalar
        Scatter => as_vec_ty(&args[2]),    // scatter(idx, vals, base): the base
        Shift => as_vec_ty(&args[2]),      // shift(k, fill, v): the shifted vector
        Sums | Prods => as_vec_ty(&args[0]), // prefix sums / products, same numeric type
        // sequence analysis: classify/locate/edges -> [bit]; cut/window -> [[T]]
        Member | Matches | Runs => Some(vec(Ty::Bit)),
        Partition | Windows => as_vec_ty(&args[1]).map(vec), // [T] -> [[T]]
        _ => None, // group/get/env/reflect/decode/parse
    }
}

// The result type of applying a *function argument* (of a higher-order builtin)
// to arguments of the given types. A bare builtin peels like a direct call —
// `builtin_result` on the element types, with an arity check — so `map(sum, v)`
// types as precisely as `map(fun(w) = sum(w), v)`. A closure uses its declared
// return type (unchanged); anything else is gradual.
fn fn_result(
    sc: &Scope,
    fnode: &Node,
    fty: &Option<Ty>,
    arg_tys: &[Option<Ty>],
) -> Result<Option<Ty>, CErr> {
    if let Ast::Var(name) = &fnode.ast {
        if let Some(op) = op_by_name(name.bytes()) {
            if op_arity(op) != arg_tys.len() {
                return err(
                    format!("`{}` takes {} args, got {}", name_of(name), op_arity(op), arg_tys.len()),
                    fnode.span,
                );
            }
            return Ok(builtin_result(sc, op, arg_tys));
        }
    }
    // a closure (or any fun value) is checked exactly like a direct call: arity,
    // then each element type against the corresponding parameter type.
    match fty {
        Some(Ty::Fun(params, ret)) => {
            if params.len() != arg_tys.len() {
                return err(
                    format!("function takes {} args, applied to {}", params.len(), arg_tys.len()),
                    fnode.span,
                );
            }
            for (i, (at, pt)) in arg_tys.iter().zip(params).enumerate() {
                if let Some(at) = at {
                    if !sub(sc, at, pt) {
                        return err(
                            format!("argument {} is {}, expected {}", i + 1, fmt_ty(at), fmt_ty(pt)),
                            fnode.span,
                        );
                    }
                }
            }
            Ok(Some((**ret).clone()))
        }
        _ => Ok(None), // a gradual function value
    }
}

fn check_app(sc: &mut Scope, f: &Node, args: &[Node], sp: Span) -> Result<Option<Ty>, CErr> {
    if let Ast::Var(name) = &f.ast {
        if let Some(op) = op_by_name(name.bytes()) {
            use Op::*;
            let want = op_arity(op);
            if args.len() != want {
                return err(
                    format!("`{}` takes {} args, got {}", name_of(name), want, args.len()),
                    sp,
                );
            }
            let mut arg_ts = Vec::with_capacity(args.len());
            for a in args {
                arg_ts.push(infer(sc, a)?);
            }
            let vec = |t: Ty| Ty::Vec(Box::new(t));
            // Higher-order ops apply their function argument to the elements of
            // their data argument(s); peel it there so a bare builtin (or a
            // closure) types precisely and its arity is checked statically.
            return Ok(match op {
                Map => fn_result(sc, &args[0], &arg_ts[0], &[vec_elem(&arg_ts[1])])?.map(vec),
                Map2 => fn_result(
                    sc,
                    &args[0],
                    &arg_ts[0],
                    &[vec_elem(&arg_ts[1]), vec_elem(&arg_ts[2])],
                )?
                .map(vec),
                Scan => fn_result(
                    sc,
                    &args[0],
                    &arg_ts[0],
                    &[arg_ts[1].clone(), vec_elem(&arg_ts[2])],
                )?
                .map(vec),
                Fold => fn_result(
                    sc,
                    &args[0],
                    &arg_ts[0],
                    &[arg_ts[1].clone(), vec_elem(&arg_ts[2])],
                )?,
                Filter => {
                    fn_result(sc, &args[0], &arg_ts[0], &[vec_elem(&arg_ts[1])])?; // arity-check the predicate
                    as_vec_ty(&arg_ts[1])
                }
                _ => builtin_result(sc, op, &arg_ts),
            });
        }
    }
    let ft = infer(sc, f)?;
    // a `type` alias over a function type is callable as that function type
    let ft = match &ft {
        Some(t @ Ty::Name(_)) => deref_name(sc, t),
        _ => ft,
    };
    let mut arg_ts = Vec::with_capacity(args.len());
    for a in args {
        arg_ts.push(infer(sc, a)?);
    }
    match ft {
        Some(Ty::Fun(params, ret)) => {
            if args.len() != params.len() {
                return err(format!("expected {} args, got {}", params.len(), args.len()), sp);
            }
            for (i, (at, pt)) in arg_ts.iter().zip(&params).enumerate() {
                if let Some(at) = at {
                    if !sub(sc, at, pt) {
                        return err(
                            format!("argument {} is {}, expected {}", i + 1, fmt_ty(at), fmt_ty(pt)),
                            args[i].span,
                        );
                    }
                }
            }
            Ok(Some(*ret))
        }
        Some(other) => err(format!("cannot call a value of type {}", fmt_ty(&other)), sp),
        None => Ok(None),
    }
}

fn infer(sc: &mut Scope, n: &Node) -> Result<Option<Ty>, CErr> {
    let sp = n.span;
    Ok(match &n.ast {
        Ast::Lit(v) => Some(crate::print::val_ty(v)),
        Ast::Var(x) => {
            if op_by_name(x.bytes()).is_some() {
                // a builtin used as a first-class value; gradually typed (a
                // direct call `f(args)` is still typed precisely, in check_app)
                None
            } else {
                match sc.vars.iter().rev().find(|(k, _)| k == x) {
                    Some((_, t)) => t.clone(),
                    None => return err(format!("unbound name `{}`", name_of(x)), sp),
                }
            }
        }
        Ast::Proj(e, x) => match infer(sc, e)? {
            Some(t) => match as_tab(sc, &t) {
                Some(fields) => match fields.iter().find(|(k, _)| k == x) {
                    Some((_, ft)) => Some(ft.clone()),
                    None => return err(format!("record has no field `{}`", name_of(x)), sp),
                },
                None => return err(format!("cannot project `.{}` from {}", name_of(x), fmt_ty(&t)), sp),
            },
            None => None,
        },
        Ast::Idx(e, i) => {
            let et = infer(sc, e)?;
            infer(sc, i)?;
            // A `type` name indexes as whatever it names — but the *result* is the
            // base type, not the name: indexing need not preserve a refinement
            // (a slice of a `str` need not be valid UTF-8).
            let et = match &et {
                Some(t @ Ty::Name(_)) => deref_name(sc, t),
                _ => et,
            };
            match &et {
                Some(Ty::Vec(_)) | Some(Ty::Tab(_)) | None => et,
                Some(other) => return err(format!("cannot index {}", fmt_ty(other)), sp),
            }
        }
        Ast::App(f, args) => check_app(sc, f, args, sp)?,
        Ast::VecL(es) => {
            let mut ts = Vec::with_capacity(es.len());
            for e in es {
                ts.push(infer(sc, e)?);
            }
            // all elements known: the vector's element type is their union (a
            // single case if they agree), matching the column the value builds.
            // Empty or an unknown element leaves it gradual.
            if !es.is_empty() && ts.iter().all(|t| t.is_some()) {
                let elems: Vec<Ty> = ts.into_iter().flatten().collect();
                Some(Ty::Vec(Box::new(crate::parse::union_of(elems))))
            } else {
                None
            }
        }
        Ast::TabL(fs) => {
            let mut fields = Vec::with_capacity(fs.len());
            let mut known = true;
            for (k, e) in fs {
                match infer(sc, e)? {
                    Some(t) => fields.push((k.clone(), t)),
                    None => known = false,
                }
            }
            if known {
                Some(Ty::Tab(fields))
            } else {
                None
            }
        }
        Ast::Fun { params, ret, body } => {
            for (_, t) in params {
                check_ty(sc, t, sp)?;
            }
            check_ty(sc, ret, sp)?;
            let depth = sc.vars.len();
            for (x, t) in params {
                sc.vars.push((x.clone(), Some(t.clone())));
            }
            let bt = infer(sc, body)?; // scope + application typing inside the body
            sc.vars.truncate(depth);
            if let Some(bt) = &bt {
                if !sub(sc, bt, ret) {
                    return err(format!("body is {}, declared return is {}", fmt_ty(bt), fmt_ty(ret)), body.span);
                }
            }
            Some(Ty::Fun(params.iter().map(|(_, t)| t.clone()).collect(), Box::new(ret.clone())))
        }
        Ast::If(c, a, b) => {
            let ct = infer(sc, c)?;
            let ta = infer(sc, a)?;
            let tb = infer(sc, b)?;
            match ct {
                Some(Ty::Bit) | None => branch_join(sc, ta, tb, sp)?, // scalar cond: pick one branch
                Some(_) => {
                    return err("if condition must be a scalar bit (use select for a [bit] mask)".to_string(), sp)
                }
            }
        }
        Ast::Try(a, b) => {
            let ta = infer(sc, a)?;
            let tb = infer(sc, b)?;
            branch_join(sc, ta, tb, sp)?
        }
        Ast::Err(e) => {
            infer(sc, e)?;
            None // `err` never returns
        }
        Ast::Is(e, t) => {
            let et = infer(sc, e)?;
            check_ty(sc, t, sp)?;
            match &et {
                // a vec tested against a scalar element type tests elementwise
                Some(Ty::Vec(_)) if !is_vec_ty(sc, t) => Some(Ty::Vec(Box::new(Ty::Bit))),
                _ => Some(Ty::Bit),
            }
        }
        Ast::As(e, t) => {
            infer(sc, e)?;
            check_ty(sc, t, sp)?;
            Some(t.clone()) // conformance is enforced at the runtime coercion
        }
        Ast::Seq(ds) => {
            let vdepth = sc.vars.len();
            let tdepth = sc.types.len();
            let mut last = None;
            for d in ds {
                last = check_decl(sc, d)?;
            }
            sc.vars.truncate(vdepth);
            sc.types.truncate(tdepth);
            last
        }
        Ast::Let { .. } | Ast::Type { .. } | Ast::Use { .. } => {
            check_decl(sc, n)?;
            None
        }
    })
}

fn check_decl(sc: &mut Scope, d: &Node) -> Result<Option<Ty>, CErr> {
    Ok(match &d.ast {
        Ast::Let { x, ty, e, .. } => {
            let et = infer(sc, e)?; // RHS sees only earlier names => no recursion
            let bound = match ty {
                Some(t) => {
                    check_ty(sc, t, d.span)?;
                    Some(t.clone())
                }
                None => et,
            };
            sc.vars.push((x.clone(), bound.clone()));
            bound
        }
        Ast::Type { x, base, pred, .. } => {
            check_ty(sc, base, d.span)?;
            infer(sc, pred)?;
            sc.types.push((x.clone(), base.clone()));
            None
        }
        Ast::Use { x, .. } => {
            let ty = (sc.resolve_use)(x);
            sc.vars.push((x.clone(), ty));
            None
        }
        _ => infer(sc, d)?,
    })
}

use crate::ast::op_arity;
