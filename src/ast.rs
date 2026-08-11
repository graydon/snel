// AST and types. One internal AST with a fixed bijection to canonical tabs
// (see wire.rs / print.rs). `mod` is desugared by the parser and has no node.

use crate::value::{Bytes, Sym, Val};
use std::rc::Rc;

#[derive(Clone, PartialEq, Debug)]
pub enum Ty {
    Nil,
    Bit,
    I64,
    F64,
    U8,
    Vec(Box<Ty>),
    Union(Vec<Ty>), // flattened, deduped, source order
    Tab(Vec<(Sym, Ty)>),
    Fun(Vec<Ty>, Box<Ty>),
    Name(Sym), // named predicate subtype; resolved via the checker's typ table
}

impl Ty {
    pub fn admits_nil(&self) -> bool {
        matches!(self, Ty::Nil) || matches!(self, Ty::Union(ts) if ts.iter().any(|t| *t == Ty::Nil))
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Span {
    pub lo: u32,
    pub hi: u32,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Node {
    pub ast: Ast,
    pub span: Span,
}

#[derive(Clone, PartialEq, Debug)]
pub enum Ast {
    Lit(Val),
    Var(Sym), // builtin names resolve here first; they are reserved
    Proj(Box<Node>, Sym),
    Idx(Box<Node>, Box<Node>),
    App(Box<Node>, Vec<Node>),
    VecL(Vec<Node>),
    TabL(Vec<(Sym, Node)>),
    Fun { params: Vec<(Sym, Ty)>, ret: Ty, body: Rc<Node> },
    If(Box<Node>, Box<Node>, Box<Node>), // scalar-bit condition only; lazy
    Try(Box<Node>, Box<Node>),
    Err(Box<Node>),
    Is(Box<Node>, Ty),
    As(Box<Node>, Ty), // ascription (e : T); checks e against T
    Seq(Vec<Node>), // declarations then final expression; value = last
    Let { x: Sym, ty: Option<Ty>, e: Box<Node>, doc: Option<Bytes>, public: bool },
    Typ { x: Sym, base: Ty, pred: Box<Node>, doc: Option<Bytes>, public: bool },
    // `use x` loads x.sn; `use x = "url"` loads a remote unit (optional feature)
    Use { x: Sym, url: Option<Bytes>, doc: Option<Bytes> },
}

// Builtin operators and functions: language-level, reserved, not env bindings.
// Canonical (encodable) names are the enum names lowercased.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Op {
    Add, Sub, Mul, Div, Rem, Neg, Abs, Itof, Ftoi,
    Sqrt, Floor, Ceil, Sign, Ord, Chr,
    Eq, Ne, Lt, Le, Gt, Ge,
    And, Or, Not,
    Len, Cat, Iota, Grade, Sum, Prod, Min, Max, Isnil, All, Any,
    Rev, Take, Drop, First, Last, Which, Distinct, In,
    Map, Map2, Fold, Scan, Filter, Group, Get, Select,
    Find, Split, Join,
    Env, Reflect, // reflection: current environment / a closure, as tabs
    Show, Encode, Decode, Parse, Unparse, // text/binary/source (de)serialization
    At, Rep, Scatter, // element access, constant fill, indexed amend
    Shift, Sums, Prods, // stencil shift-with-fill, prefix sum, prefix product
    // sequence analysis: classify, locate, segment, window (all vectorized)
    Member, Matches, Runs, Partition, Windows,
    // interop: JSON (nesting) and CSV (flat tables only)
    ToJson, FromJson, ToCsv, FromCsv,
}

pub const OPS: &[(Op, &str)] = &[
    (Op::Add, "add"), (Op::Sub, "sub"), (Op::Mul, "mul"), (Op::Div, "div"),
    (Op::Rem, "rem"), (Op::Neg, "neg"), (Op::Abs, "abs"), (Op::Itof, "itof"),
    (Op::Ftoi, "ftoi"), (Op::Sqrt, "sqrt"), (Op::Floor, "floor"),
    (Op::Ceil, "ceil"), (Op::Sign, "sign"), (Op::Ord, "ord"), (Op::Chr, "chr"),
    (Op::Eq, "eq"), (Op::Ne, "ne"),
    (Op::Lt, "lt"), (Op::Le, "le"), (Op::Gt, "gt"), (Op::Ge, "ge"),
    (Op::And, "and"), (Op::Or, "or"), (Op::Not, "not"), (Op::Len, "len"),
    (Op::Cat, "cat"), (Op::Iota, "iota"), (Op::Grade, "grade"),
    (Op::Sum, "sum"), (Op::Prod, "prod"), (Op::Min, "min"), (Op::Max, "max"),
    (Op::Isnil, "isnil"), (Op::All, "all"), (Op::Any, "any"),
    (Op::Rev, "rev"), (Op::Take, "take"), (Op::Drop, "drop"),
    (Op::First, "first"), (Op::Last, "last"), (Op::Which, "which"),
    (Op::Distinct, "distinct"), (Op::In, "in"), (Op::Map, "map"),
    (Op::Map2, "map2"), (Op::Fold, "fold"), (Op::Scan, "scan"),
    (Op::Filter, "filter"), (Op::Group, "group"), (Op::Get, "get"),
    (Op::Select, "select"),
    (Op::Find, "find"), (Op::Split, "split"), (Op::Join, "join"),
    (Op::Env, "locals"), (Op::Reflect, "reflect"), (Op::Show, "show"),
    (Op::Encode, "encode"), (Op::Decode, "decode"), (Op::Parse, "parse"),
    (Op::Unparse, "unparse"),
    (Op::At, "at"), (Op::Rep, "rep"), (Op::Scatter, "scatter"),
    (Op::Shift, "shift"), (Op::Sums, "sums"), (Op::Prods, "prods"),
    (Op::Member, "member"), (Op::Matches, "matches"), (Op::Runs, "runs"),
    (Op::Partition, "partition"), (Op::Windows, "windows"),
    (Op::ToJson, "tojson"), (Op::FromJson, "fromjson"),
    (Op::ToCsv, "tocsv"), (Op::FromCsv, "fromcsv"),
];

pub fn op_by_name(name: &[u8]) -> Option<Op> {
    OPS.iter().find(|(_, n)| n.as_bytes() == name).map(|(o, _)| *o)
}

// Argument count of a builtin (checked at direct calls, and at first-class
// application through a Prim value).
pub fn op_arity(op: Op) -> usize {
    use Op::*;
    match op {
        Env => 0,
        Neg | Abs | Itof | Ftoi | Sqrt | Floor | Ceil | Sign | Not | Len | Iota | Grade | Ord
        | Chr | Sum | Prod | Min | Max | Isnil | All | Any | Rev | First | Last | Which
        | Distinct | Reflect | Show | Encode | Decode | Parse | Unparse | Sums | Prods | Runs
        | ToJson | FromJson | ToCsv | FromCsv => 1,
        Fold | Scan | Map2 | Select | Scatter | Shift => 3,
        _ => 2, // arithmetic/compare pairs, cat, map/filter, member/matches/partition/windows, …
    }
}

pub fn op_name(op: Op) -> &'static str {
    OPS.iter().find(|(o, _)| *o == op).unwrap().1
}

// Surface spelling for infix/prefix printing; None = prints as a call.
pub fn op_infix(op: Op) -> Option<&'static str> {
    Some(match op {
        Op::Add => "+", Op::Sub => "-", Op::Mul => "*", Op::Div => "/",
        Op::Rem => "%", Op::Eq => "=", Op::Ne => "<>", Op::Lt => "<",
        Op::Le => "<=", Op::Gt => ">", Op::Ge => ">=", Op::And => "and",
        Op::Or => "or",
        _ => return None,
    })
}
