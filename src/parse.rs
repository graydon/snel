// Recursive-descent parser. Newlines separate declarations; inside ( [ and
// tab-literal { they are whitespace. `mod` desugars here — it has no AST node.

use crate::ast::{op_by_name, Ast, Node, Span, Ty};
use crate::lex::{lex, Tok};
use crate::value::{Bytes, Sym, Val};

#[derive(Debug)]
pub struct PErr {
    pub msg: String,
    pub at: u32,
}

const KEYWORDS: &[&str] = &[
    "let", "fun", "type", "mod", "pub", "use", "try", "else",
    "err", "if", "then", "where", "nil", "is", "and", "or", "not", "inf", "nan",
    "true", "false", "do", "end", "bit", "i64", "f64", "u8",
];

pub struct Parser {
    toks: Vec<(Tok, u32)>,
    pos: usize,
    depth: u32, // bracket depth; >0 => newlines are whitespace
}

pub fn parse_unit(src: &str) -> Result<Vec<Node>, PErr> {
    let lexed = lex(src).map_err(|(msg, at)| PErr { msg, at })?;
    let mut p = Parser { toks: lexed.toks, pos: 0, depth: 0 };
    let ds = p.decls(&Tok::Eof)?;
    Ok(ds)
}

impl Parser {
    // The token stream always ends with `Eof`, so every read clamps to the last
    // token: a parser that runs off the end then sees `Eof` forever and reports
    // "expected ..." instead of indexing out of bounds. (Consuming loops only
    // advance on a match, so clamping cannot spin.)
    fn ix(&self, off: usize) -> usize {
        (self.pos + off).min(self.toks.len() - 1)
    }

    fn peek(&mut self) -> &Tok {
        // newlines are insignificant whitespace everywhere; `;` separates decls.
        // doc comments are only skipped inside brackets (top level, `decl` reads
        // them for attachment).
        loop {
            match &self.toks[self.ix(0)].0 {
                Tok::Newline => self.pos += 1,
                Tok::Doc(_) if self.depth > 0 => self.pos += 1,
                _ => break,
            }
        }
        &self.toks[self.ix(0)].0
    }
    fn at(&self) -> u32 {
        self.toks[self.ix(0)].1
    }
    fn next(&mut self) -> Tok {
        self.peek();
        let t = self.toks[self.ix(0)].0.clone();
        self.pos += 1;
        t
    }
    fn err<T>(&self, msg: impl Into<String>) -> Result<T, PErr> {
        Err(PErr { msg: msg.into(), at: self.at() })
    }
    fn eat(&mut self, p: &'static str) -> Result<(), PErr> {
        match self.next() {
            Tok::Punct(q) if q == p => Ok(()),
            t => self.err(format!("expected `{}`, found {:?}", p, t)),
        }
    }
    fn eat_kw(&mut self, kw: &str) -> Result<(), PErr> {
        match self.next() {
            Tok::Name(n) if n.bytes() == kw.as_bytes() => Ok(()),
            t => self.err(format!("expected `{}`, found {:?}", kw, t)),
        }
    }
    fn is_punct(&mut self, p: &str) -> bool {
        matches!(self.peek(), Tok::Punct(q) if *q == p)
    }
    fn is_kw(&mut self, kw: &str) -> bool {
        matches!(self.peek(), Tok::Name(n) if n.bytes() == kw.as_bytes())
    }
    fn take_punct(&mut self, p: &str) -> bool {
        let yes = self.is_punct(p);
        if yes {
            self.pos += 1;
        }
        yes
    }
    fn take_kw(&mut self, kw: &str) -> bool {
        let yes = self.is_kw(kw);
        if yes {
            self.pos += 1;
        }
        yes
    }
    fn name(&mut self) -> Result<Sym, PErr> {
        match self.next() {
            Tok::Name(n) => {
                if KEYWORDS.iter().any(|k| k.as_bytes() == n.bytes())
                    || op_by_name(n.bytes()).is_some()
                {
                    self.err(format!("`{:?}` is reserved", n))
                } else {
                    Ok(n)
                }
            }
            t => self.err(format!("expected name, found {:?}", t)),
        }
    }

    // Field names (record keys, tab-type fields, projections) live in the tab-key
    // namespace, not the term namespace, so they may be builtin names (`first`,
    // `sum`, `env`, …) — only keywords are excluded.
    fn field_name(&mut self) -> Result<Sym, PErr> {
        match self.next() {
            Tok::Name(n) if !KEYWORDS.iter().any(|k| k.as_bytes() == n.bytes()) => Ok(n),
            Tok::Name(n) => self.err(format!("`{:?}` is reserved", n)),
            t => self.err(format!("expected a field name, found {:?}", t)),
        }
    }
    fn node(&self, ast: Ast, lo: u32) -> Node {
        Node { ast, span: Span { lo, hi: self.at() } }
    }

    // ---------- declarations ----------

    // Parse declarations until `end`. `;` separates them (newlines are
    // whitespace); a trailing `;` before `end` is optional.
    fn decls(&mut self, end: &Tok) -> Result<Vec<Node>, PErr> {
        let mut ds = Vec::new();
        loop {
            self.skip_seps();
            if &self.toks[self.ix(0)].0 == end {
                self.pos += 1;
                return Ok(ds);
            }
            ds.push(self.decl()?);
            while matches!(self.toks[self.ix(0)].0, Tok::Newline) {
                self.pos += 1; // trailing whitespace before the separator
            }
            match &self.toks[self.ix(0)].0 {
                Tok::Punct(";") => {}
                t if t == end => {}
                t => return self.err(format!("expected `;` or end of block, found {:?}", t)),
            }
        }
    }

    // Skip declaration separators (newlines, `;`) and detached doc comments
    // (a doc line followed by a blank line, i.e. not immediately before a decl).
    fn skip_seps(&mut self) {
        loop {
            match &self.toks[self.ix(0)].0 {
                Tok::Newline | Tok::Punct(";") => self.pos += 1,
                Tok::Doc(_) if matches!(self.toks[self.ix(1)].0, Tok::Newline | Tok::Eof) => self.pos += 1,
                _ => break,
            }
        }
    }

    fn decl(&mut self) -> Result<Node, PErr> {
        let doc = match self.peek() {
            Tok::Doc(d) => {
                let d = d.clone();
                self.pos += 1;
                Some(d)
            }
            _ => None,
        };
        let public = self.take_kw("pub");
        let lo = self.at();
        if self.take_kw("let") {
            let x = self.name()?;
            let ty = if self.take_punct(":") { Some(self.ty()?) } else { None };
            self.eat("=")?;
            let e = self.expr()?;
            return Ok(self.node(Ast::Let { x, ty, e: Box::new(e), doc, public }, lo));
        }
        if self.is_kw("fun") {
            // `fun name(...)` is declaration sugar; bare `fun(...)` is an expression.
            if let Tok::Name(_) = self.toks[self.ix(1)].0 {
                self.pos += 1;
                let x = self.name()?;
                let f = self.fun_expr(lo)?;
                return Ok(self.node(Ast::Let { x, ty: None, e: Box::new(f), doc, public }, lo));
            }
        }
        if self.take_kw("type") {
            let x = self.name()?;
            self.eat("=")?;
            let base = self.ty()?;
            // `where pred` is optional; a bare alias has the always-true predicate.
            let pred = if self.take_kw("where") {
                self.expr()?
            } else {
                self.always_true(lo, &base)
            };
            return Ok(self.node(Ast::Type { x, base, pred: Box::new(pred), doc, public }, lo));
        }
        if self.take_kw("mod") {
            return self.mod_decl(lo, doc, public);
        }
        if public {
            return self.err("`pub` must precede let/fun/type/mod");
        }
        if self.take_kw("use") {
            let x = self.name()?;
            // `use x = "url"` names a remote unit
            let url = if self.take_punct("=") {
                match self.next() {
                    Tok::Str(s) => Some(s),
                    t => return self.err(format!("expected a url string, found {:?}", t)),
                }
            } else {
                None
            };
            return Ok(self.node(Ast::Use { x, url, doc }, lo));
        }
        if doc.is_some() {
            return self.err("doc comment must precede a declaration");
        }
        self.expr()
    }

    // mod m { pub d1 ... }        => let m = (d1; ...; {pubs})
    // mod m(p: T) { pub d1 ... }  => let m = fun(p: T) -> {pubs} = (d1; ...; {pubs})
    fn mod_decl(&mut self, lo: u32, doc: Option<Bytes>, public: bool) -> Result<Node, PErr> {
        let x = self.name()?;
        let params = if self.is_punct("(") { Some(self.params()?) } else { None };
        self.eat("{")?;
        let saved = self.depth;
        self.depth = 0; // mod body: newline-separated declarations
        let ds = self.decls(&Tok::Punct("}"))?;
        self.depth = saved;
        // pub names and their declared types (for the parametric result type)
        let mut pubs: Vec<(Sym, Option<Ty>)> = Vec::new();
        for d in &ds {
            match &d.ast {
                Ast::Let { x, ty, e, public: true, .. } => {
                    let t = ty.clone().or_else(|| fun_sig(e));
                    pubs.push((x.clone(), t));
                }
                Ast::Type { x, public: true, .. } => pubs.push((x.clone(), Some(Ty::Tab(Vec::new())))),
                Ast::Type { .. } | Ast::Let { .. } | Ast::Use { .. } => {}
                _ => return self.err("mod body must contain only declarations"),
            }
        }
        let tab = Ast::TabL(
            pubs.iter()
                .map(|(k, _)| (k.clone(), self.node(Ast::Var(k.clone()), lo)))
                .collect(),
        );
        let mut body = ds;
        body.push(self.node(tab, lo));
        let seq = self.node(Ast::Seq(body), lo);
        let e = match params {
            None => seq,
            Some(ps) => {
                let ret = Ty::Tab(
                    pubs.into_iter()
                        .map(|(k, t)| {
                            t.map(|t| (k.clone(), t)).ok_or(PErr {
                                msg: format!("pub `{:?}` in parametric mod needs a type annotation", k),
                                at: lo,
                            })
                        })
                        .collect::<Result<_, _>>()?,
                );
                self.node(Ast::Fun { params: ps, ret, body: seq.into() }, lo)
            }
        };
        Ok(self.node(Ast::Let { x, ty: None, e: Box::new(e), doc, public }, lo))
    }

    // fun(_: base) -> bit = 1b  — the transparent-alias predicate.
    fn always_true(&self, lo: u32, base: &Ty) -> Node {
        let body = self.node(Ast::Lit(Val::Bit(true)), lo);
        self.node(
            Ast::Fun {
                params: vec![(Bytes::str("_"), base.clone())],
                ret: Ty::Bit,
                body: body.into(),
            },
            lo,
        )
    }

    fn params(&mut self) -> Result<Vec<(Sym, Ty)>, PErr> {
        self.eat("(")?;
        self.depth += 1;
        let mut ps = Vec::new();
        if !self.is_punct(")") {
            loop {
                let x = self.name()?;
                self.eat(":")?;
                ps.push((x, self.ty()?));
                if !self.take_punct(",") {
                    break;
                }
            }
        }
        self.eat(")")?;
        self.depth -= 1;
        Ok(ps)
    }

    // ---------- types ----------

    fn ty(&mut self) -> Result<Ty, PErr> {
        let mut parts = vec![self.ty_post()?];
        while self.take_punct("|") {
            parts.push(self.ty_post()?);
        }
        Ok(if parts.len() == 1 { parts.pop().unwrap() } else { union_of(parts) })
    }

    fn ty_post(&mut self) -> Result<Ty, PErr> {
        let t = self.ty_atom()?;
        if self.take_punct("?") {
            Ok(union_of(vec![t, Ty::Nil]))
        } else {
            Ok(t)
        }
    }

    fn ty_atom(&mut self) -> Result<Ty, PErr> {
        if self.take_punct("[") {
            self.depth += 1;
            let t = self.ty()?;
            self.depth -= 1;
            self.eat("]")?;
            return Ok(Ty::Vec(Box::new(t)));
        }
        if self.take_punct("{") {
            self.depth += 1;
            let mut fs = Vec::new();
            if !self.is_punct("}") {
                loop {
                    let k = self.field_name()?;
                    self.eat(":")?;
                    fs.push((k, self.ty()?));
                    if !self.take_punct(",") {
                        break;
                    }
                }
            }
            self.depth -= 1;
            self.eat("}")?;
            return Ok(Ty::Tab(fs));
        }
        if self.take_kw("fun") {
            self.eat("(")?;
            self.depth += 1;
            let mut args = Vec::new();
            if !self.is_punct(")") {
                loop {
                    args.push(self.ty()?);
                    if !self.take_punct(",") {
                        break;
                    }
                }
            }
            self.eat(")")?;
            self.depth -= 1;
            self.eat("->")?;
            return Ok(Ty::Fun(args, Box::new(self.ty()?)));
        }
        match self.next() {
            Tok::Name(n) => Ok(match n.bytes() {
                b"nil" => Ty::Nil,
                b"bit" => Ty::Bit,
                b"i64" => Ty::I64,
                b"f64" => Ty::F64,
                b"u8" => Ty::U8,
                _ => {
                    if KEYWORDS.iter().any(|k| k.as_bytes() == n.bytes()) {
                        return self.err(format!("`{:?}` is not a type", n));
                    }
                    Ty::Name(n)
                }
            }),
            t => self.err(format!("expected type, found {:?}", t)),
        }
    }

    // ---------- expressions ----------

    pub fn expr(&mut self) -> Result<Node, PErr> {
        let lo = self.at();
        let e = self.pipe_expr()?;
        if self.take_kw("is") {
            let t = self.ty()?;
            return Ok(self.node(Ast::Is(Box::new(e), t), lo));
        }
        Ok(e)
    }

    // Tacit pipe: `x |> f(a)` is `f(a, x)` — the left value is appended as the
    // last argument, or substituted for each `_` placeholder if any are present.
    // `x |> f` (a bare callee) is `f(x)`. Lowest precedence, left-associative.
    fn pipe_expr(&mut self) -> Result<Node, PErr> {
        let lo = self.at();
        let mut e = self.or_expr()?;
        while self.take_punct("|>") {
            let rhs = self.or_expr()?;
            e = self.desugar_pipe(e, rhs, lo);
        }
        Ok(e)
    }

    fn desugar_pipe(&self, lhs: Node, rhs: Node, lo: u32) -> Node {
        match rhs.ast {
            Ast::App(f, mut args) => {
                let holes: Vec<usize> = args
                    .iter()
                    .enumerate()
                    .filter(|(_, a)| matches!(&a.ast, Ast::Var(n) if n.bytes() == b"_"))
                    .map(|(i, _)| i)
                    .collect();
                if holes.is_empty() {
                    args.push(lhs);
                } else {
                    for i in holes {
                        args[i] = lhs.clone();
                    }
                }
                self.node(Ast::App(f, args), lo)
            }
            _ => self.node(Ast::App(Box::new(rhs), vec![lhs]), lo),
        }
    }

    fn binop_level(
        &mut self,
        ops: &[(&'static str, &'static str)],
        next: fn(&mut Self) -> Result<Node, PErr>,
    ) -> Result<Node, PErr> {
        let lo = self.at();
        let mut e = next(self)?;
        loop {
            let mut matched = false;
            for (surface, name) in ops {
                let hit = if surface.chars().next().unwrap().is_ascii_alphabetic() {
                    self.take_kw(surface)
                } else {
                    self.take_punct(surface)
                };
                if hit {
                    let rhs = next(self)?;
                    e = self.node(
                        Ast::App(
                            Box::new(self.node(Ast::Var(Bytes::str(name)), lo)),
                            vec![e, rhs],
                        ),
                        lo,
                    );
                    matched = true;
                    break;
                }
            }
            if !matched {
                return Ok(e);
            }
        }
    }

    fn or_expr(&mut self) -> Result<Node, PErr> {
        self.binop_level(&[("or", "or")], |s| {
            s.binop_level(&[("and", "and")], |s| {
                s.binop_level(
                    &[("=", "eq"), ("<>", "ne"), ("<=", "le"), (">=", "ge"), ("<", "lt"), (">", "gt")],
                    |s| {
                        s.binop_level(&[("+", "add"), ("-", "sub")], |s| {
                            s.binop_level(&[("*", "mul"), ("/", "div"), ("%", "rem")], Self::unary)
                        })
                    },
                )
            })
        })
    }

    fn unary(&mut self) -> Result<Node, PErr> {
        let lo = self.at();
        if self.take_punct("-") {
            // Fold `-<int literal>` before it reaches the atom's range check, so
            // -9223372036854775808 (i64::MIN) round-trips.
            if let Tok::Int(m) = self.peek().clone() {
                self.pos += 1;
                let v = i64::try_from(-m).map_err(|_| PErr { msg: "int out of range".into(), at: lo })?;
                return Ok(self.node(Ast::Lit(Val::I64(v)), lo));
            }
            let e = self.unary()?;
            if let Ast::Lit(Val::F64(f)) = e.ast {
                return Ok(self.node(Ast::Lit(Val::F64(crate::print::canon_f64(-f))), lo));
            }
            return Ok(self.node(
                Ast::App(Box::new(self.node(Ast::Var(Bytes::str("neg")), lo)), vec![e]),
                lo,
            ));
        }
        if self.take_kw("not") {
            let e = self.unary()?;
            return Ok(self.node(
                Ast::App(Box::new(self.node(Ast::Var(Bytes::str("not")), lo)), vec![e]),
                lo,
            ));
        }
        self.postfix()
    }

    fn postfix(&mut self) -> Result<Node, PErr> {
        let lo = self.at();
        let mut e = self.atom()?;
        loop {
            if self.take_punct(".") {
                let x = self.field_name()?;
                e = self.node(Ast::Proj(Box::new(e), x), lo);
            } else if self.is_punct("[") {
                self.pos += 1;
                self.depth += 1;
                let i = self.expr()?;
                self.depth -= 1;
                self.eat("]")?;
                e = self.node(Ast::Idx(Box::new(e), Box::new(i)), lo);
            } else if self.is_punct("(") {
                self.pos += 1;
                self.depth += 1;
                let mut args = Vec::new();
                if !self.is_punct(")") {
                    loop {
                        args.push(self.expr()?);
                        if !self.take_punct(",") {
                            break;
                        }
                    }
                }
                self.depth -= 1;
                self.eat(")")?;
                e = self.node(Ast::App(Box::new(e), args), lo);
            } else {
                return Ok(e);
            }
        }
    }

    fn fun_expr(&mut self, lo: u32) -> Result<Node, PErr> {
        let params = self.params()?;
        self.eat("->")?;
        let ret = self.ty()?;
        self.eat("=")?;
        let body = self.expr()?;
        Ok(self.node(Ast::Fun { params, ret, body: body.into() }, lo))
    }

    fn atom(&mut self) -> Result<Node, PErr> {
        let lo = self.at();
        match self.peek().clone() {
            Tok::Int(i) => {
                self.pos += 1;
                let v = i64::try_from(i).map_err(|_| PErr { msg: "int out of range".into(), at: lo })?;
                Ok(self.node(Ast::Lit(Val::I64(v)), lo))
            }
            Tok::Float(f) => {
                self.pos += 1;
                Ok(self.node(Ast::Lit(Val::F64(f)), lo))
            }
            Tok::U8Lit(v) => {
                self.pos += 1;
                Ok(self.node(Ast::Lit(Val::U8(v)), lo))
            }
            Tok::BitVec(digits) => {
                self.pos += 1;
                // :1011 is a [bit] column, index 0 first
                let bits: crate::value::Bits = digits.bytes().iter().map(|d| *d == b'1').collect();
                let col = crate::value::Col::simple(crate::value::Payload::Bits(bits));
                Ok(self.node(Ast::Lit(Val::Vec(std::rc::Rc::new(col))), lo))
            }
            Tok::Str(s) => {
                self.pos += 1;
                // a string literal is a [u8] value
                let col = crate::value::Col::u8s(s.bytes());
                Ok(self.node(Ast::Lit(Val::Vec(std::rc::Rc::new(col))), lo))
            }
            Tok::Punct(":") => {
                // :name is sugar for the string "name" (a symbol, i.e. a [u8])
                self.pos += 1;
                let name = self.field_name()?; // allows builtin/keyword-ish names as symbols
                let col = crate::value::Col::u8s(name.bytes());
                Ok(self.node(Ast::Lit(Val::Vec(std::rc::Rc::new(col))), lo))
            }
            Tok::Punct("(") => {
                self.pos += 1;
                self.depth += 1;
                // ascription form: ( e : T )
                let first = self.decl()?;
                if !is_decl(&first) && self.take_punct(":") {
                    let t = self.ty()?;
                    self.depth -= 1;
                    self.eat(")")?;
                    return Ok(self.node(Ast::As(Box::new(first), t), lo));
                }
                let mut ds = vec![first];
                loop {
                    if self.take_punct(")") {
                        break;
                    }
                    self.eat(";")?; // `;` separates block items
                    self.skip_seps();
                    if self.take_punct(")") {
                        break; // trailing `;`
                    }
                    ds.push(self.decl()?);
                }
                self.depth -= 1;
                if ds.len() == 1 && !is_decl(&ds[0]) {
                    return Ok(ds.into_iter().next().unwrap());
                }
                Ok(self.node(Ast::Seq(ds), lo))
            }
            Tok::Punct("[") => {
                self.pos += 1;
                self.depth += 1;
                let mut es = Vec::new();
                if !self.is_punct("]") {
                    loop {
                        es.push(self.expr()?);
                        if !self.take_punct(",") {
                            break;
                        }
                    }
                }
                self.depth -= 1;
                self.eat("]")?;
                Ok(self.node(Ast::VecL(es), lo))
            }
            Tok::Punct("{") => {
                self.pos += 1;
                self.depth += 1;
                let mut fs = Vec::new();
                if !self.is_punct("}") {
                    loop {
                        let k = self.field_name()?;
                        self.eat("=")?;
                        fs.push((k, self.expr()?));
                        if !self.take_punct(",") {
                            break;
                        }
                    }
                }
                self.depth -= 1;
                self.eat("}")?;
                Ok(self.node(Ast::TabL(fs), lo))
            }
            Tok::Name(n) => {
                self.pos += 1;
                match n.bytes() {
                    b"nil" => Ok(self.node(Ast::Lit(Val::Nil), lo)),
                    b"inf" => Ok(self.node(Ast::Lit(Val::F64(f64::INFINITY)), lo)),
                    b"nan" => Ok(self.node(Ast::Lit(Val::F64(f64::NAN)), lo)),
                    // sugar for the bit literals 1b / 0b
                    b"true" => Ok(self.node(Ast::Lit(Val::Bit(true)), lo)),
                    b"false" => Ok(self.node(Ast::Lit(Val::Bit(false)), lo)),
                    b"do" => {
                        // `do … end` is a block, a synonym for `( … )`
                        self.depth += 1;
                        let first = self.decl()?;
                        let mut ds = vec![first];
                        loop {
                            if self.take_kw("end") {
                                break;
                            }
                            self.eat(";")?;
                            self.skip_seps();
                            if self.take_kw("end") {
                                break; // trailing `;`
                            }
                            ds.push(self.decl()?);
                        }
                        self.depth -= 1;
                        if ds.len() == 1 && !is_decl(&ds[0]) {
                            Ok(ds.into_iter().next().unwrap())
                        } else {
                            Ok(self.node(Ast::Seq(ds), lo))
                        }
                    }
                    b"fun" => self.fun_expr(lo),
                    b"if" => {
                        let c = self.expr()?;
                        self.eat_kw("then")?;
                        let t = self.expr()?;
                        self.eat_kw("else")?;
                        let e = self.expr()?;
                        Ok(self.node(Ast::If(Box::new(c), Box::new(t), Box::new(e)), lo))
                    }
                    b"try" => {
                        let e = self.expr()?;
                        self.eat_kw("else")?;
                        let f = self.expr()?;
                        Ok(self.node(Ast::Try(Box::new(e), Box::new(f)), lo))
                    }
                    b"err" => {
                        let e = self.expr()?;
                        Ok(self.node(Ast::Err(Box::new(e)), lo))
                    }
                    _ => {
                        if op_by_name(n.bytes()).is_some() {
                            // builtin name: only callable / passable as value
                            Ok(self.node(Ast::Var(n), lo))
                        } else if KEYWORDS.iter().any(|k| k.as_bytes() == n.bytes()) {
                            self.err(format!("unexpected keyword `{:?}`", n))
                        } else {
                            Ok(self.node(Ast::Var(n), lo))
                        }
                    }
                }
            }
            t => self.err(format!("unexpected {:?}", t)),
        }
    }
}

fn is_decl(n: &Node) -> bool {
    matches!(n.ast, Ast::Let { .. } | Ast::Type { .. } | Ast::Use { .. })
}

// The syntactic fun type of a fun literal, if e is one (for mod pub sigs).
fn fun_sig(e: &Node) -> Option<Ty> {
    match &e.ast {
        Ast::Fun { params, ret, .. } => Some(Ty::Fun(
            params.iter().map(|(_, t)| t.clone()).collect(),
            Box::new(ret.clone()),
        )),
        _ => None,
    }
}

pub fn union_of(parts: Vec<Ty>) -> Ty {
    let mut flat: Vec<Ty> = Vec::new();
    for p in parts {
        match p {
            Ty::Union(ts) => flat.extend(ts),
            t => flat.push(t),
        }
    }
    flat.dedup_by(|a, b| a == b); // adjacent only; full dedup below
    let mut out: Vec<Ty> = Vec::new();
    for t in flat {
        if !out.contains(&t) {
            out.push(t);
        }
    }
    if out.len() == 1 {
        out.pop().unwrap()
    } else {
        Ty::Union(out)
    }
}

// The module doc comment: a `--` block at the very top of a unit, separated
// from the first declaration by a blank line. (A leading block with *no* blank
// line after it is the first declaration's own doc, as usual.)
pub fn module_doc(src: &str) -> Option<Bytes> {
    let lexed = lex(src).ok()?;
    match (&lexed.toks.first()?.0, &lexed.toks.get(1)?.0) {
        (Tok::Doc(d), Tok::Newline) => Some(d.clone()),
        _ => None,
    }
}
