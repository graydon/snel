// Values. Primitives: nil, bit, i64, f64, u8. The one aggregate is the vector
// (a homogeneous column); tables map byte-string keys to values. Strings are
// [u8]; `str`/`sym` are refinements over [u8], not distinct value kinds.
// Columns are flat buffers behind Rc, functional-but-in-place (reused when
// uniquely owned, copied when shared). Small byte buffers
// and small bit vectors are stored inline (SSO); this is an in-memory
// optimisation only — the on-disk format is already byte-packed.

use std::rc::Rc;

// ---------- Bytes: an immutable byte buffer with small-buffer optimisation ----------
// The one byte-vector representation: small buffers inline, large ones behind
// Rc — exactly like Bits does for bit vectors. Backs prim names, tab keys, and
// the payload of a [u8] column (a string).

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Bytes {
    S(u8, [u8; 22]),
    H(Rc<[u8]>),
}

// A byte-string used as an identifier: tab keys, prim names, AST names.
pub type Sym = Bytes;

impl Bytes {
    pub fn new(b: &[u8]) -> Bytes {
        if b.len() <= 22 {
            let mut buf = [0u8; 22];
            buf[..b.len()].copy_from_slice(b);
            Bytes::S(b.len() as u8, buf)
        } else {
            Bytes::H(b.into())
        }
    }
    pub fn str(s: &str) -> Bytes {
        Bytes::new(s.as_bytes())
    }
    pub fn bytes(&self) -> &[u8] {
        match self {
            Bytes::S(n, buf) => &buf[..*n as usize],
            Bytes::H(rc) => rc,
        }
    }
    pub fn len(&self) -> usize {
        self.bytes().len()
    }
    pub fn as_str(&self) -> Option<&str> {
        std::str::from_utf8(self.bytes()).ok()
    }
    // Valid identifier: non-empty, [a-zA-Z0-9_], not starting with a digit.
    pub fn is_ident(&self) -> bool {
        let b = self.bytes();
        !b.is_empty()
            && !b[0].is_ascii_digit()
            && b.iter().all(|c| c.is_ascii_alphanumeric() || *c == b'_')
    }
}

impl std::fmt::Debug for Bytes {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", String::from_utf8_lossy(self.bytes()))
    }
}

// ---------- bitmaps ----------

// Packed bit vector, LSB-first within each u64 word. Vectors of ≤64 bits keep
// their single word inline (SSO).
#[derive(Clone, PartialEq, Debug)]
pub struct Bits {
    pub len: usize,
    words: BitWords,
}

#[derive(Clone, PartialEq, Debug)]
enum BitWords {
    Inline(u64),
    Heap(Vec<u64>),
}

impl Default for Bits {
    fn default() -> Bits {
        Bits { len: 0, words: BitWords::Inline(0) }
    }
}

impl Bits {
    pub fn new(len: usize, fill: bool) -> Bits {
        let nwords = len.div_ceil(64).max(1);
        let words = if nwords <= 1 {
            BitWords::Inline(if fill { !0 } else { 0 })
        } else {
            BitWords::Heap(vec![if fill { !0u64 } else { 0 }; nwords])
        };
        let mut b = Bits { len, words };
        b.trim();
        b
    }
    fn nwords(&self) -> usize {
        self.len.div_ceil(64)
    }
    pub fn words(&self) -> &[u64] {
        match &self.words {
            BitWords::Inline(w) => std::slice::from_ref(w),
            BitWords::Heap(v) => v,
        }
    }
    fn word_mut(&mut self, i: usize) -> &mut u64 {
        // promote to heap if the index needs more than the inline word
        if i > 0 {
            if let BitWords::Inline(w) = self.words {
                let mut v = vec![0u64; i + 1];
                v[0] = w;
                self.words = BitWords::Heap(v);
            }
        }
        match &mut self.words {
            BitWords::Inline(w) => w,
            BitWords::Heap(v) => {
                if i >= v.len() {
                    v.resize(i + 1, 0);
                }
                &mut v[i]
            }
        }
    }
    pub fn get(&self, i: usize) -> bool {
        self.words()[i / 64] >> (i % 64) & 1 != 0
    }
    pub fn set(&mut self, i: usize, v: bool) {
        let (w, m) = (i / 64, 1u64 << (i % 64));
        let word = self.word_mut(w);
        if v {
            *word |= m;
        } else {
            *word &= !m;
        }
    }
    pub fn push(&mut self, v: bool) {
        let i = self.len;
        self.len += 1;
        self.set(i, v);
    }
    pub fn and_word(&mut self, i: usize, w: u64) {
        *self.word_mut(i) &= w;
    }
    pub fn or_word(&mut self, i: usize, w: u64) {
        *self.word_mut(i) |= w;
    }
    pub fn not_inplace(&mut self) {
        for i in 0..self.nwords() {
            let w = self.words()[i];
            *self.word_mut(i) = !w;
        }
        self.trim();
    }
    // Zero the tail bits past len; canonical form for Eq and serialization.
    pub fn trim(&mut self) {
        if self.len % 64 != 0 {
            let last = self.nwords().saturating_sub(1);
            let mask = (1u64 << (self.len % 64)) - 1;
            *self.word_mut(last) &= mask;
        }
        let nw = self.nwords().max(1);
        if let BitWords::Heap(v) = &mut self.words {
            v.truncate(nw);
        }
    }
}

impl FromIterator<bool> for Bits {
    fn from_iter<I: IntoIterator<Item = bool>>(it: I) -> Bits {
        let mut b = Bits::default();
        for v in it {
            b.push(v);
        }
        b
    }
}

// ---------- columns (vecs) ----------

// One case payload of a column: a flat homogeneous buffer. Names are plural to
// read as "a column of Xs". `U8s` is a [u8] (a string) — a byte buffer, SSO for
// small; `Vecs` is a column of sub-vectors ([[T]], including columns of
// strings); `Tabs` is a column of nested tables.
#[derive(Clone, PartialEq, Debug)]
pub enum Payload {
    Bits(Bits),
    I64s(Vec<i64>),
    F64s(Vec<f64>),
    U8s(Bytes),          // a [u8] column (a string); SSO
    Vecs(Vec<Rc<Col>>),  // a [[T]] column (including [[u8]], columns of strings)
    Tabs(Vec<Rc<Tab>>),  // a [tab] column
}

impl Payload {
    pub fn len(&self) -> usize {
        match self {
            Payload::Bits(b) => b.len,
            Payload::I64s(v) => v.len(),
            Payload::F64s(v) => v.len(),
            Payload::U8s(b) => b.len(),
            Payload::Vecs(v) => v.len(),
            Payload::Tabs(v) => v.len(),
        }
    }
    // Case-kind code shared with col_from_vals / empty_build.
    pub fn kind(&self) -> u8 {
        match self {
            Payload::Bits(_) => 1,
            Payload::I64s(_) => 2,
            Payload::F64s(_) => 3,
            Payload::U8s(_) => 4,
            Payload::Vecs(_) => 5,
            Payload::Tabs(_) => 6,
        }
    }
}

// A column. `present` (1 = non-nil) exists iff the type admits nil. Unions
// with >=2 non-nil cases carry `sel` (case index per element) and one payload
// per case; payloads are full-length and aligned.
#[derive(Clone, PartialEq, Debug)]
pub struct Col {
    pub len: usize,
    pub present: Option<Bits>,
    pub sel: Option<Vec<u8>>,
    pub cases: Vec<Payload>,
}

impl Col {
    pub fn simple(p: Payload) -> Col {
        Col { len: p.len(), present: None, sel: None, cases: vec![p] }
    }
    // A [u8] string column from raw bytes.
    pub fn u8s(b: &[u8]) -> Col {
        Col::simple(Payload::U8s(Bytes::new(b)))
    }
}

// ---------- tabs ----------

// Ordered key->value map (byte-string keys), unique, right-biased rebinding.
// Serves as record, dataframe, environment, module, and AST node.
#[derive(Clone, PartialEq, Debug, Default)]
pub struct Tab {
    pub keys: Vec<Sym>,
    pub vals: Vec<Val>,
    pub docs: Vec<Option<Bytes>>,
}

impl Tab {
    pub fn get(&self, k: &[u8]) -> Option<&Val> {
        self.keys.iter().rposition(|s| s.bytes() == k).map(|i| &self.vals[i])
    }
    pub fn bind(&mut self, k: Sym, v: Val, doc: Option<Bytes>) {
        if let Some(i) = self.keys.iter().position(|s| s == &k) {
            self.vals[i] = v;
            self.docs[i] = doc;
        } else {
            self.keys.push(k);
            self.vals.push(v);
            self.docs.push(doc);
        }
    }
    pub fn len(&self) -> usize {
        self.keys.len()
    }
}

// ---------- values ----------

#[derive(Clone, PartialEq, Debug, Default)]
pub enum Val {
    #[default]
    Nil,
    Bit(bool),
    I64(i64),
    F64(f64),
    U8(u8),
    Vec(Rc<Col>),
    Tab(Rc<Tab>),
    Fun(Rc<Clo>),
    Prim(Sym), // Sym here is just the byte-buffer key type, not a value kind
}

// A closure: typed params, body (code), captured env (free vars only).
#[derive(Clone, PartialEq, Debug)]
pub struct Clo {
    pub params: Vec<(Sym, crate::ast::Ty)>,
    pub ret: crate::ast::Ty,
    pub body: Rc<crate::ast::Node>,
    pub env: Rc<Tab>,
}
