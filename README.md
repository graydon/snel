# Snel

## LLM notice

The code in this repo was made with an LLM, subject to my guidance. If this
offends your sensibilities, close the tab and move along. Sorry.

It was made fairly quickly (3ish evenings?) and so it probably still has lots
of bugs. There are 2 implementations and a differential fuzzer and so far it
seems to mostly do what I want, but you know, big warning here. LLM zone.

This README is human-written.

## What is it

Snel is a small, experimental language that exists to explore several questions
I've been curious about for a while.

## Quick look

```
let v = [3, 1, 7, 5];            -- an [i64] column
let mask = v > 2;                -- vector-compare makes bitmap :1011
let big = v[v > 2];              -- mask-index selects elements [3, 7, 5]
let t = { name = ["alice", "bob"],
          age = [40, 20] };      -- tables name and structure columns
let over30 = t[t.age > 30];      -- table-index selects all columns { name = ["alice"], age = [40] }
mod stats(eps: f64) {            -- parametric module = fun returning a tab
  pub fun near(x: f64, y: f64) -> bit = abs(x - y) < eps
};
```

See [examples/tour.sn](examples/tour.sn) for a feature-tour, or any of
the other examples in [examples](examples/) for some specific aspects.

## Design considerations

As I said above, this is an experiment to explore questions I've wondered
about and wanted a playground to try out in: 

  1. Vectorization and vectorized interpreters. Specifically: there are no
     user-controlled loops in Snel, and conditional code is strongly encouraged
     to use masks/selects rather than branches. Branches are hard to eliminate
     entirely (you can fake them with selects-of-vectors-of-closures) and
     occasionally convenient, so I left one scalar `if/then/else` convenience
     form in, but they will always be slower than masks/selects; that's the
     whole thing with vectorization!
  
     I [gave a talk](https://venge.net/graydon/talks/VectorizedInterpretersTalk-2023-05-12.pdf)
     about this a while ago and part of that was speculation: that vectorized
     style might work well -- be ergonomic and also fast -- for more domains
     than it already works in. APL is unpopular but APL is weird in lots of
     ways. I'm curious to see how well vectorization works in not-APL.

  2. Termination. There are not just no loops but also no recursion (there's a
     static typechecker that among other things prohibits typing self-application).
     There's an escape hatch (you can spawn a subprocess and pass it a closure) but
     by default every program just runs top to bottom once and stops. I'm curious
     if this causes any problems in practice, or is fine for most programs.

  3. Purity and error recovery. It's an eager language, but doesn't admit much
     state. All data structures are immutable and all bindings too (the runtime
     reuses uniquely-owned buffers in place — functional-but-in-place). Again
     there's an escape hatch (an effectful io module) but if you don't touch it
     there are no side effects. Consequently errors just throw away the current
     computation entirely, and there's a `try/else` to encapsulate those.

  4. Minimalism. The implementation is 8kloc of Rust including LSP server, code
     formatter/printer, and all builtins; and there's a twin implementation in
     11kloc of C. Size constraints tend to force interesting choices and I
     wanted to see what I'd keep vs. throw out given size pressure.

  5. Builtin datatype and homoiconicity. Its central datatype -- tables of
     symbol-indexed homogeneous columns -- is akin to a dataframe in other
     languages, and is reused for all structures (environments, programs,
     modules, user data). It can roundtrip in text and binary forms, so saving
     (or transmitting, or inspecting) anything is always at your fingertips.

  6. Refinement typing (with a simple gradual implementation). Everything is
     typed but the types go a little beyond easy decidability: there are
     user-predicate refinement types and union-vector narrowings that really
     just depend on runtime data. So it statically checks all the decidable
     stuff and inserts gradual-style coercion points (dynamic checks) on all the
     undeicable parts. I am curious if this is pleasant or unpleasant as a
     typing regime, if it catches enough errors, etc.

  7. LLM-friendliness. Any file module (.sn) can be summarized to a
     signatures-only file (.sni) that eats less LLM context than the full body
     file: the revenge of header files! Furthermore several of the factors above
     -- minimalism, purity, termination, refinement typing -- are partly bets
     I'm making that they might play well with the peculiar strengths and
     weaknesses of LLMs. My bet is that we need _more_ error-defense mechanisms
     in our languages now rather than fewer, and that new languages should be
     _more_ constrained environments for coding. More restricted-to-local
     reasoning, fewer dumb bugs.

## Spec

See [SPEC.md](SPEC.md) for the language definition.

## License

I haven't any idea if LLM stuff is even subject to copyright. And if it was,
what would it matter at this point? Anyone could re-synthesize this thing in a
few evenings for a few dollars, just as I did from first principles. Maybe for
the sake of politeness I'll say it's MIT licensed? Obviously you should just do
whatever you like with it. If anything. I expect nobody will care but it's a
nice old habit to post things if you think they're potentially interesting.

## Name

My "vectorized interpreters" talk made the analogy between vectorized
interpreters and "mass rapid transit", which is a fancy term for "trains"
(especially used in urban settings). A Dutch inter-city express train used to be
called a <a href="https://nl.wikipedia.org/wiki/Sneltrein">Sneltrein</a> (though
they seem to have retired this name, sadly; it is a great name).
