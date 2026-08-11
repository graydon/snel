// Coverage-guided fuzz target: libfuzzer mutates raw bytes, the generator in
// src/bin/fuzz.rs turns those bytes into a Snel program (one byte per grammar
// choice, so a byte-level mutation moves exactly one choice), and this target
// asserts the invariants the language promises about any program it accepts.
//
//   cargo +nightly fuzz run roundtrip
//   cargo +nightly fuzz run roundtrip -- -max_total_time=300
//
// A crash here is a Rust-side bug: a panic, or a broken round trip. Whether the
// C twin *agrees* is a separate question — replay this target's corpus through
// both with `tools/difftest.sh corpus fuzz/corpus/roundtrip`.

#![no_main]

use libfuzzer_sys::fuzz_target;

// The generator lives with the corpus generator rather than in the library, so
// the interpreter crate keeps no fuzzing code. Its `main` is unused here.
#[allow(dead_code)]
#[path = "../../src/bin/fuzz.rs"]
mod gen;

use snel::eval::NoLoader;

fuzz_target!(|data: &[u8]| {
    if data.len() > 4096 {
        return; // keep inputs (and so programs) small enough to stay fast
    }
    let src = gen::program_from_bytes(data);

    // 1. Parsing must not panic, and must be a total function of the text.
    let Ok(ds) = snel::parse::parse_unit(&src) else { return };

    // 2. Printing an AST and reparsing it must give the same AST, and printing
    //    must be idempotent (SPEC §10.1: text round-trips losslessly).
    let printed = snel::print::fmt_program(&ds);
    let ds2 = snel::parse::parse_unit(&printed)
        .unwrap_or_else(|e| panic!("reparse of printed source failed: {}\n--- src ---\n{}\n--- printed ---\n{}", e.msg, src, printed));
    let printed2 = snel::print::fmt_program(&ds2);
    assert_eq!(printed, printed2, "printing is not idempotent\n--- src ---\n{}", src);

    // 3. AST -> binary -> AST must round-trip, and reprint identically: this is
    //    the same path `snel bin` takes, expressed as an invariant.
    let as_val = |ds: &[snel::ast::Node]| {
        let vals: Vec<snel::value::Val> = ds.iter().map(snel::wire::ast_to_val).collect();
        snel::value::Val::Vec(std::rc::Rc::new(
            snel::ops::col_from_vals(vals).expect("AST values form a column"),
        ))
    };
    let v = as_val(&ds);
    let back = snel::bin_roundtrip(&v).expect("binary round-trip decodes");
    assert_eq!(
        snel::print::fmt_val(&back),
        snel::print::fmt_val(&v),
        "binary round-trip changed the AST\n--- src ---\n{}",
        src
    );

    // 4. Evaluation must not panic. Errors are fine — the language is total, so
    //    it must either produce a value or report an error, never abort.
    let mut loader = NoLoader;
    if let Ok(v) = snel::eval_unit(&mut loader, &src) {
        // 5. A value's canonical text must reparse, and its binary form must
        //    round-trip to an equal value (SPEC §4.9, §10.1).
        let text = snel::print::fmt_val(&v);
        let dec = snel::bin_roundtrip(&v).expect("value binary round-trip decodes");
        assert_eq!(text, snel::print::fmt_val(&dec), "binary round-trip changed the value");
    }
});
