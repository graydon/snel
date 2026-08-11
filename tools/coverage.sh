#!/usr/bin/env bash
# How much of the Rust interpreter does a generated corpus actually reach?
#
#   tools/coverage.sh [N] [SEED] [FUZZBIN]
#
# Builds an instrumented `snel`, pushes N generated programs through every
# subcommand that reads a unit (run / bin / fmt / sni), and prints a per-module
# coverage summary. FUZZBIN lets you point at a different generator to compare
# corpora (that is how the old and new generators were measured against each
# other). The C twin is not measured here; the two implementations mirror each
# other module for module, so the Rust numbers stand in for both.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
N="${1:-300}"
SEED="${2:-1}"
FUZZ="${3:-$ROOT/target/release/fuzz}"

command -v cargo-llvm-cov >/dev/null || { echo "need: cargo install cargo-llvm-cov"; exit 2; }
[ -x "$FUZZ" ] || cargo build --release --bin fuzz 2>&1 | grep -E "^error" && true
[ -x "$FUZZ" ] || { echo "missing generator: $FUZZ"; exit 2; }

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cp "$FUZZ" "$work/gen"                # `clean` below wipes target/
cp "$ROOT/examples/std.sn" "$work/"   # so a generated `use std` resolves
FUZZ="$work/gen"

# Instrument, then drive the built binary directly — going through `cargo
# llvm-cov run` once per program would spend all its time in cargo.
# shellcheck disable=SC1090
source <(cargo llvm-cov show-env --export-prefix)
cargo llvm-cov clean --workspace
cargo build --bin snel 2>&1 | grep -E "^error" && exit 1

for ((i = 0; i < N; i++)); do
  "$FUZZ" one $((SEED + i)) > "$work/p.sn"
  for mode in run bin fmt sni; do
    "$ROOT/target/debug/snel" "$mode" "$work/p.sn" > /dev/null 2>&1
  done
  # ...and the same program through the language server, which is a whole
  # module (parse + check + diagnostics) the CLI modes never touch.
  "$FUZZ" lsp $((SEED + i)) | "$ROOT/target/debug/snel" lsp > /dev/null 2>&1
done

# The examples are part of the corpus too: they reach io, interop, and the
# module loader, which random units mostly do not.
for f in "$ROOT"/examples/*.sn; do
  timeout 20 "$ROOT/target/debug/snel" run "$f" > /dev/null 2>&1
done

echo "corpus: $N generated programs (seed $SEED) x4 subcommands, plus examples/"
cargo llvm-cov report --summary-only
