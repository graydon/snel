#!/usr/bin/env bash
# Differential fuzz driver: generate random Snel programs and check the Rust
# and C interpreters agree on `run` (eval+text), `bin` (binary round-trip),
# `fmt` (canonical printing), and `sni` (interface generation).
#
#   tools/difftest.sh [N] [SEED]          N generated programs from SEED
#   tools/difftest.sh corpus DIR          every file in DIR, as fuzzer input bytes
#
# The `corpus` form replays a coverage-guided corpus (fuzz/corpus/roundtrip,
# grown by `cargo +nightly fuzz run roundtrip`) through both twins: libfuzzer
# finds inputs that reach new code, and this checks the two agree on them.
#
# Errors are canonicalized to "ERR" before comparison: the interpreters must
# agree on success-value exactly and on error-vs-success, not on message text.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
N="${1:-500}"
SEED="${2:-1}"
RUST="$ROOT/target/debug/snel"
C="$ROOT/c/snel"
FUZZ="$ROOT/target/debug/fuzz"

for bin in "$RUST" "$C" "$FUZZ"; do
  [ -x "$bin" ] || { echo "missing: $bin (build it first)"; exit 2; }
done

canon() { sed -E 's/^(parse|check|eval|bin) error.*/ERR/'; }

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cp "$ROOT/examples/std.sn" "$work/"   # so a generated `use std` resolves
fails=0

# inputs: either N seeds, or the files of a corpus directory
if [ "$N" = "corpus" ]; then
  dir="${2:-$ROOT/fuzz/corpus/roundtrip}"
  [ -d "$dir" ] || { echo "no such corpus: $dir"; exit 2; }
  mapfile -t inputs < <(find "$dir" -type f | sort)
  echo "corpus: ${#inputs[@]} inputs from $dir"
else
  inputs=()
  for ((i=0; i<N; i++)); do inputs+=("$((SEED + i))"); done
fi

for s in "${inputs[@]}"; do
  prog="$work/p.sn"
  if [ "$N" = "corpus" ]; then
    [ -f "$s" ] || continue   # a concurrent fuzz run may still be pruning
    "$FUZZ" bytes < "$s" > "$prog"
  else
    "$FUZZ" one "$s" > "$prog"
  fi
  for mode in run bin fmt sni; do
    a="$("$RUST" "$mode" "$prog" 2>&1 | canon)"
    b="$("$C"    "$mode" "$prog" 2>&1 | canon)"
    if [ "$a" != "$b" ]; then
      echo "MISMATCH seed=$s mode=$mode"
      echo "--- program ---"; cat "$prog"
      echo "--- rust ---"; echo "$a"
      echo "--- c ---"; echo "$b"
      echo
      fails=$((fails+1))
      [ "$fails" -ge 10 ] && { echo "stopping after 10 mismatches"; exit 1; }
    fi
  done
done
if [ "$fails" -eq 0 ]; then
  echo "OK: ${#inputs[@]} programs x4 modes, Rust == C"
else
  echo "FAILED: $fails mismatches"; exit 1
fi
