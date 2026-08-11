#!/usr/bin/env bash
# Time each benchmark through both interpreters. Usage: bench/run.sh
set -e
cd "$(dirname "$0")/.."
C=./c/snel
RUST=./target/release/snel
printf '%-10s %10s %10s\n' bench C rust
for f in bench/*.sn; do
  name=$(basename "$f" .sn)
  ct=$( { TIMEFORMAT='%3R'; time $C run "$f" >/dev/null 2>&1; } 2>&1 )
  rt=$( { TIMEFORMAT='%3R'; time $RUST run "$f" >/dev/null 2>&1; } 2>&1 )
  printf '%-10s %9ss %9ss\n' "$name" "$ct" "$rt"
done
