#!/bin/sh
# tests.sh -- the prototype's regressions: every example (the summary line
# and the fallback count), and the read-back tests of PRIMREC.md 5.4.
# Compare with tests.expected:  ./tests.sh | diff tests.expected -
ROOT=$(cd "$(dirname "$0")" && pwd)
SEGD=$(cd "$ROOT" && cabal list-bin exe:segd 2>/dev/null)
for f in "$ROOT"/examples/*.seg "$ROOT"/examples-defenv/*.seg; do
  out=$(cd "$(dirname "$f")" && timeout 30 "$SEGD" "$(basename "$f")" 2>&1)
  printf '%s\n' "$out" | grep -E 'declarations,|^split conversion fallback|^SCOPE ERROR|^OK$|^FAILED|^INTERNAL' | sed 's/, [0-9.]* s$//'
done
for d in ack skipN; do
  echo "quote-test $d:"
  (cd "$ROOT/examples" && timeout 30 "$SEGD" primrec.seg --quote-test $d 2>&1)
done
