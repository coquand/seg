#!/bin/sh
# Check the port module by module: each run checks ONE module (--only), the
# others are trusted (entered into the context, proofs not checked).  Every
# run is under the ten-second cap; together they check everything.
# IvBase is a segment whose generic files are imported INSIDE it: its own
# declarations are checked with --only-top (IvBase, Cn), each nested file
# with --only.
# The runs are independent, so they run JOBS at a time (default 6; JOBS=1
# gives the old sequential run).  The cap is the checker's own CPU time
# (the "x.xx s" it reports, and its internal per-declaration budget); the
# outer wall-clock guard is looser, since parallel runs share the machine.
SEG=$(cabal list-bin seg 2>/dev/null)
JOBS=${JOBS:-6}
WALL=$([ "$JOBS" = 1 ] && echo 10 || echo 40)
DIR=$(mktemp -d)
nested=$(grep -E '^\s*import ' model/IvBase.seg | sed 's/.*import \([A-Za-z0-9_]*\).*/\1/')
# one line per run: index, label, arguments
i=0
for m in $(grep -E '^\s*import ' model/All.seg | sed 's/.*import \([A-Za-z0-9_]*\).*/\1/'); do
  if [ "$m" = IvBase ]; then
    i=$((i+1)); echo "$i IvBase --only-top IvBase --only-top Cn --only-top Fa --only-top FaU --only-top PrismCov"
    for n in $nested; do i=$((i+1)); echo "$i $n --only $n"; done
  elif [ "$m" = Classical ]; then
    # the classical segment Cl (lem): its files are imported inside it
    i=$((i+1)); echo "$i Classical --only-top Classical --only-top Cl"
    for n in $(grep -E '^\s*import ' model/Classical.seg | sed 's/.*import \([A-Za-z0-9_]*\).*/\1/'); do
      i=$((i+1)); echo "$i $n --only $n"
    done
  else
    i=$((i+1)); echo "$i $m --only $m"
  fi
done > "$DIR/jobs"
export SEG WALL DIR
xargs -P "$JOBS" -L 1 sh -c '
  idx=$0; label=$1; shift
  out="$DIR/$idx.out"
  if timeout "$WALL" "$SEG" model/All.seg "$@" > "$out" 2>&1; then
    secs=$(tail -2 "$out" | head -1 | sed "s/.*, \([0-9.]*\) s$/\1/")
    if awk "BEGIN { exit !($secs >= 10) }"; then
      printf "FAIL  %-18s over the 10 s cap: %s s\n" "$label" "$secs" > "$DIR/$idx.res"
    else
      printf "ok    %-18s %s\n" "$label" "$(tail -2 "$out" | head -1 | sed "s/.*: //")" > "$DIR/$idx.res"
    fi
  else
    { printf "FAIL  %-18s\n" "$label"; grep -A4 "FAILED\|OVERRUN" "$out" | head -20; } > "$DIR/$idx.res"
  fi
' < "$DIR/jobs"
fail=0
for k in $(seq 1 "$i"); do
  cat "$DIR/$k.res" 2>/dev/null || { echo "FAIL  (run $k did not report)"; fail=1; }
  grep -q '^FAIL' "$DIR/$k.res" 2>/dev/null && fail=1
done
rm -rf "$DIR"; exit $fail
