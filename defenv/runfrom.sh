#!/bin/sh
# runfrom.sh [-n] START [COUNT]  -- check the file-modules of core/All.seg one
# at a time, in dependency order, starting at START, at most COUNT of them.
#
# Each check loads the whole program (All.seg: the nesting and the module
# parameters are kept) and checks only that file-module (--only M); the rest
# is trusted.  The order is All.seg's imports, with CBase replaced by its
# own top-level declarations (--only-top CBase, --only-top CB) and then its
# imports.  Stops at the first failure or at a file over 5 s.
#   -n   print the order only
DRY=0; [ "$1" = -n ] && { DRY=1; shift; }
START=${1:-Base}; COUNT=${2:-1000}
ROOT=$(cd "$(dirname "$0")" && pwd)
CORE="$ROOT/core"
SEGD=$(cd "$ROOT" && cabal list-bin exe:segd 2>/dev/null)

order() {
  sed -n 's/^ *import \([A-Za-z0-9]*\) *;.*/\1/p' "$CORE/All.seg" | while read -r m; do
    if [ "$m" = CBase ]; then
      echo "CBase --only-top"; echo "CB --only-top"
      sed -n 's/^ *import \([A-Za-z0-9]*\) *;.*/\1/p' "$CORE/CBase.seg"
    else
      echo "$m"
    fi
  done
  echo "ModelUA"
}

if [ $DRY = 1 ]; then order; exit 0; fi

started=0; n=0
order | while read -r m flag; do
  [ "$m" = "$START" ] && started=1
  [ $started = 1 ] || continue
  [ $n -lt "$COUNT" ] || exit 0
  n=$((n+1))
  opt=${flag:---only}
  t0=$(perl -MTime::HiRes=time -e 'printf "%.2f", time')
  out=$(cd "$CORE" && timeout 30 "$SEGD" All.seg $opt "$m" 2>&1); st=$?
  t1=$(perl -MTime::HiRes=time -e 'printf "%.2f", time')
  secs=$(echo "$t1 - $t0" | bc)
  summary=$(printf '%s\n' "$out" | tail -1)
  printf '%-16s %6s s  %s\n' "$m" "$secs" "$summary"
  if printf '%s\n' "$out" | grep -q 'FAILED\|ERROR\|OVERRUN' || [ $st -ne 0 ]; then
    printf '%s\n' "$out" | grep -v '^ *$' | head -30
    exit 1
  fi
  if [ "$(echo "$secs > 5" | bc)" = 1 ]; then echo "over 5 s: stop and analyse"; exit 1; fi
done
