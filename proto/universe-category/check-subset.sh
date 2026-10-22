#!/bin/sh
# Check only the modules that can be affected by a change: each run checks
# ONE module (--only), the others are trusted, so a change to files F needs
# F and the modules that mention them, not all 320.
# Usage (from seg/):  proto/universe-category/check-subset.sh [DIR] PATTERN
#   DIR      model directory (default model)
#   PATTERN  grep -E pattern; every module of DIR whose text matches is checked
# Example: proto/universe-category/check-subset.sh model 'GElC|EGen|GUniv|smallC|GSmall|ElF\[|ElC\['
#   or:  check-subset.sh DIR --closure "M1 M2 ..."   the changed modules and
#        everything that mentions them, transitively (closure.py); with
#        DRY=1 only the list is printed (to ask before a large run)
SEG=${SEG:-$(cabal list-bin seg 2>/dev/null)}
JOBS=${JOBS:-3}
if [ $# -ge 2 ]; then DIRM=$1; shift; else DIRM=model; fi
if [ "$1" = --closure ]; then
  mods=$(python3 "$(dirname "$0")/closure.py" "$DIRM" $2)
else
  PAT=$1
  mods=$(grep -lE "$PAT" "$DIRM"/*.seg | sed "s|$DIRM/||;s|\.seg$||" | grep -v '^All$')
fi
if [ -n "$DRY" ]; then echo "$mods" | tr ' ' '\n' | grep -c . ; echo $mods; exit 0; fi
TMP=$(mktemp -d)
for m in $mods; do
  if [ "$m" = IvBase ]; then echo "$m --only-top IvBase --only-top Cn --only-top Fa --only-top FaU --only-top PrismCov"
  elif [ "$m" = Classical ]; then echo "$m --only-top Classical --only-top Cl"
  else echo "$m --only $m"; fi
done > "$TMP/jobs"
export SEG DIRM TMP
start=$(date +%s)
xargs -P "$JOBS" -L 1 sh -c '
  label=$0
  if out=$(timeout 40 "$SEG" "$DIRM/All.seg" "$@" 2>&1); then
    secs=$(echo "$out" | tail -2 | head -1 | sed "s/.*, \([0-9.]*\) s$/\1/")
    if awk "BEGIN { exit !($secs >= 10) }"; then echo "FAIL $label over cap $secs"; else echo "ok   $label $secs"; fi
  else echo "FAIL $label"; echo "$out" | grep -A4 "FAILED\|OVERRUN" | head -10; fi
' < "$TMP/jobs" | sort -k3 -rn > "$TMP/res"
cat "$TMP/res"
echo "$(grep -c '^ok' "$TMP/res") ok, $(grep -c '^FAIL' "$TMP/res") FAIL, $(wc -l < "$TMP/jobs" | tr -d ' ') modules, wall $(( $(date +%s) - start )) s"
grep -q '^FAIL' "$TMP/res"; r=$?; rm -rf "$TMP"; [ $r -ne 0 ]
