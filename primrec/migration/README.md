# Migration of core to recursion by eliminators (PRIMREC.md), 19 October 2026

- `core-primrec.diff`: `seg/defenv/core` against `seg/primrec/core`
  (32 files, +559 / -511 lines).
- `examples-primrec.diff`: the four example files that used recursion by name.
- `migrate-report.txt`: the automatic rewrite (`../migrate.py`), 160
  definitions.
- `runfrom-all.txt`: `runfrom.sh Base`, all 202 steps, OK.

How the migration was done:
1. `migrate.py` rewrote the direct calls into recursive results.
2. Forward references were moved with `../reorder.py`.
3. The helper cycles and `lift-refl` were changed by hand.

Full check, same session, same machine:

| | declarations | time | maximum resident | split fallback |
|---|---|---|---|---|
| defenv (counter added in a scratch copy) | 11812 | 54.4 s | 709 MB | 19953 |
| primrec | 11816 | 54.4 s | 789 MB | 19953 |

Per file (`runfrom.sh`): no file differs from the `defenv` baseline by more
than 0.3 s. The sum of the 202 steps is 230.5 s, against 228.2 s.
