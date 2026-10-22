# Records migration, 18 October: diffs and test results

Kept here because nothing is committed and `defenv/` is untracked.

- `checker-records.diff`: `src/Seg.hs`, `src/SegParse.hs`, `app/Main.hs`, from the state before the record work (RECORDS.md §§1–4: records, `Mem`, `open` in records, the survey, fixed fields).
- `examples-records.diff`: the examples, the same period (new: `recordrules.seg`, `recordopen.seg`, `fixedfields.seg`).
- `core-records.diff`: `core/`, the migration of the 24 records (RECORDS.md §10), from the copy taken just before it.
- `core-vs-seg-core.diff`: `defenv/core` against the committed `seg/core`. This includes the earlier changes (CHANGES.md §9 and the η lemmas of `Presheaf` and `CPartial` from the previous session).
- `runfrom-all.txt`: `runfrom.sh Base`, all 202 steps, with times (after the migration, before §4).
- `runfrom-section4.txt`: the same after §4 (fixed fields): the current baseline.
- `examples-results.txt`: every example, after §4 (the current baseline) (`locks.seg`'s one failure is `byDeps`, by design).
- `records-survey.txt`: `segd All.seg --survey-records` before the migration.

To review the two larger proof changes: `COp.seg` (module `OpExtE`) and `CFibExt.seg` (`base`, `core`) in `core-records.diff`, with the three call sites in `COpCl.seg` and `CDSmallCl.seg`.
