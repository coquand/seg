# Handoff: Id vs Path in seg/core (goal for the next seg-62 session)

Thierry (2026-10-17): "maybe it could be interesting to have Id vs Path in Delta using classical
logic or in Poset using Swan's technique?" Accepted as the goal of the next fresh session.

## State at hand-off
- seg/core is COMPLETE against seg/notes/model.tex (the specification, 14 pages); only the Yoneda
  remark of §6.2 is not formalised (marked "not needed"). 178 modules, `./segc core all` 38 s cold,
  every file < 4 s. Status: seg/core/DESIGN.md ("final"); comparison: seg/core/COMPARISON.md.
- Both instances give Theorem 7, ua : ContrOp, fibU : Fib(U) (posets constructive; Delta with lem only
  in CDeltaHornBox.decDeg).
- Checking: ONLY through the server `./segc core changed|all|check M|deps M|stop` (seg/segc).
- Hidden arguments: deterministic rule (memory seg-hidden-args); give {e} when not inferred.
- canonicity-96 (sock /tmp/cc-socks/3686.sock) is paused, owns seg/core files; seg-62 edits
  model.tex only. Never commit; no src/ change without Thierry.

## The goal
An identity type Id with strict J-computation, compared with Path, in the model:
1. Swan's construction (generic, both instances): Id_A(a,b) = { (p : Path_A(a,b), phi : Phi) |
   p is constant (degenerate) on phi }; refl = (const, top); J by composition, strict on refl since
   the cofibration top makes the filler's value the given one. Needs: the one-sieve Phi with
   unions/forall (CBase), Path fibrancy (CPathFib/CPathComp), transport (CTr*), filling (CFill).
   Check what Swan needs of cofibrations (closure under Sigma-types / "dominance"; that phi |-> the
   sieve where p is constant is a cofibration) and whether our Phi (decidable sieves) has it for
   posets and Delta.
2. Delta classically: does Path itself admit a strict J (regularity), using normalised fillers
   (degenerate problems get degenerate fillers, CDNorm*)? Decide mathematically first — regularity
   fails at higher types in general (memory regularity-fails-at-higher-types); do not assume it.
3. Id ≃ Path (equivalence), fibrancy of Id, naturality (move form, as for the type formers).

## Method (same as the rebuild)
1. Write the mathematics first as a new section of seg/notes/model.tex (Thierry's paper style),
   with precise statements and proofs; settle what the cofibrations must satisfy.
2. Then formalise in seg/core (via canonicity-96 or directly), every file < 5 s, lock after
   characterising lemmas, gate = `./segc core changed`.

## References
- Swan, "Identity types in algebraic model structures and cubical sets"; CCHM §9.1 (Id via Swan).
- Memories: swan-id-strictness, sid-is-needed, regularity-fails-at-higher-types, seg-core-rebuild.
- /Users/coquand/POSET/survey-slides.pdf, /Users/coquand/CANONICITY/cours6.pdf.
