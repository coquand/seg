# Handoff: the model as a universe category (Voevodsky), 2026-10-15

## Goal

Develop the simplicial-set / poset model in a **shorter, more robust and more
modular** way, by presenting it as a *universe category* in the sense of
Voevodsky (V1.pdf, V3.pdf in `~/CANONICITY`): types are codes (maps into a
universe), type formers are single maps out of presheaves of data built from
the universe, and stability under substitution is composition of maps
instead of a separate theorem for each construction.

Constraints (Thierry):
- **No change of the type theory** (no new conversion rule, no kernel change).
- **Abstract results**: the base category stays generic (posets and Delta are
  instances).
- The usual seg rules: abstract first then instance; never fork generic
  copies; one home per fact; every `--only` check under 10 s (a slow check is
  a mismatch to fix); lock constructions right after their characterising
  lemmas; work on a copy until a step is green.

## Why (the diagnosis, measured)

The present development (`seg/model`, green 318/318 on 2026-10-15) builds every
construction on an arbitrary context and then proves, for that construction,
that it commutes with substitution. Over the 88 files of the univalence
development (about 9800 lines, measured by `proto/universe-category/classify.py`):

| layer | share |
|---|---|
| mathematics proper (Ext, Theorem 7, equivalences, ua operation, G7 core) | 36% |
| proofs that substitution commutes with a construction (GExtSub*, GExtNat*, GEquivSub*, GYonEq*, GUaOp6/7/8/10, GCompU2/3, ...) | 39% |
| transport of structures along equations of types (GEqLaws*, GEqExt, GExtFull(C), GTransferSub, GTransferEqCong, GUnivEq.comb, PElYon*) | 15% |
| moving structures between universe levels (GTransfer*, GFibMove) | 8% |

The root cause: a type over a context is a presheaf type whose action is
indexed by equality proofs (`Presheaf.PTy.tact ... e`), so two constructions
of "the same" type (e.g. El along c then substituted along s, versus El
along c∘s) differ by proofs; they are equal only by a lemma, and every
structure on them must be transported and shown coherent.

Read first: `seg/notes/type-formers-as-maps.pdf` (two pages: the idea and the
measurement), then V1.pdf §2 (universe categories, the C-system CC(C,p);
contexts are lists of codes, substitution is precomposition, one lemma 2.5
about chosen pullbacks), then V3.pdf §2 (a type former as a (P, P~)-structure
on p: one map out of an object built from p, a pullback square for
λ/app/β/η). V3 remarks that this is the main ingredient of the univalent
model in Kan simplicial sets (Kapulkin–Lumsdaine–Voevodsky), i.e. our model.
(`seg/notes/substitution-styles.pdf` is an earlier note, superseded.)

## The dictionary

| Voevodsky | seg |
|---|---|
| category C | presheaves on the base (`GPre[a]`, generic base) |
| universe p : Ũ → U | `GUniv.Univ` (U0 = code: type over a representable + its fibrancy structure), El over UCtx |
| type over X = map X → U | a code map `c : D → UCtx` (now `GElC.Fam[D, c, cnat]`) |
| substitution = precomposition | `xsub` along `xoS c s` (prototype) |
| chosen pullback (X; F), Lemma 2.5 | El substituted along c (`xsub`), its composition law `xsub-o` |
| (P, P~)-structure on p | Ext/Glue as one map out of the presheaf of glue data |
| p univalent | `UaOp` (cours6 form), proved on the universal data |
| U fibrant | G7 (`GCompU5.FibU`), a property of the object U |

## What is already checked (prototype, not in `model/`)

Files: `seg/proto/universe-category/GSmall.seg`, `GSmallEl.seg` (to be
imported in `IvBase.seg`: `import GSmall ;` just before `import GElC ;`,
`import GSmallEl ;` just after it; checked on a copy, 22 and 25 declarations,
3.4 s and 2.9 s).

- `GSmall`: `SPTy[G]` = a *small* type over a *large* context (context at
  level a+1, fibres at level a: exactly what El over UCtx is); `XSub[D, G]` =
  maps from a level-a context into it; `xsub` = substitution along them;
  `xoS` = composite with an ordinary map; **`xsub-o` proved once for all
  small types** (two paths in a set give the same action, then `ty-ext2`).
- `GSmallEl`: El defined once as `SPTy[UCtx]`.
  - `GElC.Fam[D, c, cnat].ElTy ≡ xsub c El` holds by `refl` (El along a code
    map *is* El substituted along it).
  - `elSub`, with its exact present statement, is a one-line instance of
    `xsub-o`.

Other facts established (scratch experiments, not to be redone):
- In the base category `Cat` (both instances use it), `comp-assoc`,
  `comp-idl`, `comp-idr` hold by `refl` once `compH`/`idH` are not locked;
  unlocking them breaks nothing and speeds up the slow files (GExtNat4
  6.6→5.9 s, PElYon 6.7→6.1, GUaOp8 6.1→4.9, DGlueClSub 6.8→6.4). But the
  base must stay generic, so inside `IvBase` the laws remain parameters.
- Records with proof fields (`PSub.nt-nat`, `PTy.tact` along `e`) are the
  reason substitution laws are propositional; this is not fixable without a
  type-theory change (rejected). The plan therefore aims at proving each law
  **once**, not at making it definitional.

## Plan (steps with checkpoints)

Work in a copy of `seg/model` (e.g. `cp -R seg/model <scratch>/uc/model`),
check with `timeout 10 $(cabal list-bin seg) model/All.seg --only <M>` from the
copy's parent. Land in `seg/model` only with seg-62's agreement, in a window.

**Step 1 — El and its structures from the universal family.**
- Finish the structure side: compositions on `xsub c A` from compositions on
  the lift of A (this is `GTransfer.Tr` with identity fibre maps), and the
  law "compositions substituted twice = substituted along the composite",
  generically for any `SPTy` (adapt `GElC.ElF.FibSub` with `xsub` in place of
  `Fam`; the proof-irrelevance lemmas `isProp-CnT`/`PhNT`/`LawT` become
  generic over `XSub`).
- Checkpoint: `GElC.ElF.FibSub.elFibSub` and the univalence-op obligation
  `tautCl-sub` become instances; `GElC.Fam` is replaced by `xsub` (one home).
  Measure lines removed from GElC and the transfer files.

**Step 2 — the presheaf of glue data and Ext as one map (the real test).**
- Build, at level a+1 like `UCtx`, the presheaf `GD` whose points at stage I
  are local glue data over `yP I`: a code A (with fibrancy), a cofibration ψ,
  a code B over the restriction to ψ, a map α : B → A|ψ, an equivalence
  structure on α. Coding: follow `GUniv` (codeU via `encCl`) and
  `GUnivEq.UaU` (`Q4`, `R`, `encUa` already code exactly such data;
  `encPMap`, `encEqOn` exist). The action is substitution along `yH`
  (`uActS`, `GEqLaws.eqDSub`), laws via `comb` as in `GUnivEq.r-id/r-o`.
- Define `Ext_U : SPTy[GD]` once (the local-data form of `GExt`/`GExt2`
  already computes Ext's codes from local data) with its fibration
  (Theorem 7 **once**, at the universal data: reuse `GExtComp*`, `GExtFib`).
- For data α over Γ, `Ext(α) := xsub ℓ_α Ext_U` with ℓ_α : Γ → GD the
  local-data map.
- Checkpoint: Theorem 7's naturality (today `GExtSub1-6` + `GExtNat1-10`,
  ~1700 lines) reduces to `xsub-o` (+ its fibration version) and ONE equation
  of data `ℓ_{α[s]} = ℓ_α ∘ s`. If this equation costs as much as the chain it
  replaces, stop and report: that is the decisive measurement.

**Step 3 — glue/univalence/universe on the universal data.**
- The glued type and its classifier (`GUaOp3`, `glueCl`) as one map out of
  the data presheaf; the univalence operation (`GUaOp9`) stated on `Q4`
  (already the presheaf of univalence data); `kunif`/`OutNat` (GUaOp6/8) and
  U6 (`GUaOp10`, the KESI) should follow from substitution laws.
- G7 (`GCompU1-5`): the side data is El's transport data substituted along
  the line of codes; `GCompU2`'s `tri`/`TrEqCong` should disappear.
- Checkpoint: line counts per layer (rerun `classify.py`), all files < 10 s,
  instances (posets `PUaOp`/`PCompU`, Delta `DUaOp`/`DFibU`) unchanged in
  statement.

## Success measure

- The naturality and transport layers (54% today) shrink substantially; the
  statements of the main results (Theorem 7, `UaOp.ua`, `FibU.fibU`) are
  unchanged and still generic over the base.
- Every file under 10 s, ideally under 5 s.
- The poset and Delta instances still green.

## Risks / open questions

- **Coding the data presheaves** at level a+1 (Step 2) is the main work; the
  pattern exists (`GUniv`, `GUnivEq`) but Ext's data includes a cofibration
  (a list of generators today; `GCofib.Cof`) and an equivalence structure.
- **Data equations remain theorems**: e.g. El along the Yoneda code of F is
  F (`elYon`, uses g∘id = g in the generic base); `ℓ_{α[s]} = ℓ_α∘s`;
  restriction of cofibrations (`pre-comp`). The plan assumes these are few;
  Step 2's checkpoint tests it.
- **Laws of maps are propositional in seg** (records with `nt-nat`); so the
  composition laws (`xsub-o`, `oS` associativity, chosen-pullback lemma) are
  equations proved once, not definitional.
- **Cofibrations as lists**: the U6 insertion work (`GCofIns`, `forallU-ins`)
  is a presentation issue that a one-sieve-per-cofibration redesign (deferred
  by Thierry) would remove; keep it separate from this plan.
- Coordination: seg-62 coordinates `seg/model`; canonicity-11 owns the Delta
  files (`Delta*`, `D*`, `Classical`). Ask before touching shared files.

## References

- V. Voevodsky, *A C-system defined by a universe category* (V1.pdf), §2.
- V. Voevodsky, *The (Π, λ)-structures on the C-systems defined by universe
  categories* (V3.pdf), §2; also V2.pdf (presheaves on universe categories),
  V4.pdf (products of families).
- Kapulkin–Lumsdaine–Voevodsky, the simplicial model of univalent foundations.
- S. Awodey, natural models; Lumsdaine–Warren, local universes.
- Th. Ehrhard / `~/DOMAIN/MODEL/cwf2.pdf` (the analogy for substitution).
- `seg/notes/type-formers-as-maps.pdf`, `seg/CYLINDER.md` ("Univalence,
  generic", for the present development).
