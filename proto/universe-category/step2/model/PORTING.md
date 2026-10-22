# Porting ~/DOMAIN/MODEL to seg: conventions and decisions

How the Agda development `~/DOMAIN/MODEL` is ported to `model/*.seg`, so that a
fresh session can continue.  The table in `../README.md` lists what is ported.

## Checking

    $(cabal list-bin seg) model/All.seg --only M     # check module M, trust the rest
    ./check-model.sh                                 # every import of All.seg, each < 10 s
    $(cabal list-bin seg) model/All.seg --only M --unfolds   # which constants a proof unfolds

* **Ten-second rule**: every `--only M` run must stay under 10 s.  An overrun
  is a defect: speed the proofs up (below) or split the file (`Ext`, `Ext2`,
  ..., `ExtComp1` + `ExtComp1E`, ...).
* After each file: add `import M ;` to `All.seg` (after the previous one;
  each session appends only its own import lines), check it, and run a
  **mutation test** (break one proof step, check that it FAILS, restore).
* Two sessions port in parallel; do not port a file the other one owns.

## File layout

* `fe`/`univ` files live inside `module Model (fe ..) (univ ..) { import V ; ... }`
  in `All.seg`; files that use no axioms are imported at top level.
* A file begins with a comment saying which Agda file it ports and what it
  contains, then `level a ;` (or `level a l ;` + `constraint a <= l ;`) and
  its `open`s.  Agda's several levels become one level where Agda has
  several for no reason.
* A file module SHADOWS a member with the same name: hence the renames
  Trees, PreL, Encode, UnivCtx, UnivEl, Cofib (= Poset/Cof), ...
* Opens of a segment are not re-exported: a file that continues a segment
  (`ExtB2`, `ExtB3`, `C1E`, `C2N`, ...) repeats its parameters and its opens,
  then opens the previous part, e.g. `open ExtComp1[a].C1[G, A, psi, ...] ;`.

## Translation

* **Records -> segments**: fields are body-less units; derived lemmas are
  members; the record type is the segment used as a type, `M[args]`;
  elements are `new M[args, field1, field2, ...]`.  Agda `module _ (params)`
  and `where` blocks -> named segments (their shared telescope becomes the
  segment parameters).  Agda's nested `module A (..)` / `module B (..)`
  usually become ONE segment with all the parameters.
* **Implicit arguments**: none except hidden `{x : A}`; hidden FAMILIES
  (`B : A -> U`) are not inferred, so write them.  A hole `_` for an
  element is often solved wrongly: write the element out.
* **Matches**: `f refl = ...` -> `idJ`; dependent Bool/Fin/tree/Plus
  matches -> `split` helpers, one argument at a time (`true -> \ e -> split
  {...}` splits the NEXT argument); dot patterns -> lemma at the matched
  indices.
* **abstract -> `opaque f ;`** after the definition and its characterising
  lemmas.  Agda `opaque unfolding X` lemmas must be defined before `opaque X`.
* Families are eta-expanded for cumulativity (`\ z -> W0.Ix z`).
* `U` is a keyword (no variable named U); no shadowing of names in scope.

## Decisions (user rulings)

* **Conversion is cubicaltt-style**: structural `u == v`, otherwise whnf,
  unfolding every non-opaque constant.  Hence:
* **Opacity: let the mathematics decide.**  Lock a construction right after
  its characterising lemmas (V-codes after their Ix lemmas; Ext/ext/glue
  after Lemma 6 / Theorem 7; fillers after their equations; EquivOp /
  ContrOp used by their fields).  `--unfolds` only confirms.
* **Category laws on the nose (option 3)**: NO definitional proof
  irrelevance, no rework of the universe; keep compH / idH / app / mkHom
  transparent where Yon / UAct / EGen / ElFam need the laws definitionally;
  `hom-eq` is welcome elsewhere.
* Use segments MORE (telescopes as parameters, abbreviations as members);
  report the size before/after for refactors.

## Records are compared by name (checker rule, 2026-10-13)

`new M[..]` / `sig {..}` / `struct {..}` get an internal name from their
text: two of them are equal only if they come from the SAME occurrence
(with convertible free variables).  A variable of segment type is still
compared by its fields.  Hence ONE named constructor per record, used
everywhere:  Boxes.mkSide / mkBox / mkCompOp (Box.seg), Psh.mkTy
(Presheaf.seg; every PTy, including subTy, goes through it), Sq.mkFD
(TranspSq.seg).  Never write `new P.Box[..]` etc. outside the constructor.
To state a principle for a given type, take the type as a segment
parameter (FibExtV: FEV (G) (A A' : PTy[G])) rather than building it.

## Speed idioms

* Hidden-point unification is the main cost: give chains their points
  (`trans A x y z p q`, `ap A B f x y p`, `sym A x y p` from Prelude, or
  `transH {A}{x}{y}{z}`), especially through opaque constants.
* Do NOT abbreviate with local alias members (`g = compH ..`,
  `bf = restrict ..`) inside a lemma whose stated type is written literally:
  the structural mismatch makes conversion whnf both sides down to
  `new Box[...]` (8.9 s -> under 1 s after inlining).
* Cross-file opens of segment instances are slower than local ones; split a
  file when it nears 10 s.
* Open only the file modules you use: an UNUSED `open ExtBox2[a] ;` cost
  4.3 s on LBox (reported to the src owner).  A small lemma used once from a
  big file is better proved locally (Agda often does so too).
* Long chains: generate nested `trans T x0 x1 xn p (trans ...)` with all
  points written (a helper script makes this mechanical).
