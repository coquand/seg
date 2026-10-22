# seg

A dependent type theory checked in a context of **unit declarations**, with
AUTOMATH/Wang **segments** as the module system and the **BCDE universe
system** (bcde.pdf, ~/DOMAIN/BCDE4: level variables, constraints, cumulative
Russell universes, level- and constraint-indexed products).  Successor of
`../mtt` (kept unchanged; CHWISTEK depends on it).  Haskell2010, `base` only.

    src/Level.hs      levels, theories, Bezem-Coquand validity and loop check
    src/Seg.hs        syntax, glued values, whnf under a lock, conversion, checker
    src/SegParse.hs   lexer, parser, resolver (scope, ids, dependency analysis)
    app/Main.hs       driver: imports, 10 s budget per declaration, directives

    cabal build && $(cabal list-bin seg) examples/basic.seg
    ./run-tests.sh                      # examples/*.seg, each must print OK
    $(cabal list-bin seg) model/All.seg # the port of ~/DOMAIN/MODEL so far
    $(cabal list-bin seg) model/All.seg --only Box   # check one module, trust the rest
    ./check-model.sh                    # every module, one run each, each < 10 s
    $(cabal list-bin seg) model/All.seg --each   # every module in ONE process
    $(cabal list-bin seg) model/All.seg --repl   # a session: check M | each | reload | quit
    $(cabal list-bin seg) core/All.seg  # the generic core and the poset model (~50 s)

`core/` is the current development: the poset model and its localisation D.
The convergence of the Postnikov approximations (D A is the strict limit and,
for fibrant A, the homotopy limit of the D_N A) is presented in
`notes/postnikov-limit.pdf`; its appendix lists the files of `core/` for each
statement (CPostConvergence.RightInverse.homotopy,
CPostInvNat.LeftInverse.homotopy, CPostFib.PostFib.fib).

`--each` checks the modules one at a time in a single process: the port is
parsed once and what is evaluated for one module is reused by the next.
`--repl` keeps the loaded port in memory (as Gofer's `load` and cubicaltt's
REPL do): `check M ..` checks modules (the rest trusted), `reload` re-reads
the files after an edit, and results already computed stay until then.
Commands can be piped in:  printf "check Box\ncheck Fib\n" | seg model/All.seg --repl

`--only M` checks the declarations of module M only; everything else is
TRUSTED: entered into the context (lazily) but its proofs not checked.  The
context after a declaration never depends on whether it checked, so this is
Agda's separate checking of modules, with no interface cache to keep
coherent.  check-model.sh runs it for every import of model/All.seg.

## Units

A program, a module body and a `let`/`where` block are lists of units; checking
threads a context of units (final.pdf ch. 3, generalised):

    x (tel) : A ;                 parameter (top level: primitive notion)
    x (tel) : A = e ;             definition (body: expression or split, + where)
    data D (tel) : U l = c (tel) | .. ;   labelled sum; without ": U l" it is
                                  small and lies in every universe (bcde: N : U_l)
    level a b ;                   level variables
    constraint a < b, c <= a \/ b ;
    module M (tel) { units } ;    a segment: its parameters are its body-less
                                  units (term, level), its constraints are
                                  obligations on every instantiation
    module N = M[args] ;          an instance
    open M ;  open M[args] ;      short names for the members
    import F ;                    F.seg spliced as  module F { .. } , once
    opaque f ;  transparent f ;  transparent_all ;
    #normal e ; #type e ; #conv e = e' ; #fails { units } ;

Consecutive definitions form one mutually recursive group.  Telescopes:
`(x y : A)`, `(a b : Level)`, `(a < b)`.  Expressions add to mtt's: `U l`,
`[a] A`, `<a> t`, `t @l`, `[a < b] A`, `sig { l : A ; .. }`,
`struct { l = e ; .. }`, `e.l`, `M[args].x`.  Levels: `a`, `l+`, `l \/ m`.

## What the design does

* **Segments share.**  `M[args]` only binds M's parameters in an
  environment; nothing is copied.  A member keeps one identity, its qualified
  name, and its value is *glued*: the name, the values of the variables it
  depends on (computed statically: its dynamic part, bengt.pdf slides 31-33),
  and a lazy unfolding.  Conversion compares name + dynamic part + spine
  first and unfolds only if that fails.  So `M[fe,ua].f` reached through two
  different paths is one object (examples/locks.seg, model/VTests.seg) --
  the cause of the Agda slowdowns described in ~/DOMAIN/MODEL/modules.tex.
* **Parameters once.**  `module Model (fe : [b] Axioms[b].FunExt) (univ : ..)`
  holds the two axioms of the metatheory; every file is a sub-segment and
  sees them lexically.
* **The lock is a property of the run** (Wang).  Values are computed
  lock-agnostically; only whnf consults the strategy, so `opaque M.f` placed
  after M applies to every instance of M.  Command line: `+id`, `-id`,
  `--none`.  Locking only under-approximates conversion.
* **Universes.**  `U l : U l+`; cumulativity `A : U l, l <= m => A : U m` at the
  top (BCDE4's SubTy), not under Pi -- eta-expand (`\ b -> T b`) as BCDE4's
  coercions do.  `[a]A` and `[psi]A` are large types (in no universe); a
  constraint product is introduced and discharged silently (`[psi]A = A`
  when psi is valid).  Validity and loops: Bezem-Coquand forward reasoning
  with a cap (Level.hs explains why the cap is exact).  A context with a loop
  collapses (Gonthier's rule, bcde App. C): everything converts.  Internally
  there is a bottom level `0` (`0 <= a` for all a), used only as the level of
  the small data types; the user cannot write it.

## Equational chains

    calc A { a0 =< p1 > a1 =< p2 > a2 .. =< pn > an }

writes every point once (examples/calc.seg).  It is notation: the parser
turns it into Prelude's `trans` (J on the second path), right nested as
`trans p1 (trans p2 ..)`, so the chain is definitionally the nested
`trans`.  The type `A` is given, nothing is inferred, and each step is checked
on its own: `pi` against `Id A a(i-1) ai`, so a wrong point is reported at
its step.  model/ElFam.seg (snatU, cbU) uses it.

## Segments as types (after Arend's records/classes)

A segment name is also a TYPE: the Sigma of its parameters, with its
defined members available on every element (Arend's `\func` inside a
record, with implicit `this`):

    module Mon (l : Level) { A : U l ; op : A -> A -> A ;
                             sq (x : A) : A = op x x ;     -- a member
                             e : A ; sqe : Id A (sq e) e ; } ;
    Mon[a]                     a type (level parameters must be fixed)
    Mon[a, N]   Mon[A := N]    a partial instance is a type (Arend's class
                               extension C { | f => e }); positional args
                               fill the parameters in order, named by name
    new Mon[a, N, plus, zero, refl zero]     an element
    M.sq  M.op                 members and fields of an element M
    module Ops (M : Mon[a]) { open M ; .. }  open a variable of segment type

* An element is an instance environment; `M.sq` is the member evaluated in
  it, a glued value compared by name and the fields it uses: no copy.
* A variable of segment type is bound to its eta-expansion, so a fixed field
  computes: `M : Mon[A := N]` gives `M.A = N`.  Elements have eta.
* Subtyping: `Mon[I] <= Mon[I']` when every field fixed in I' is fixed (to a
  convertible value) in I, or is that value in the element itself.
* The universe of `Mon[a]` is the join of the sorts of its parameters
  (computed when the segment is checked); a large parameter makes it large.
* **Constructors.**  A segment `M` whose body has fields gets
  `mkM (params) (fields) : M[params] = new M[params, fields]`, defined just
  after it (examples/records.seg).  Since `new` occurs once, elements built
  with `mkM` compare by name (by-name rule above).  Not generated when the body
  has `level`/`constraint` units, when a field has hidden binders, when a
  field type mentions a member of the body, or when the user defines `mkM`
  in the same block (the port's hand-written mkBox, mkSide, .. stay).
* Not done: Arend's `\extends` (inheritance between segments), instance
  inference, `\default`.

## Hidden arguments (the Agda-wiki design, no unification)

https://wiki.portal.chalmers.se/agda/Main/ImplicitSyntax: hidden arguments
are notation on top of the explicit system.  `f {x : A} (y : B) : C` has the
ordinary type `(x : A) -> (y : B) -> C`; hiddenness belongs to the
declaration, and a USE of `f` is read with a hole `_` at each hidden
position ("f is understood as f _ _").  `{e}` gives a hidden argument, `_`
asks for any argument to be inferred.

A hole is filled by one-way MATCHING, never unification: the domain of a
later explicit argument (holes as rigid placeholders) against that
argument's inferred type, then the result type against the expected type.
The solution is quoted back into a term of the current scope; the core only
ever sees filled terms.  A hole that is not determined this way is an error
asking for `{e}` (examples/hidden.seg shows `comp idm (comp idm f)`, whose
middle object needs unification).  Works well: path lemmas
(`trans p (sym p)`), fields whose explicit arguments fix the indices
(`idl (comp idm f)`).  Needs hints: a bare `p`, `lift s`, `id` whose index
is fixed only by a sibling argument's expected type.

## The port of ~/DOMAIN/MODEL (model/)

| Agda | seg | status |
|---|---|---|
| Prelude.agda | Prelude.seg (segment, one level) | checks |
| Axioms.agda | Axioms.seg (FunExt, Univalence at a level; lemma segments) | checks |
| Lv/Base.agda | -- | not needed: it only existed for lack of cumulativity |
| Lv/V.agda, V.agda | V.seg (segment in Model, level l) | checks |
| CwF.agda | CwF.seg: `CwF[l]` a segment type with derived members between fields; Formers over `(C : CwF[l])` with UnitStr..IdStr as segment types; Eta | checks |
| -- | VTests.seg | computations through instances, #fails |
| VModel.agda | VModel.seg: the CwF of iterative sets as `new CwF.CwF[..]`, formers as `new F.UnitStr[..]` etc., Nat; all CwF equations refl (pairs have eta) | checks |
| Lv/SmallCat.agda | SmallCat.seg (level k) | checks |
| Lv/Presheaf.agda, Presheaf.agda | Presheaf.seg: `Psh (C)` with PCtx/PSub/PTy/PEl as segment types; category at k, presheaves at l >= k | checks |
| Lv/PresheafFormers.agda | PresheafFormers.seg: Un[G], SigAB[G,A,B], SigNat, IdAB, IdNat segments; hidden path lemmas (427 -> 303 lines after the refactor) | checks |
| Lv/VLift.agda | VLift.seg: liftM without Lift/lower; PiS | checks |
| Lv/PresheafPi.agda | PresheafPi.seg: RawPi, PiCode, PiNat as segments | checks |
| Poset/Tree.agda | Trees.seg (renamed: the file module would shadow the data Tree) | checks |
| Poset/Cat, Constr, Test, Model | Cat.seg, Constr.seg, Test.seg, PosetModel.seg | checks |
| Poset/Arith, Simp | Arith.seg (helpers with permuted arguments where Agda splits a later argument first), Simp.seg | checks |
| Lv/Pre.agda | PreL.seg (renamed: Constr has a segment Pre) | checks |
| Poset/D.agda | D.seg: NatMap a segment type; DT, Act, FacesGen, Vx, Mu, DMap, Laws segments | checks |
| Poset/BoxBase, Lv/Box | BoxBase.seg, Box.seg: Side, Box, CompOp segment types (s.svE a member) | checks |
| Poset/FillBase.agda | FillBase.seg: Recs with Stage/Cross segment types, FB | checks |
| Poset/FillCell.agda | FillCell.seg: dot patterns as lemmas at the matched indices + idJR (Paths) | checks |
| Poset/FillStage, FillComp | FillStage.seg, FillComp.seg (Lemma 2.1: horn -> comp(DA)) | checks |
| Poset/HornFace, Conn, Lv/Fib, BoxHorn | HornFace.seg, Conn.seg, Fib.seg (FillOp a segment type), BoxHorn.seg (comp -> horn) | checks |
| Poset/CompDA, PropD | CompDA.seg, PropD.seg (Proposition 4.1) | checks |
| Poset/Sum, DPath, DPathEnd | Sum.seg (ordinal sums; OSum/Inner/Outer/Same segments), DPath.seg, DPathEnd.seg (Lemma 3.1; Agda's opaque/unfolding = segment RAt with `opaque R`, where-blocks = segments) | checks |
| Lv/FibSub, FibSig, FibNat, FibPath, FibPiE, FibPi (Poset/Fib* are their lzero shims) | FibSub.seg, FibSig.seg, FibNat.seg (Disc/Nat/Unit), FibPath.seg, FibPiE.seg, FibPi.seg: fibrancy of substitution, Sigma, discrete types, Path, Pi; one level l | checks |
| Lv/Level1 | Level1.seg: the instances at (l, l+); Fib* are two-level (a, l) for this | checks |
| Lv/Esi, EsiRes, EsiFill, EsiSub, EsiNat, EsiSig, EsiPi, EsiPath | Esi.seg (InsE a segment type), EsiRes.seg, ... EsiPath.seg | checks |
| Lv/FibExt, Lv/Enc | FibExt.seg (fibExt, via Presheaf's tact-funext / idLaw-prop / oLaw-prop), Encode.seg (renamed: a module Enc would shadow the type Enc) | checks |
| Univ/Yon, UAct, UEnc, UCtx | Yon.seg, UAct.seg, UEnc.seg (codeU, encUf opaque), UnivCtx.seg (renamed: shadowing; UCtx, UTy, EGen) | checks |
| Univ/EGenComp, EGenEsi | EGenComp.seg, EGenComp2.seg, EGenComp3.seg (split for the 10 s cap; cunifC's chain points stated), EGenEsi.seg | checks |
| Univ/El, Lv/VAbs | UnivEl.seg (renamed: shadowing), VAbs.seg | checks |
| Univ/ElFam | ElFam.seg .. ElFam4.seg (split; chains with explicit points) | checks |
| Poset/VCode | VCode.seg (PiO/SigO/IdO/PiO3 opaque formers; `unfolding` lemmas stated before the opaque line) | checks |
| Poset/Cof | Cofib.seg (renamed: shadowing; Cof, PSide, Partial, ContrOp segment types) | checks |
| Poset/Equiv | Equiv.seg (PMap segment type, FibTy, EquivOp) | checks |
| Poset/Ext | Ext.seg (codes, opaque Pairs interface), Ext2.seg (PAct, ExtT by cases), Ext3.seg (EX forms), Ext4.seg (extMap, glue, ext-det) | checks |
| Poset/ExtKit | ExtKit.seg (LineBox; LFam/LData segment types; FE and its laws opaque) | checks |
| Poset/ExtBox | ExtBox.seg (MapBox), ExtBox2.seg (BoxPlus, PFam segment type), ExtBox3.seg (restriction, FEp-unif via FEp-def) | checks |
| Univ/FibExtV | FibExtV.seg (FEV segment; Agda's refl-matches as idJ) | checks |
| Poset/ExtEquiv | ExtEquiv.seg (toFA/fromFA, Tr, kE), ExtEquiv2.seg (Th: line box, a0, pairs, v0), ExtEquiv3.seg (kopX, sides, uniformity, extEquiv) | checks |
| Poset/ExtComp1, 1b, 2, 2T, 3, 4 | ExtComp1.seg + ExtComp1E.seg, ExtComp1b.seg, ExtComp2.seg + ExtComp2N.seg, ExtComp2T.seg, ExtComp3.seg, ExtComp4.seg + ExtComp4U.seg (one segment per Agda C/D pair) | checks |
| Univ/LBox | LBox.seg (ExtKit's LineBox over any line, lid at eS; fopA opaque) | checks |
| Univ/EndQ | EndQ.seg (tree matches as split helpers) | checks |
| Univ/Transp, TranspSq, TranspSqN, TranspB, TranspP, TranspPU, TranspEquiv, TranspEquiv2 | Transp.seg .. TranspEquiv2.seg (segments Tp, Sq, SqN, TB, TP, TPU, TEq, TEq2; FD is a segment type, FD-ext on components; trEquiv) | checks |
| Univ/LBSub, FillSub, RelGen, BCBase, BCB | LBSub.seg, FillSub.seg, RelGen.seg, BCBase.seg, BCB.seg | checks |

Check with `./check-model.sh` (each module with `--only`, the rest trusted,
each under the 10 s cap); a single `model/All.seg` run is about 1600
declarations.  model/Paths.seg has the path lemmas with hidden
type and endpoints (symH, transH, apH, substH, happlyH); `_` works for any
argument.  Mutations are caught in each file.  CwF.seg gained NatStr.

Porting notes: a file module shadows a member of the same name (hence
Trees, PreL), and `open M` also brings M's module aliases into scope, so
files avoid top-level `module T = ..` aliases.  A constructor of another module's data type is written
unqualified (`sup A f`, resolved by the expected type); where-bindings are
not in scope in the result type (inline them, or add a top-level helper
such as `EP`); `(x : A) * B -> C` parses as a Sigma over `B -> C`, so
parenthesise the Sigma.  (Agda on the same files: 0.7 s; these are not the
slow files, so this is not yet the comparison that matters.)

Differences from the Agda source: no implicit arguments (endpoints explicit);
`f refl = ..` becomes one `idJ`; Agda's anonymous parametrised modules
(`module _ (R) .. where hedberg`) become named segments (`Hedberg[..]`); a
lemma at `U l` itself needs the next level, which a segment cannot do on
itself (`symU` in Prelude); `abstract mkEmb` is `opaque mkEmb`.

## Known limits

* Lambda binders may shadow; the dependency analysis assumes they don't
  shadow a variable that a local definition depends on.
* No implicit arguments, no unifier, no termination or positivity check.
* CwF uses one level where Agda has four (cumulativity makes the max do).
