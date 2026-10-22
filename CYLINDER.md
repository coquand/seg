# The cylinder interface, for posets and for simplicial sets

Goal: one proof of the model (seg/model) whose hypotheses on the base hold
both for the poset model (current instance) and for simplicial sets
(presheaves on Δ = finite non-empty linear orders, classical logic allowed).
Reference: Gambino–Sattler, *The Frobenius condition, right properness, and
uniform fibrations* (~/COLL/gambino1.pdf), §1 and §8; the awfs/Frobenius
machinery there is not needed.

## 0. The metatheory of the model (Thierry, 2026-10-15)

The complete argument is carried out in the segment metatheory ASSUMING
univalence and function extensionality (the two parameters of
model/All.seg's Model segment); both may be used anywhere, including to
transport data.  Terms built with them do not compute by refl, so when a
later step needs a definitional equality it is stated as a lemma.
Deriving funext from univalence is a later task.

## 1. Hypotheses, matched with Gambino–Sattler

E = Psh(C), C small, with terminal object [0] and an object Iv (= [1]), so
the interval I = y Iv is representable.

| G–S | statement | here |
|---|---|---|
| interval | δ0, δ1 : ⊤ → I | `e0, e1 : IPt` (points [0] → Iv), constant maps `ptH W e` |
| (1.1) contraction | ε : I ⊗ − → Id, ε δk = id | cartesian cylinder: ε = projection `pX` |
| (1.2) connections, j-faces | c_k (δ^k ⊗ I) = δ^k ε ; c_k (I ⊗ δ^k) = … | `conn-jsrc`, `conn-isrc` |
| (1.3) connections, other faces | c_k (δ^{1-k} ⊗ I) = id ; c_k (I ⊗ δ^{1-k}) = id | `conn-jtgt`, `conn-itgt` |
| naturality of c_k | c_k natural in the presheaf | `conn-cyl` |
| (C1), (C2) | I ⊗ − preserves pullbacks, δk cartesian | automatic: I ⊗ − = I × − (G–S Ex. 2.2) |
| (M1), (M3) | cofibrations are monos, stable under pullback | decidable sieves `Phi X`, `pre`, `Lands` |
| (M2) | 0 → X is a cofibration | `emptyS`, `empty-lands` |
| (M4) | closed under Leibniz product with δk | the shape of a box: sides `Q_j * I` plus the lid `X * {e}` (`InQ`, `endQ`, `allIv`) |
| Thm 8.1 | uniform lifting against all monos ⇔ against monos into representables | boxes are taken over representables y X, uniform in restriction along h : Y → X (`cunif`) |
| Rem. 8.4 | constructive with decidable monos | Phi decidable (`allS`) |

In Δ: Iv = [1], δk the two vertices, c0 = min, c1 = max on maps W → [1]
(G–S Ex. 1.1); Phi [n] = decidable sieves on [n].

## 2. The cylinder at the presheaf level

I × y X is not representable in Δ. A map y W → I × y X is a pair
(f : W → X, i : W → Iv); so

* `pX (f , i) = f`, `pr2 (f , i) = i`, `lid e g = (g , e ∘ !)`,
  `cyl h (f , i) = (h f , i)`, and the product laws (pr1-pair, pair-eta,
  pair-ext) hold by definition;
* a point of a context G over the cylinder, today `rho : G (X * Iv)`, is a
  natural family `rho (f , i) ∈ G W`, i.e. an element of Nat(I × y X, G);
  in the poset instance I × y X ≅ y (X × Iv) and this is G (X × Iv).

## 3. The obstruction: boxes over cylinders

The current proof composes boxes whose BASE is itself a cylinder:

* Fib (MkFill): the box `fbox` over `X * [1]` (fillers from compositions,
  along the connection), composed by `co.cop (XI X)`;
* FibPath: a path box over X is an A-box over `Z = X * [1]`;
* TranspP, ExtKit: boxes over `X * [1]_j`;
* PropD: composition along the contraction `[n+1] * [1] -> [n+1]`.

In Δ these bases (y X × I, y X × I × I) are not representable, so §2 alone
does not suffice: composition must be available for boxes over SHAPES
P = y X × I^k (finite products of simplices), naturally in maps of shapes.
Two ways:

(A) Shapes as the base of boxes.  S = the full subcategory of sSet on finite
    products of standard simplices (= finite products of chains, as posets
    with monotone maps, since the nerve is fully faithful on posets).  S has
    products and I ∈ S, so it satisfies the current CylCat hypotheses
    (category with products, interval, sieves, connections).  Contexts are
    simplicial sets G, evaluated on a shape by G(P) = Nat(P, G) (right Kan
    extension along Δ ⊂ S; Yoneda at representables).  Fibrancy = uniform
    composition for boxes over shapes.  The proof is reused as is, with
    C := S; what must be checked is that the type formers and the universe
    built over S restrict to sSet (the contexts used are of the form Ĝ).

(B) Boxes over representables only (G–S Thm 8.1), and composition over
    shapes DERIVED by triangulating y X × I^k into simplices (the prism
    chains P_k, Q_k of FillBase/FillCell already do this for [n] × [1]).
    No change of base, but every construction of §3 needs the derived
    composition and its uniformity.

(A) changes the instance, not the proof; (B) changes the proof.

## 4. Decision (2026-10-14): follow survey-slides.pdf (option C)

Internal formulation, as in ~/POSET/survey-slides.pdf (slides 4-15):

* trivial fibration = uniform extension structure for partial elements
  (one map out of Partial_Γ(A); property = structure, no choice).  In the
  code: `Cofib.Partials[D, C].ContrOp` already is this notion.
* A over Γ is fibrant when ev_e : A^I -> A ×_Γ Γ^I is a trivial fibration
  (e = e0, e1): a partial line with a total end point extends to a total
  line.  Filling is primitive; composition is evaluation at the other end.
  So no box over X × I is needed: boxes over cylinders become partial
  elements of the path object A^I over X (exponential law), and §3 disappears.
* Π, Σ, paths, Glue / equivalence extension: internal arguments, valid for
  any base with an interval with connections and cofibrations (M1-M4):
  posets and Δ alike.
* The universe of fibrant families needs I tiny (slide 12).  Posets: I is
  tiny (products in the base, I representable: X^I(c) = X(c × I)) — the
  current U0 X = FibE (y X).  Simplicial sets: Δ¹ is not tiny; the universe
  is defined by horn filling, with classical logic at exactly one point,
  box filling ⇔ horn filling (slide 10).  The model already has both
  directions in the poset setting: BoxHorn (comp -> horn), FillComp/PropD
  (horn -> comp in D).

DECISION (Thierry, 2026-10-15): PRESENTATION INVARIANCE is solved by
CANONICAL SIEVES on Delta.  Phi on Delta is the type of DECIDABLE SIEVES
on [X] (DeltaBase.DPhi: a Boolean predicate on the maps into [X], closed
under precomposition; equal sieves are equal by funext, dphi-ext), not
single faces.  A union is one sieve, and forall of a list of lines is ONE
sieve (DeltaForall.forallS, decided on the shuffles of the prism by
PrismCov), so IvBase.FaU's list has one element on Delta.  FaU gained
forallU-len / forallU-pre (the list is stable under restriction: same
length, per-index pre), which posets satisfy per line (Fa.forall-pre)
and Delta by forallS-pre.  This is what Theorem 7's uniformity needs:
the partial elements built on delta = forall psi restrict side by side.
The Delta probes (prism triangles T1, T2: forall T1 at vertex 0 only,
forall T2 at vertex 1 only, the edge in forall (T1 u T2) and in neither
alone) give the same answers, by refl (compH / idH unlocked for the
probes only).  The poset-and-Delta ForallPos proof is now the poset one
only; DeltaNat's subset codes (enc / dec) were removed.

### Plan

1. [done 2026-10-14] FibTriv: for A over Γ and an end point e, the context Γ^I ×_Γ A and the
   type of lines over it; fibrancy FibT e := ContrOp of that type.  Bridge
   FibT e <-> Fib.FillOp[e] for the poset instance (box sides <-> partial
   lines, by the existing LBox / ExtKit conversions: a side at psi is the
   line at pX psi evaluated at (id , pr2 psi)).
2. Path object of a context as an interface operation (Γ^I with ev_e,
   constant lines, connections, the exponential law), instantiated by
   Γ(X × Iv) for posets and by natural families on yX × Δ¹ for Δ.
3. Re-prove fibrancy of Π, Σ, Path, Glue from FibT (internal arguments);
   retire MkFill (fill from comp) and the boxes over cylinders.
4. Universe: tininess (posets) as now; horns + classical box⇔horn (Δ).

## 5. Status of the code (seg/model, 2026-10-14)

* CylCat: category, products with Iv, interval points, sieves (Phi, pre,
  Lands, phi-ext, emptyS, ptS, allIv, allS), connections (Conns: conn,
  pX-conn, the four faces, conn-cyl; conn-end derived).  Poset instance in
  Constr (PSv) and Conn (PCn).
* Pointwise reasoning (El / app / trees) remains in the poset-specific
  modules (Constr, Conn, Simp, D, DPath, PropD, BoxHorn, HornFace, Fill*)
  and in ~140 `PW` uses elsewhere (pointwise twins of map equalities, to be
  removed).

### Step 1 as built (2026-10-14)

* CylCat: `cyl-id`, `cyl-comp` (the cylinder is a functor), `cylEv`,
  `cyl-evm` (psi = (pX psi * Iv) (id , pr2 psi)).
* PathObj: `GI` (lines in G), `ev e : PSub[GI, G]`, `AI : PTy[GI]` (lines in A).
* FibTriv: `SFib` (strict fibres of a PMap), `TrivFib`, `LineFib.Ev[e].evA`
  (evaluation of lines at e), `LineFib.FibAt e` = TrivFib of evA e.
* FibTrivFill (1a): `ToFill[G, A, e, k].fillOp : Fib.FillDef.FillOp[e]` from
  `k : FibAt e`.  A box is a partial line (the side at f is read along
  f * Iv); its filler is the extension.  `SL.pv` is locked after its
  characterisation (pv-pt, pv-line).  3.9 s.
* FibTrivFib (1b): `ToFib[G, A, e, fo].fibAt : FibAt e` from
  `fo : FillOp[e]`: a partial line is a box (side at psi = the line at
  pX psi read along cylEv psi; v locked after v-def / side-E); kunif by
  box-ext.  CylCat: cylEv-cyl, cylEv-lid, cylEv-nat, cylEv-pX.  3.1 s.
  So for posets FibAt e and FillOp[e] are equivalent; every existing
  fibrancy result transfers.
* Lesson (both directions): state lemmas with the callee's names (no local
  aliases such as psi := .., x' := ..; XI X vs prodP X Iv), and lock value
  functions (pv, v) after their characterisation, or conversion unfolds
  down to the poset objects (mkOb, app).

### Composition stays the stored structure (user, 2026-10-14)

FibE keeps (Comp, ESI); filling is shown equivalent to composition:
* CompFill.seg: `F2C` (filling -> composition: evaluate the filler at the
  other end), `fill-to-comp`; with `FillB.comp-to-fill` (MkFill),
  `comp-fill-comp : fill-to-comp (comp-to-fill c) = c` given ESI (FillTop).
* FibTrivFib.CompFib: `comp-to-fib`, `fib-to-comp` (through filling).
The other round trip (fill -> comp -> fill) is not the identity on the
nose (fillers are not unique).

### Step 2 as built (2026-10-14)

* FibTriv: `PathStr` (interface: pth, pev, pthTy, pevA), `LineFibP[P, G, A]`
  (FibAt for any path structure), `posetPath` (instance: PathCtx.GI,
  PathCtx.ev, PathObj.AI, PosetEv.evA); `LineFib.FibAt := LineFibP[posetPath]`.
  PathObj.seg split into PathCtx (lines in a context) and PathObj (in a type).
* FibTriv: `CompAtP[P, G, A, e, e']` — composition in line form for any
  path structure (cop on the partial lines of FibAt e, cside against the
  ends at e', cunif), and `FromFib` (FibAt e gives CompAt e e').
* CompLine.seg (posets): box CompOp e e' <-> CompAt e e' (ToCompAt,
  ToCompOp), from FTC.BP / FTC.BPR (box -> partial line, restriction) and
  PBox.ToBox / PBox.BoxR (partial line -> box).  2.8 s.
* Lesson: give the implicit end points of transH / apH between box terms
  explicitly (inferring them by unification through record projections
  overran); use Box's XI X, not prodP X Iv, at comparison points with box
  terms.

### Cofibrations on Delta: generators and lists (2026-10-14)

Question raised: Phi [n] (from posets) is a decidable VERTEX subset Q, with
f landing iff im f is contained in Q; on Delta that is a single face, so a
horn or a boundary is not an element of Phi.

Statement of the (naming) mismatch: Phi X is not the type of cofibrations
but of their GENERATORS.  A cofibration is a finite list of generators:
the sides of a partial element (GCofib.Partial: pr sides, each over its
own Phi X) and the extents (Cofib.Cof[G]: cr subsets cQ X rho l).  Its
sieve is the union of the generated sieves (f lands in SOME Q_l).  On
Delta this is enough:

* every decidable sieve S on Delta[n] (a downward-closed decidable set of
  faces) is the union of the faces generated by its maximal elements, so
  it is the list of these vertex subsets; horns Lambda^k[n] (the faces
  d_i, i /= k) and boundaries are such lists;
* binary join = concatenation of lists; FillLine already uses it for
  psi \/ (i = e) (side 0 prepended to the sides of p); restriction along
  f is pre on each generator (the inverse image of a face is a face);
* the empty sieve = the empty list (emptyS is a generator only for the
  "empty side" convention of Esi).

Open obligation (presentation vs sieve): cours6 takes Phi as a sublattice
of sieves, so an operation depends only on the SIEVE.  With lists, a
composite or filler may depend on the PRESENTATION (order of the sides, a
side contained in another, the same sieve from different maximal faces).
ESI covers only the insertion of an empty side.  To be settled when FibE
and the universe are built: either invariance under permutation and
under absorbing a contained side, or the places where it is not needed
(e.g. when the structure is a proposition).

So Phi stays as it is in IvBase; what is renamed in the documentation:
"sieves" -> "generators of sieves".  What does NOT carry over to Delta yet:
forall along the interval (allIv, in Cyl), used by Glue / the extent
dQ: it needs the products of the base.  On Delta it must be restated on
the path object (a cofibration on lines), when Glue is moved to the
generic layer.

### The base as a segment; posets as its instance (2026-10-14)

Methodology (user): the poset model is an INSTANCE of the abstraction; no
generic copy lives beside a poset twin.

* IvBase.seg: `module IvBase { obV ; homV ; idH ; compH ; laws ; Iv ; IPt ;
  e0 ; e1 ; ptH ; ptH-nat ; src ; tgt ; Phi ; pre ; Lands ; ... ; allS ... }`
  (fields, no products), derived sieve laws, and the generic files imported
  INSIDE it: GPre (PshL, TyL), GCofib (Partials, ContrOp), GLine (PMap,
  SFib, TrivFib, PathStr, LineFibP, CompAtP, PathConn), GFam (the family
  path object famPath / famConn, for any base).  Nested segment `Cn`
  (interval connections cI + laws) imports GConn (ConnKit), GFill, GFillFib.
* PosetBase.seg: `module PB = IvBase[a].IvBase[obV, homV, idH, compH, ...,
  src, tgt, Subset, pre, Lands, ...]`: a MODULE instance, so its fields ARE
  the poset values (one name per object).  Poset files declare
  `module BaseP = PosetBase[a].PB` (it must be in scope for hidden
  arguments mentioning BaseP.BC to be written).
* Replaced by instances and deleted: PreL (BaseP.GPre), Cofib.Partials
  (BaseP.GCofib, as Cofib.GP), Equiv.PMap and FibTriv's SFib / TrivFib /
  PathStr / LineFibP / CompAtP (BaseP.GLine, opened), PathConn.seg,
  FillLine.seg, FillLineFib.seg (PosetConn: `module PCnB = BaseP.Cn[cIp,
  ...]`, PosetFill = PCnB.GFillFib instance).  Fin moved to Arith.
* Mismatches met and fixed (each was a slowdown or a failure): a record
  value's projection (posetBase.compH) vs Cat.compH (60k unfoldings);
  BaseP.BC not nameable unless BaseP is in scope; PCyl.src vs a second
  split for the end points (src/tgt are now base fields bound to PCyl's).
* CylCat built ON IvBase: CylCat.seg is imported inside IvBase as the
  nested segment Cyl (binary products only; Sieves adds allIv); the poset
  instance lives in Constr: `module PosB = IvBase[a].IvBase[...]` (base
  sieves of PosetSub), then `module PCyl = PosB.CylCat.Cyl[prodP, ...]`
  and `PSv = PCyl.Sieves[allIv, ...]` (PosetSubC).  src / tgt are IvBase
  members (one home).  Poset files `open PosB ; open PCyl ; open PSv` and
  declare `module BaseP = Constr[a].PosB`.  PosetBase.seg and Cat.PosetCat
  deleted (PosB.BC is the poset category).
* DeltaBase.seg: Delta as the instance `DB = IvBase[a].IvBase[natV, \ n m ->
  homV (lin n) (lin m), ...]` (sieves, interval and connections restricted
  from posets; phi-ext by maps from [0]); DCn = DB.Cn[cIp at lin n].
  SSetFill: for simplicial sets, composition in line form gives fibrancy
  (DCn.GFillFib at DB.GFam.famPath / famConn).

### Step 2b as built (2026-10-14): composition gives filling, internally

The connection is not taken as pth G -> pth (pth G): composing a square in
the type of lines would need composition for A^I with a face {i = e} that
is not a sieve on the stage.  Instead the path structure gets the
EXPONENTIAL LAW, and the filler is composed stage by stage:

* PathConn.seg, `PathConn[P]` (interface on top of PathStr): lines as
  natural families over the generalised points (f , i) : W -> X * I,
  `lev`/`lam` for contexts, `levA`/`lamA` for types (read in E), with
  lev-nat, lev-act, lev-ev (the end at e is the value at (id , e)),
  lev-lam, lev-ext (and the A versions); connections on maps into the
  interval `cI d W i j` with cI-nat, cI-jsrc, cI-jtgt, cI-isrc.
  `ConnKit`: the connection line `connL z i` (j |-> z (c (i , j))),
  `connA`, the constant lines `constG`/`constA`, each locked after its
  evaluation lemma; connL-act, connL-src (constant on {i = src}),
  constA-end.  2.1 s.
* FillLine.seg, `FillLine[P, C, G, A, d, ca]`: `Prob[W, x, p, i]`, the
  composition problem at W along connL x.1 i: start x moved to the
  connection line, side 0 on {i = src d} = the constant line, the sides of
  p connected; ts-ext (an element of the fibres is determined by its point
  and the evaluations of its line), mkTS.  3.1 s.
* FillLineFib.seg: `cE-pt` (the composite lies over x.1 (id , i)),
  `cE-src`, `cE-side`, `ProbR` (the restricted problem is the problem at
  the restricted data; with cunif: cE-eq), `Fill` (the composites at
  (f , i) form a natural family over x.1; the filler is its lamA),
  `fibAt : FibAt (src d)` from `ca : CompAt (src d) (tgt d)`.  2.9 s.
* PosetConn.seg: `posetConn : PathConn[posetPath]` (lev = action along
  (f , i), lam = value at (pX , pr2), cI from CylCat's conn via
  pair-comp / cyl-pair / pair-gen / pair-lid), and `PosetFill` (line
  composition -> FibAt for posets, no box over a cylinder).  3.1 s.
* cop-cong moved from CompLine into FibTriv.CompAtP.

Next: FibE storing CompAt.  What it takes (measured 2026-10-14):
* FibE is FibExt[a, l] and is used at l = a+ (UnivEl.ElFib), but the line
  layer (Cofib.Partials, Equiv.PMap, PathObj, FibTriv, CompLine, PathConn,
  FillLine*) is at level a only: it must first be made level-generic
  (`level a l`, PreL[a, l]), as Box/Esi are.
* ESI (insertion of an empty side does not change the composite) is stated
  for box composites; FibE needs its line form (an empty side inserted in a
  partial line), with the bridge box ESI <-> line ESI through CompLine.
* FibExt (CompExt, isProp-ESI, BoxTr, fibExt), UEnc (encodes the box cops),
  and the producers (ElFam4.ElFib, TranspPack, UBoxData, ExtSide, UnivOp,
  ...) are restated for CompAt; consumers that need box composites use
  CompLine.ToCompOp, which needs the round trip ToCompOp (ToCompAt c) = c on
  composites (box-ext).


### Step 3: plan (2026-10-14)

Type formers are proved fibrant in line form over the generic base, with
the family path object famPath (GFam), defined for every base: one proof
for posets and Delta.  (Posets: posetPath ~ famPath by PosetConn's
exponential law; the box world reaches famPath through CompLine and that
iso.)  Order:

1. GCofib.MapP: partial elements moved along a map of types over a
   substitution (sides mapped, compatibility, restriction).  PackRel's MV
   mapP to become an instance.
2. Sigma (GSig): a partial line in Sigma A B is filled by filling its A
   part (FibAt A), then its B part over the filled A line, a line in G.A
   (famPath: lines in G.A are lines in A over lines in G, by construction).
3. Pi, Path (Id), then Glue (needs forall along the interval on Delta, see
   the cofibration note), then FibE := (A, CompAt pair, line ESI), and the
   universe (posets: tininess; Delta: horns + classical box <=> horn).

### Step 3 as built (2026-10-14)

* GCofib.MapP: partial elements moved along a map of types over a
  substitution (mapS with its characterisation mapS-pv, mapP,
  mapP-restr).
* GLine.EndKit[P, G, A, e] (any path structure: endE, endE-act, tv-eq,
  lineL, lineL-act, mkTS) and GLine.LevKit[P, C, G, A, e] (with the
  exponential law: endL-lev, ts-ext, mkTS-lev, line-act, levA-ptAct): one
  home, used by CompAtP, ConnKit, FillLine, FillLineFib and GSig.
* GSig.seg (inside IvBase, so for posets AND Delta): FMap (famPath is
  functorial in substitutions), SigFib[G, A, B, e, kA, kB].fibAt :
  FibAt e of Sigma A B from FibAt e of A (over G) and of B (over G.A).
  The A part of a partial line (MapP along pA), its filler, the B part
  over the filled A line (a line in G.A), its filler, put together (jn);
  kside from kA/kB.kside, kunif (Unif) from kA.kunif + mapP-restr and
  kB.kunif + partExtH.  Pitfall met: a local alias (fa := kA.kop ...)
  against the callee's statement cost 173k unfoldings; use the callee's
  term.
* FibPiE moved inside IvBase (the poset FibPiE deleted; FibPi / EsiPi use
  BaseP.FibPiE; its use of Fib.Kit.fromE replaced by TyL.coeT / pr-coe).
* GPi.seg (inside IvBase): PiLines.ApL (a line in Pi applied to a line in
  A: a line in B over a line of G.A, natural by apW-act / apW-f /
  apW-tact / apW-gen), apW-restr; PiComp[G, A, B, eS, eT, kA, cB]: the
  line form of FibPi.  Prob[K, w, p, v]: fill A backwards from v (kA :
  FibAt eT, empty partial), apply the start and the sides along it (a B
  problem over a line of G.A), compose in B (cB : CompAt eS eT); ProbR
  (restriction = problem at the restricted data), Prob-cong, CopX (the
  composite, an element of Pi with cop-val), CS (cside: a total side, by
  cB.cside), CU (cunif, by Prob-cong + restrictP-o); piComp : CompAt eS eT.
  Pitfalls met: local aliases (wJ, fg, and the pair for Prob.xA) against
  the callees' statements (64k unfoldings): use the callee's terms.
  Remaining hot spot: famPath projections vs FC names (Qb 0.7 s, CH 1.1 s).
* GPiFib.seg (inside IvBase.Cn): Pi A B fibrant at src d from kA (A at
  tgt d) and cB (B, src d -> tgt d), by GFillFib.
* Driver: --only-top M (only the declarations directly in M); the check
  scripts run IvBase's own declarations with --only-top IvBase --only-top
  Cn and each nested file with --only (IvBase as one run was 10.01 s).
* Named mismatch, to fix next: the path structure is passed as a RECORD
  value (P : PathStr; famPath = new PathStr[...]), so famPath.pth G /
  famPath.pev G e are second names for FC[G].GI / FC[G].ev e (5-15k
  unfoldings per lemma in GPi; GPi 7.4 s).  Cure as for the base: the line
  layer as a segment over the path structure's fields, instantiated by
  module (famPath, posetPath).
* Next milestone: transfer of FibAt / CompAt between a path structure with
  the exponential law (PathConn) and famPath (lev / lam on contexts, levA /
  lamA on types, MapP on partial lines).  Posets: posetConn carries the
  box world's fibrancy (posetPath, via FibTrivFill / CompLine) to famPath
  and back, so FibSig / FibPi become instances of GSig / GPi.
* GTrans.seg (inside IvBase): ToFam[P, C, G, A, e, kP].fibAt (FibAt at
  famPath from FibAt at any P with the exponential law: a family goes to P
  by lam, partial lines along MapP, the filler read back by levA) and
  FromFam[P, C, G, A, e, kF].fibAt (the converse: lines of P to families
  by lev / levA, the filler back by lamA).  Posets (P = posetPath, C =
  posetConn): box fibrancy <-> famPath fibrancy, so the generic Sigma / Pi
  apply to the poset model.  Next: the same transfer for CompAt; then FibE
  storing CompAt with a line ESI (EsiSig / EsiPi are stated for the box
  composites of FibSig / FibPi, so retiring those needs the line ESI).
* GTrans: the maps factored into PsiMap / PhiMap (no filler parameter);
  ToFamC[P, C, G, A, e, e', cP].compAt and FromFamC[...].compAt: CompAt
  transferred in both directions (the composite moved along evE; cside by
  cS.cside + mapS-pv + endL-lev; cunif by cS.cunif + cop-cong +
  mapP-restr).

### Line ESI (2026-10-15)

* skipN moved to Arith (one home; Esi's users point there).
* CofEsi moved inside IvBase as GCofEsi (InsP, KESI, InsPH, kesiH; the
  poset CofEsi deleted, its users take BaseP.GCofEsi); added insR
  (restriction preserves insertion) and MapIns.mapIns (MapP preserves it).
* GLine.CompAtP.CESI (the line ESI of a composition: an inserted empty side
  is not seen) and FromFib.cesi (KESI of a filler gives CESI).
* GFillFib.FillLineFib.Kesi.kesi: CESI of the composition gives KESI of
  the line-MkFill filler (PI.insP: the problem of p' is that of p with an
  empty side inserted at suc k).  Lock-order mismatch met: SL.pv is locked
  after side is built, so (S'' n h).pv and SL.pv cannot be compared at a
  computed index; cured by the characterisation valS'' / levS'' (by cases
  on n) in GFill.Prob.
* ESI through the generic constructions: GTrans ToFam/FromFam.kesi and
  ToFamC/FromFamC.cesi (MapIns on the moved partials); GSig SigFib.kesi
  (KESI of A and B; the B start points agree only propositionally, so
  InsPH + kesiH); GPi PiComp.CE.cesi (CESI of B; the B problem of an
  inserted partial is an insertion, PI.insB) and GPiFib.kesi.
* Next (step 3 proper): FibE storing (A, CompAt pair, CESI pair) at
  famPath; the poset producers through CompLine + GTrans need the bridge
  box ESI <-> line CESI along CompLine (ToCompAt / ToCompOp); then FibSig /
  FibPi / EsiSig / EsiPi become instances of GSig / GPi.
* Box ESI <-> line CESI along CompLine: ToCompAt.cesi (box ESI gives line
  CESI: insB maps an insertion into a partial line to one into its box)
  and ToCompOp.esi (line CESI gives box ESI, through GLine.cesiH, the
  heterogeneous CESI).
* RETIRED: FibSig, EsiSig, FibPi, EsiPi (and Level1's Sig1 / Pi1, unused).
  PosetFormers.seg: SigC / PiC give the poset (Comp, ESIC) of Sigma and Pi
  as instances of GSig / GPi along box -> CompLine -> GTrans -> line MkFill
  -> generic former -> GTrans -> FromFib -> CompLine -> box, with ESI at
  each step.  Mismatch met: an end point named src false and tgt true
  (PiC); cured by castFib along refl.  Open: the generic layer is at the
  base level only (FibSig was also instantiated at l+ in Level1, unused).
* Level-generic line layer: GFam, GSig, GPi, GTrans, GPiFib take a level
  lv (a <= lv), like GPre / GCofib / GLine / GFill / GFillFib / GCofEsi /
  FibPiE already did; the family codes over the base (level a) at level lv
  are VLift's PiS (Ix = the function type on the nose) via GFam.piO /
  piH.  Level1 instantiates Sig1 = BaseP.GSig[l+], Pi1 = BaseP.GPi[l+],
  Fam1 = BaseP.GFam[l+] (the deleted FibSig / FibPi had l+ instances).
* GFibE.seg (inside IvBase): FibEL G = (A, (CompAt e0 e1 * CompAt e1 e0),
  CESI * CESI) at the family path object, for any base and level.
  PosetFibE.seg: toL / fromL convert the poset FibE (box composites, ESIC)
  and FibEL both ways (ToLDir: CompLine.ToCompAt + GTrans.ToFamC + cesi;
  FromLDir: GTrans.FromFamC + CompLine.ToCompOp + esi).
  Next for step 2: migrate the FibE consumers (UAct U0 X = FibE (yP X),
  UEnc, ElFam4, TranspPack, UBoxData, ExtSide, UnivOp, FibExtV, ...) to
  FibEL, with the line versions of FibExt's CompExt / isProp-ESI / BoxTr /
  fibExt (a CompAt is determined by its composites; CESI is a
  proposition), and the round trips fromL (toL F) = F on composites (box
  -> line -> box: box-ext; posetPath -> famPath -> posetPath: psi / phi);
  then FibExt / CompExt / BoxTr become instances.

!!! KERNEL CHANGE, FOR THIERRY TO DECIDE (2026-10-15): lazy delta in
!!! src/Seg.hs conv (sameDef): two applications of the SAME defined
!!! constant are first compared by their arguments, and unfolded only if
!!! that fails.  Sound (equal arguments, equal unfoldings).  The original
!!! kernel is saved as seg/Seg.hs.orig-before-lazy-delta.
!!! Why: GFibExt's base case compares A with its own eta-expansion as the
!!! source of MorC along the identity (srcTy G G (idS G) A A.tact ..),
!!! inside the partials CompAtP[.., A, ..].PT.Partial.  This is not two
!!! names for one notion (both names are forced: the identity morphism has
!!! source /= target syntactically), but the original kernel compares the
!!! partial-element types by unfolding the iterative-set codes of the line
!!! objects (mkV / IdV / elt: 3M unfoldings) instead of comparing A with
!!! its eta-expansion (cheap).  Measured (all at the 10 s cap):
!!!   original kernel: GSubst 2.4 s; GFibExt 3 OVERRUNs (MorId.cop-id,
!!!     base, core; 31.8 s); GFibLaws 3 OVERRUNs (subFibEL-id, cop-comp,
!!!     subFibEL-o; 32.1 s)
!!!   lazy delta: GSubst 2.3 s, GFibExt 1.8 s, GFibLaws 2.5 s; whole
!!!     check-model 157/157, 415 s -> 375 s over the 155 common files; the
!!!     slowest files halve (BCRel 6.1 -> 2.7, ExtEsi2 6.1 -> 2.6, PropD
!!!     5.6 -> 2.4, BoxHorn 4.9 -> 2.2), no file slower by more than 0.1 s.
!!! The name mismatch that WAS there (the type of MorC's source written
!!! three ways: tyM / mkTy literal / MorC.B) is fixed in the .seg files:
!!! one name, GSubst.srcTy, which MorC itself uses.

* (b) generic FibEL infrastructure, all inside IvBase, any base and level:
  - GLine.CompAtP: CompAt-ext (a composition is determined by its
    composites), isProp-CESI.
  - GFam.FMap (moved from GSig: one home).
  - GSubst: srcTy D G s A h hi ho (the type with objects A.tob o s and
    action h); MorC (problems for srcTy moved along s to problems for A,
    with ESI by MapIns); SubC = MorC at the action of subTy; subFibEL.
  - GFibExt: the extensionality principle fibExtL (the line version of
    FibExt.fibExt): same objects, pointwise equal actions, composites
    agreeing through MorC along the identity (MorId: it does nothing).
  - GFibLaws: subFibEL-id (agreement by refl), subFibEL-o (MorComp:
    along s' then s = along s o s').
  - GTrans.RoundC: posetPath-type -> famPath -> back has the same
    composites, for ANY path structure (lam o lev = id).
  - CompLine.bpRT: box -> partial line -> box is the identity.
  - PosetFibE.fromL-toL: fromL (toL F) = F.

* (a) Path types in line form, over any base (inside IvBase):
  - GPath.PathT: Path A a b at (X , x) = natural families u (W , f , i)
    in the total presheaf over x f, with u (id , e0) = a, u (id , e1) =
    b: the presheaf exponential by y(Iv) (NO product in the base), as
    codes; action = precomposition; path-eq / tp-ext / end0g / end1g.
  - GPathProb: the problem at (W , f , i) as a problem for A at W: the
    point p (f , i) on the line xh.1 f; the sides on {i = e0}, {i = e1}
    (pre W Iv i (ptS e)) with constant lines at a, b (PtProb: they do
    not depend on the partial); the sides of P along f, their paths
    evaluated at the path coordinate i g g'.  pt-disj for e0 / e1.
  - GPathRes: R1 (restriction in W: the composite path is natural), R2
    (restriction in X: uniformity).
  - GPathComp: Comp(A) -> Comp(Path A a b) with line ESI (cours6),
    pathFibEL : FibEL G -> PEl -> PEl -> FibEL G.
  - Poset paths are its instance: PosetFibE.pathFibE G F a b =
    fromL (pathFibEL (toL F) a b).  RETIRED: FibPath (its pointwise
    helpers pwCL / pwCylId moved to Equiv, their only user), EsiPath;
    Level1.Path1 = BaseP.GPathComp[l+].  DPath / DPathEnd (Lemma 3.1 of
    [S], eta_DA vs D eta_A) are a different statement and stay.
  - Mismatch met and cured: the boundary sides were first stated inside
    Prob[.., P, ..], so the boundary sides of two problems with the same
    point and different partials were different locked constants;
    they are now stated in PtProb (no partial), which is the mathematics.

SECOND KERNEL ISSUE -- FIXED 2026-10-15 (Thierry's go-ahead): whnf in
src/Seg.hs, resuming a stuck split or projection that reaches a LOCKED
glued constant, returned VApp f' a / VProj p' l instead of extending the
constant's spine, so conv failed against the same constant applied
directly.  The fallbacks now use app / vfst / vsnd / vproj.  The
workaround (ix0 / ix1 / ixL in GPathComp.Ins) is deleted; the boundary
equations are refl.

== QUESTION FOR THIERRY: the universe (the next step needs your decision) ==

Everything below the universe is now generic: FibEL (line composition +
line ESI at the family path object), substitution with its laws,
extensionality, Sigma, Pi and Path, over IvBase at any level; the poset
versions are instances through the bridges (toL / fromL, fromL-toL).

The universe is not a choice between two equal routes.  By cours6
("Univers et definition des types fibrants"), U X = FibEL (y X) gives a
bijection Comp(G, A) -> Elem(G, C(A)) only when X * [1] is representable
(posets: y Iv is tiny).  On Delta it fails, which is why there C(A) must
be the PROPOSITION isFib(X, A rho) (horn filling), with the classical
box <=> horn equivalence.

So the no-fork form is ONE generic universe construction, parameterised
by a fibrancy classifier C(A) over the base, with two instances:
  * posets: C = FibEL (y X)            (the bijection by tininess);
  * Delta:  C = isFib by horns          (the classical step);
and shared by both: Glue, forall along the interval on the path object
(now built, below), equivalence extension (cours6: Ext(alpha) fibrant),
smallness, El and the decoding.

The question: do you want the classifier interface (a parameter segment
over IvBase for C(A) with the comparison Comp -> Elem C), with the poset
classifier FibEL (y X) and the Delta classifier isFib by horns as its two
instances?  Nothing of the universe has been migrated (UAct / UEnc and
their consumers are unchanged and still box-based).

DECISIONS (Thierry, 2026-10-15), recorded at the universe question:
  (1) the universe is ONE construction parameterised by a classifier C(A),
      Glue / forall / Ext(alpha) shared; poset UAct/UEnc become an
      instance, the box-based FibE consumers retired.
  ORDER (coordinated with seg-62, Thierry agreed): Glue = Ext(alpha) is
      made generic in line form FIRST (plan below, "Ext(alpha) generic"),
      the universe after it.
  Universe caveats (cours6, "Definition des types fibrants" / "Univers"):
  * the classifier interface asks only for what a classifier gives:
    Elem(G, C(A)) -> FibEL A (natural), plus closure under the needed
    formers.  Posets discharge it constructively (C = FibEL (y X),
    tininess), postulate-free.
  * Delta: SUPERSEDED (Thierry, 2026-10-15) -- not a postulate and not a
    proposition: C(A) = isFib(X, A rho) is the untruncated horn filling
    operation, and FibEL comes from it with lem only (skeletal recursion to
    large boxes, then the generic open box): DeltaFibIff (canonicity-11).
    See the GUniv draft below.  The constructive half Comp -> isFib is
    BoxHorn (comp -> horn along the Gabriel-Zisman retraction
    r : X * [1] -> X), to be restated in line form over IvBase (r as a
    line in the path object, prism facts via PrismCov / DeltaNat), posets
    its instance.
  * OPEN OPTION (not built): FillBase / FillCell / FillStage / FillComp
    (Sattler Lemma 2.1, horn -> comp for DA, D the semi-simplicial lex
    operation of D.seg) might avoid the classical postulate; its chains
    P_k / Q_k are the m + 1 shuffles of [N] * [1] (one home with
    DeltaNat).  It gives comp for DA, not for A.
  * cours6's order: univalence first (Sigma X:U, X ~= A contractible, from
    Theorem 7's extension of partial equivalences), then Comp(1, U) as a
    corollary, not a direct Glue composition in U.

* forall along the interval, on the path object (for Glue / equivalence
  extension, shared by both bases):
  - IvBase: PhiL X = lines of sieves at X (natural families of sieves over
    (f , j) : W -> X * Iv: a sieve of y X * y Iv, no product in the base);
    HoldsL; constL, restrL.  Parameter segment Fa: forallL, lands-forall,
    forall-lands; derived forall-pre (stable under pullback) and
    forall-const (forall of a constant line is the sieve).
  - Constr.ForallPos[O, ob', o0, pt0]: ONE proof for decidable subsets of
    finite posets, for any family of posets with a point object: L holds
    everywhere iff it holds at (x , e0) and (x , e1) read at the point
    (computable).  Instances: posets PFa = PosB.Fa[FPo..] (O = Ob) and
    Delta DFa = DB.Fa[DFo..] (O = Nat, lin).
  - Constr.forall-allIv: for Q a sieve of the cylinder X * [1], the line
    forall of its line (lineQ: Q along (f , j)) IS allIv X Q.
  - check-model.sh runs IvBase with --only-top Fa as well.

* forall and UNIONS (checked 2026-10-15 at the coordinating session's request):
  - Fa.forallL takes ONE line (one generator).  Cofibrations are lists of
    generators (the sides of a partial), and forall does not distribute
    over unions in general.
  - Delta: GAP for Glue.  Counterexample, computed (DeltaBase probe-T*):
    over X = [1], the triangles T1 = {x <= e}, T2 = {e <= x} of the prism
    Delta[1] * Delta[1]: forall T1 = {0}, forall T2 = {1} (vertices), so
    the edge id [1] lands in neither, though its prism is T1 u T2: forall
    of the union is all of [1].  On Delta the prism is not representable
    and IS the union of its m + 1 maximal simplices (shuffles).
  - posets: NO gap.  W * [1] is an object, so the cylinder over f lands in
    a union iff its identity lands in one generator (Cofib.full-dQ); there
    the two triangles do NOT cover the square (it is representable and in
    neither).  So forall of a list = the list of foralls, and
    forall-allIv per generator is right for lists too.
  - IvBase.HoldsU (every (V , f g , j) lands in one of the lines) and the
    parameter segment FaU (forallU: a list of lines -> a list of sieves,
    with landsU-forall / forallU-lands), BOTH INSTANCES BUILT (below).
    The plan was:
      posets: the list of the per-generator foralls (full-dQ: take the
        universal simplex (W * [1] , pr1 , pr2));
      Delta: decidable: the faces S of [n] (vertex subsets) such that each
        of the m + 1 shuffles of S * [1] has its vertices in one generator;
        soundness: every simplex of S * [1] lies in a shuffle; completeness:
        f factors through the face of its image by a section.
  - check-model.sh runs IvBase with --only-top Fa --only-top FaU.

* FaU instances (2026-10-15 night):
  - IvBase.PrismCov[W, r, Vk, gk, jk, fact]: ONE lemma for both bases: if
    every simplex (V , g , j) of W * Iv factors through one of finitely
    many test simplices, "covered by a union" is decided on the tests
    (tests-holdsU / holdsU-tests).
  - posets (Constr.PFaU): one test simplex (W * [1] , pr1 , pr2), via
    pairH; forallU = the list of the per-generator foralls.
  - Delta (DeltaForall.DFaU, with DeltaNat for the arithmetic): the tests
    are the m + 1 shuffles P_k (Simp's pc / pl); Fact: (g , j) factors
    through P_k with k = max { g i | j i = 0 }, h i = g i or g i + 1.
    forallU over [X] = the faces S of [X] (numbers below 2^(X+1), enc /
    dec) with condS S (every shuffle of S * [1] has its vertices in one
    line), the face = "the image is in S".  Snd: soundness (the shuffle k
    of [m] maps into the shuffle at f k of the face); Cmp: completeness
    (S = the image of f, the test at f^-1 s, cases on i0 vs i1).
  - ForallPos.pt-read / pts-lands / lands-pts / atPt-eq: a line at (V , h ,
    j) read at the points (h v , j v) (shared).
  - PROBES (DeltaForall, by refl): the EDGE face {0 , 1} (number 3)
    satisfies condS for the list [T1 , T2] (probe-U-edge) and for neither
    [T1] nor [T2] alone (probe-U-edge-T1 / -T2): forall of the union
    contains the edge, the foralls of the triangles do not (see also
    DeltaBase.probe-T*, and probe-U-0 / -1 for the vertices).

### Ext(alpha) generic (2026-10-15, plan agreed with seg-62)

1. [done] cofibrations over a context in GCofib (one home with the
   partials): Cof[G] (cr generators cQ X rho l : Phi X, natural), CofL
   (full = anyF of allS at the identity: id lands in a union of sieves of
   y X iff in one generator, so right on Delta too; resCtx, inclR, res-eq,
   full-of-id) and full-same (presentation invariance: two lists with the
   same sieve at the identity have the same full).  anyF / fin-eq / finTop
   / finWk / bool-ext moved to Arith; IsTV and mkVevA / mkV-ev / mkV-f
   moved to V (W.IsTV, W.mkV-f).  Measured pitfall: importing VCode before
   IvBase (to reach mkV-f) slowed the whole line layer by a constant
   factor (GPi 4.8 -> 5.9 s, GTrans +1 s) with IDENTICAL unfold counts and
   GC time (MUT time only): a kernel cost of the position of a module in
   All.seg, not a mismatch in the mathematics; cured by moving the three
   lemmas instead of the module.  Poset Cofib keeps lands-pw and CofD (dQ: the
   forall along the cylinder, used by the box Theorem 7 only); users write
   GP.Cof / GP.CofL (+ CofD where dQ is used).  check-model 162/162.
2. [done] GEquiv (inside IvBase): HFib[D, B, A, al].FibT, the homotopy fibre
   of al over E_A, = Sigma (PresheafFormers.SigAB) of b in B(x) and a path
   in A over x from al (x , b) to (x , a), the path type being
   GPath.PathE, now general: G a context, A over H, sx : G -> H on points
   (no naturality needed), lines in E_A over sx (y f), ends aE / bE in E.
   Path A a b is the instance (H = G, sx = id, PathEnds); the fibre is the
   instance G = EAB (the points (x , a , b)), H = D.  Accessors read in E:
   fibB, fibL (+ -pt, -nat, -0, -1, -act), mkFib, fibE-eq (locked).
   EquivOp = GCofib ContrOp of its partials.
   GCofib.ContrRet: a ContrOp moves along a retraction of types over the
   same context (move partials by s, extend, read back by r; r s = id).
   PosetEquiv.FibIso (the bridge, by tininess in ONE place: PosetLevA's
   levAP / lamAP): r (box fibre -> generic: the line of p is levAP X p),
   s (generic -> box: the path is the line at the generic point
   (pr1 , pr2), via Equiv.mkFibE), rs, sr; toGen / fromGen move EquivOp
   both ways.  2.4 s.
3. [done] GExt, GExt2, GExt3, GExt4 (inside IvBase; were Ext .. Ext4): the
   type Ext(alpha), its action, the total presheaf EX, ext(alpha) / glue /
   ext-det.  They only used Hom / Lands / full and the generic line layer,
   so they MOVED (no bridge, no copy): GP = GCofib[a], PR = GPre[a]; poset
   users write BaseP.GExt .. BaseP.GExt4.  Faster than before (Ext 2.8 ->
   2.3 s).  Needed for it: Fib.Kit's fromE / fromE-eq moved to GPre.TyL
   (one home; users write FibM.PR.TyL[..].fromE, or the aliases KGE / KBE
   next to the Kit aliases KG / KB that other files reach), and VCode
   imported before IvBase (its codes are used by GExt), at the measured
   constant cost of the kernel's lock LIST (below).
   KERNEL QUESTION queued for Thierry (seg-62 relayed, NOT applied):
   src/Seg.hs:464 whnf tests i `notElem` s on the lock list s :: [Id]
   (Id = String) at every unfolding, so every `opaque` earlier in All.seg
   slows every later check (VCode's ~60 opaques before IvBase: GPi 4.8 ->
   5.9 s, same unfold counts and GC, MUT only).  Fix: a Data.Set Id.
   CODE FORMERS, two homes (for Thierry to decide): VCode's opaque PiO /
   SigO / IdO / PiO3 / lam3 / app3 (level a, codes over V[a]) and GFam's
   piO / piH (VLift.PiS: index sets of level a, codes at any level lv,
   used by GFam's lines and GPath).  Recommended single home: GFam's
   piO / piH (level-generic, which the generic layer and the universe at
   lv+ need), with opaque wrappers where comparison by name matters.
   Migration cost measured by use: among the generic files only GExt uses
   VCode's formers (36 sites, the pairs code: PiO3 / IdO / lam3 / app3 /
   PiO3-ext / -prop); the other users of VCode are the box Ext files
   (ExtComp*, ExtEquiv*), retired at step 6.  After that VCode could go
   back after IvBase (or disappear).
4. [done] GExtEquiv, GExtEquiv2, GExtEquiv3 (inside IvBase): ext(alpha) is
   an equivalence, extEquiv : GEquiv.EquivOp G ExtT A extMap, from
   kA : FibAt e1 of A (family path object) and eal : EquivOp of alpha.
   Part 1 = ExtEquiv's toFA / fromFA / Tr / kE on the generic fibres
   (lines read in E; toFA's line is the line of v made A'-valued by
   full-act).  Part 2: theta (kE at the full maps), the base point x0 =
   (constant line at rho, w at e1) (GFam.FC.constF, new), ONE partial line
   in A made of two families of sides (GCofib.Partials.Join, new: sides
   S1 l on Q_l = the lines of p, S2 k on the generators cQ X rho k = the
   lines of theta; c11 / c12 / c22, theta's agreement on two generators
   stated once, c22 = th-cong), filled by kA; a0 its value at e0, u the
   pair, v0 = (glue (a0 , u) , filler) with point w on the nose.  Part 3:
   kside (ext-det + the sides of the filler), kunif (x0eq, the restricted
   joined partial = the joined partial of the restriction (ppR, by cases
   on the two families), kA.kunif + kop-cong).  At a constant line no
   forall is needed.  2.6 / 3.8 / 3.4 s; ExtKit (606 lines, boxes over the
   cylinder from families of paths) is not used.
   Also moved for it: Plus (Constr) and the two-list Fin helpers splitF /
   finL / finR / splitL / splitR (ExtKit) to Arith (one home).
5. [core done] Theorem 7's composition in line form, any base:
   extCompAt : CompAtP[famPath, G, Ext(alpha), eS, eT].CompAt, from kAS
   (FibAt eS of A), kBS (FibAt eS of B over G|psi), kA1 (FibAt e1 of A)
   and eal (EquivOp of alpha).
   - GMapLine (inside IvBase): MapLine (partial lines moved along a map of
     types, any path structure with the exponential law) and LineSide (a
     side from a natural family of lines over the problem point; also used
     by GExtEquiv2, whose local SideOf is gone).
   - GExtComp1: beta (a problem of Ext over a FULL line is a problem of B
     over G|psi), the B-filler FBv, FB-side / FB-start, its uniformity BR,
     FBv-cong.  3.0 s.
   - GExtComp2 (inside IvBase.FaU): delta = forallU of the WHOLE list of
     psi's generator lines along the problem line; along f in delta the
     line is full (flAt) and beta gives B-fillers; the unglued problem
     (MapLine along ext); ONE joined partial line in A (sides of the
     unglued p + alpha of the B-fillers on delta), filled by kAS: F-S1
     (ext of the sides), F-S2 (alpha of the B-filler), FA-start.  3.3 s.
   - GExtComp3: w1 = the A-filler at eT; the partial fibre element over w1
     (constant paths; on Q_l the ends at eT of the sides, on delta the
     tops of the B-fillers read in Ext), extended by step 4's extEquiv;
     the composite is its B-part; cside.  4.2 s.
   - GExtComp4: uniformity (delta restricts by forallU-pre + phiL-ext; the
     B-fillers by FBv-cong; the A-filler and the fibre extension by kunif +
     kop-cong) and extCompAt.  3.5 s.
   FaU's list length is now forallUn k, independent of X (posets k,
   Delta 1), so the restricted partials compare index by index without
   transport; IvBase has isSet-Phi (local Hedberg from phi-ext).
   KERNEL BUG (reported, not fixed): with the lemma phiL-ext in IvBase's
   own body AND any unit imported after GExtComp3 inside FaU, checking
   GExtComp3 fails with "INTERNAL ERROR ... unbound variable: Ob" (every
   use of GExt3's fromB); either removal makes it pass (a later unit
   changes an earlier module's check).  Repro files kept in the session
   scratchpad (repro/).  FIXED by seg-62 with Thierry's OK (SegParse names
   `open M[args]` instances open#<o>@<module path>); phiL-ext is back in
   IvBase.
   - GExtComp5: extComp-full (Full.full): on a line full everywhere, the
     composite is the top of the B-filler read in Ext (the identity lands in
     delta, the extension is that side: kfull).  2.5 s.  GCofib gained
     restrictP-id.
   - GExtComp6: extCesi : CESI extCompAt, from the KESI of kA, kB, kA1
     and eal: beta's fillers ignore an inserted empty side (BI, kB's
     KESI), the unglued partial is an insertion (MapIns), so the joined A
     line is one (GCofEsi.joinIns) and w1 does not change (kA's KESI); the
     partial fibre element over w1 is an insertion, so the extension does
     not change (GExtEquiv4: KESI of extEquiv from those of eal and kA1).
     3.3 s.
   - GCofEsi gained JoinIns / joinIns (an empty side inserted into the
     first family of a joined partial is inserted into the join; first
     family of any length r1' = suc r1) and InsSides (an insertion read
     side by side); Arith gained the index lemma (SR, split-skip, split-k,
     moved from EsiSplit) and leb-plus.
   So Theorem 7 is complete in line form over any base: extCompAt,
   extCesi, extComp-full, extEquiv, extEquiv-kesi.
   - Ext(alpha) as a FibEL: GExtFib (inside IvBase.FaU: Theorem 7 both
     ways from fillers of A and B at both ends with their KESI), GFibFill
     (inside IvBase.Cn: a FibEL's compositions give those fillers by line
     MkFill), and the instances PosetExt.PExt / DeltaExt.DExt (a few lines
     each: their Cn instance's GFibFill + their FaU instance's GExtFib).
     So Glue = Ext(alpha) is fibrant for posets AND simplicial sets by ONE
     proof.  (Segment-typed parameters (cn : Cn) cannot reach the files
     nested in a segment, hence the per-instance combination.)
   CSieve.seg (before IvBase): canonical decidable sieves over a small
   category (one home); Delta's Phi is now its instance (DeltaBase.DS).
   NEXT (agreed with seg-62): step 6 = the univalence operation on the
   generic layer (ExtSide / ExtRel* reason about the box Theorem 7's
   internals, feeding UnivOp's box UData), so it goes with the universe;
   then the one-sieve redesign (Cof = one sieve, FaU/HoldsU removed,
   posets onto CSieve with subS as the only bridge from Subset).
6. Poset ExtThm7 as an instance via toL / fromL; retire the box Ext files.

### Delta: horn filling and box filling (2026-10-15, canonicity-11)
RULING (Thierry): Delta fibrancy is a STRUCTURE. isFib G A (DeltaHorn.DH) is a horn filling operation, untruncated and with no uniformity; C(A)(X, rho) = isFib(X, A rho) is a presheaf by precomposition, so Elem(G, C(A)) <-> isFib(G, A). Classical logic = ONE segment, Classical (lem only), used only at horn => box (DeltaHornBox): lem decides degeneracy and membership in the Eilenberg-Zilber / skeletal recursion, each new non-degenerate simplex is filled by the given operation, and the generic open box gives uniformity. AC would be needed only to obtain the operation from the truncated property, which the model never uses.
* box => horn, constructive, any base: IvBase.GHornRetr (a CompAt extends a partial element along a retraction line r with R1-R3). Delta instance: DeltaRetr (BoxHorn's retractions read on (f, i) via pairH): BoxToHorn.isFib-of-comp.
* DONE: the poset BoxHorn is an instance of GHornRetr (sides = the faces QH m k y; box Comp -> CompLine.ToCompAt -> GTrans.ToFamC -> RF; one home for the retractions, BoxHorn.DRet, used by DeltaRetr at W = lin V). BoxHorn / CompDA moved after PosetConn in All.seg.
* horn => box, DONE (canonicity-11): 4a constructive FACE-uniform fillers (DGlue .. DFill: the prism filled by the shuffle chains P_k, one horn filling each, both directions; the faces' fillers glued on the boundary); 4b NORMALISED fillers by the first elementary degeneracy (DNormA .. DNormE, DSimpId, DFactor): Eilenberg-Zilber done by recursion, uniform along every map; lem used ONLY in DeltaHornBox.decDeg (deciding b = s_i^* d_i^* b, a proposition via ProbRel, so "Prob is a set" is not needed); line ESI by the one-side normalisation (DOneSide, constructive: on Delta a partial element is one side on the union sieve); DeltaFibIff.FI.hornToFib : isFib A -> FibEL, fibToHorn : FibEL -> isFib (constructive). This is goal (5); the Delta classifier can use isFib.
* Slowness, FIXED (2026-10-15): the cost was NOT Nat-vs-Ob (retyping the binders to Ob changed nothing, measured). It was calc chains over 4-deep resP / act terms at concrete indices (suc (suc N')). Cure: state the fact once at abstract data and lock it: DNormD.sqE (commuting square of restrictions; coreG = one sqE), DNormA.dsd (degTwo's case split at an abstract problem), DNormC.fpz (filler along a degeneracy then a face). DNormD 5.9 -> 4.7 s, DNormA 4.5 -> 3.8 s, DNormC 4.4 -> 3.8 s.
* Univalence interface (2026-10-15): GHornRetrSub.RFS.fill-sub (extension along a retraction line commutes with substitution, any base); DElHorn.elFib (El of DU has horn filling); DFibToHornSub.toCl / toCl-sub (strict Id in Sigma A'. ClD D A', any s); Classical.Cl.DeltaElFib.elFibEL (FibEL DU.UCtx, first component EGen). hornToFib is NOT natural in general (normalisation by first degeneracy is not preserved when s identifies points), so the generic univalence step never uses it.
* Glue classifier (2026-10-15, Thierry's case split): DGlueCl.GC.clExt : ClD G ExtT, at a horn problem at rho: full rho -> B's own horn op hB (data read by toB, filler by fromB; Full.res locked, res-E), else toCl of Ext's composition; clExt-full / clExt-nfull. DGlueCl.TrT / ClT: a classifier along an equation of types, pointwise <-> Sigma (PTy is a set). DGlueClSub.GS.clExt-sub: (Ext[s], clSub s clExt) = (Ext(alpha[s]), clExt') strict, for any s, under FS (Ext's FibEL under s, supplied by canonicity-96's B5); by cases on full (fullS), PhiB/toBeq on psi, toCl-sub off psi. Constructive. DGlueClSub 6 s (Phi lemmas trPhi / toBPhi in GExtSub6.ActS); the remaining cost is Ext's fibre code (extOb by cases) unfolded when elements are compared; cure = lock extOb after GExt4 (canonicity-96, planned after B5).
* G6 DONE (2026-10-15, canonicity-11): transport along a fibrant line is an equivalence, line form, any base, constructive.  GPath / GPathProb / GPathRes / GPathComp generalised IN PLACE to paths over a line (PathOverE / -Prob / -Res / -Comp: values over s y (f , i), ends at src dd / tgt dd; PathE and PathComp are the instances, names unchanged; GPath.disjD).  GTE1..GTE16 inside IvBase.Cn: tr = end of the transport filler (GTE1); omega = filler of the paths over the line along the fibre element's line (GTE2-4); B part = filler at tgt d of omega-sides (GTE5); path part = composite along the line of the transposed squares in paths between moving ends (GTE6-9); extension, kside, kunif, KESI (GTE10-15); GTE16.TrU: the data built once over pth G (ln = id), dat D ln = eqDSub along ln, trNat = eqD-o.  Lesson: a long inline transH chain whose intermediate types are inferred (GTE10.pe) overran 10 s; the same chain as separate typed lemmas checks in 0.1 s.

* Delta instance of univalence (2026-10-15, canonicity-11): Classical.Cl.DUaOp.ua = DFaU.GUaOp9.UaOp at DeltaClassifier.DU.  tautCl (DTautCl: a horn of El along a code map is moved to El at the code, filled by DElHorn.elFib, read back; tautCl-fill, then locked; tautCl-sub by FExt.isFibExt), tautCl-yon (DTautYon, along elYon by ClT.toSig), glueCl = DGlueCl.GC.clExt (locked after clExt-full / -nfull), glueCl-sub = DGlueClSub (any (psi', fullS)), clFullOp = DClFull.CF.clFull (over a full psi the glue classifier is clSub sec hB, for ANY (c , e): true on Delta by the case split, false on posets), kU* = DCn.GFibFill at elFibEL.  Never through fibToHorn o hornToFib.
* MILESTONE (2026-10-15 night): THE SIMPLICIAL UNIVERSE IS FIBRANT.  DFibU.fibU (G) : FibEL G, in any context: Comp(1, U) from ua (GCompU5.FibU, canonicity-96's G7) with its ESI from DFibU.uaKesi (U6).  Full check 318/318, lem only in DeltaHornBox.  U6 = the KESI of ua = invariance of the univalence operation under an inserted EMPTY side, i.e. under re-presenting psi_p with one empty generator inserted.  Done with no copies:
  - ExtSub (GExtSub2-6, GExtNat1.ExtMove, glueCl-sub) takes (psi', fullS); GQ form = GExtSub2.PQ / HQ.
  - GCofIns.InsC (+ fullS-ins, hg-ins): psi' = psi along s with one empty generator inserted.
  - IvBase.GensIns (the same list, or one empty generator inserted) and FaU.forallU-ins (Delta: the same sieve, DeltaForall.FIns; posets: an inserted generator, Fa.forall-empty).
  - equivalence half (canonicity-11): GExtNat3/4/4J/5/8 at (psi', fullS) with Hg : GensIns; the moved joined A line (GExtNat4J) by cases: joinEq2 + kop-cong, or GCofEsi2.joinIns2 + kA's KESI.
  - fibration half (canonicity-96): GExtNat2/6/7/10 with Hd, N10I.FS-ins.
  - GUaOp6.OutNatG and GUaOp8.K8G take FS / EQ / KP as inputs (OutNat, K8: the p|h instances); GUaOp10.UaK.uaKesi = K8G at q = p'|id (insR, InsC by pre-empty / pre-comp, KP by an index decomposition and pcs), with kunif of p' at id, then act-id and pr-inj.
  Posets: PUaOp.uaKesi, PCompU.fibU (canonicity-96).

### GUniv: the universe over a fibrancy classifier (DESIGN DRAFT, no code yet)

Order of construction still to be ruled by Thierry (universe before or
after the one-sieve redesign).  The cofibration psi of a Glue enters ONLY
through CofL.full / Lands, never through a generator index.

Interface (a parameter segment inside IvBase, after Cn / FaU; levels: types
of level a, universe at a+):

  Cl (G : PCtx) (A : PTy[G]) : U a+                 the classifier C(A)
  clSub (D G) (s : PSub[D, G]) (A) (c : Cl G A) : Cl D (subTy D G A s)
  clSub-id  : (A , c) = (A[id] , clSub id c)          in  Sigma A. Cl G A
  clSub-o   : (A[s s'] , clSub (s s') c) = (A[s][s'] , clSub s' (clSub s c))
  encCl (X) (A : PTy[yX]) : Enc (Cl (yX) A)          the code one level up
  toFib  : an element of C(A) over every stage gives the fibrancy the model
           uses for El (see the question below).

Derived once, for both bases: U0 X = Sigma (A : PTy[yX]) Cl (yX) A, its
action uActS / uAct and the laws uAct-id / uAct-o (from clSub-id / -o and
y(id) = id, y(f g) = y f y g: GYon), codeU X (encTy + encCl), the presheaf
UCtx and the type UTy, the generic family EGen (fibre at the identity:
fib0, tactG, tidG, toG), El = EGen along a code (ElTy).  Shared formers
on codes: Pi, Sigma, Path (GPi / GSig / GPathComp), Glue = Ext(alpha)
(GExtFib, both bases), forall along lines (Fa).

Instances:
(1) POSETS: Cl G A = FibEL structure (compositions both ways with line
    ESI); clSub = GSubst.subFibEL, laws = GFibLaws, encCl = the encoding of
    line composites (CompAt-ext: a composition is determined by its
    composites; CESI is a proposition).  El is fibrant by TININESS
    (y X * y Iv = y (X * Iv)): constructive, a structure.  The poset UAct /
    UEnc / UnivCtx / EGenComp* / ElFam* become this instance (box FibE
    retired with the box Ext chain).
(2) DELTA (Thierry, 2026-10-15): fibrancy is a STRUCTURE, as on posets.
    Cl (yX) A = isFib(X, A rho), the untruncated horn filling OPERATION (a
    Sigma: a filler for every horn, not required to be uniform).  From it,
    with lem only (no AC), the skeletal / Eilenberg-Zilber recursion gives a
    large box filling operation, and the generic open box (survey-slides
    6-8) gives the uniform FibEL: the classifier gives FibEL through
    DeltaFibIff.  Built by canonicity-11: DeltaHorn, GHornRetr, DeltaRetr,
    Classical (= lem), DeltaHornBox, DeltaFibIff.  The converse FibEL ->
    isFib is BoxHorn in line form.

Univalence before Comp(1, U) (cours6): for A : U, Sigma (X : U) X ~= A is
contractible, from Theorem 7's extension of partial equivalences
(extEquiv / GExtFib: a partial equivalence with codomain A extends to a
total one); then X = A -> X ~= A gives a composition structure on U as a
corollary, not a direct Glue composition in U.

### Strictness = equality of codes (Thierry, 2026-10-15, "important")

U0 is a presheaf of SETS of codes: an element of U0 X is a code in V
(iterative sets), and V's equality is extensional (ZF-like).  The
metatheory is univalent, but two isomorphic types with different codes are
DIFFERENT elements of U0.  So every uniformity equation of the universe
(kunif of univalence, Ext(alpha)[s] = Ext(alpha[s]), the composites, the
equivalence, toCl-sub / fibToHorn-sub) is an Id in V / U0: never an iso of
decoded types, never a relation (no return to UnivOp's URel).  Where two
fibres agree, they agree as codes (e.g. El along a code map vs the type:
A.tob Z (g o id) = A.tob Z g by ap of comp-idr, an equality of PTy).

Univalence plan (canonicity-96, approved): Partials[UCtx, UaT].ContrOp with
UaT X F = (B : U0 X) * PMap[yX, B.1, F.1] * (EquivOp + KESI); fibrancy of A
and B always as elFibEL pulled back along their code maps (natural by
subFibEL-o); the classifier only through toCl + toCl-sub (Delta's
hornToFib is not natural: it picks the first degeneracy).

### GUniv built (2026-10-15, universe first: user's go-ahead)

- GYon (inside IvBase): y X, y f, yH-idH, yH-compH, over any base; the
  poset Yon.seg is gone (its users open BaseP.GYon).
- GUniv (inside IvBase): `module Univ { Cl ; clSub ; clSub-id ; clSub-o ;
  encCl ; ... }` with U0, uActS / uAct, uAct-id / uAct-o, the type code
  (EncTy) and codeU, UCtx, UTy, smallC, fib0, tactG / tidG / toG and EGen,
  derived once (from the generic parts of UAct / UEnc / UnivCtx).  Encode
  is imported before IvBase (no opaques: no lock-list cost).  2.2 s.
- The poset universe is its INSTANCE: UnivCtx.PU = BaseP.GUniv.Univ[UAct.
  ClB, clSubB, clSub-idB, clSub-oB, UEnc.EncCl.encClB].  UAct now holds the
  box classifier (box compositions with ESI) with its two laws for ANY
  contexts (UIdB / UOB generalise the old UId / UO); UEnc holds its code
  (a box classifier is determined by its two composites).  Users open
  UnivCtx[a].PU; all of them (EGenComp*, EGenEsi, UnivEl, ElFam*, UnivOp,
  ExtSide, UBoxData, TranspUData, BCRel, ExtRel*) check unchanged.
- NEXT: the poset classifier switches from box compositions to FibEL
  (line compositions; El fibrant by tininess, line form of EGenComp*),
  then the univalence operation on FibEL from extEquiv / GExtFib
  (retiring UnivOp / ExtSide / ExtRel* / UBoxData / Transp* / BC* and the
  box Ext chain), univalence first and Comp(1, U) as its corollary.

### El of the line-classifier universe is fibrant (2026-10-15)

- IvBase.GUnivL: the universe U_L at the LINE classifier, ClL G A =
  (c : FE.Comp) * ESIC c, clSubL = subFibEL, laws subFibEL-id/-o, code
  encClL derived with no new IvBase field (a sieve is coded by its
  characteristic map W f |-> allS W (pre W X f Q)).  U_L is the POSET
  universe: El is fibrant only where X * [1] is representable.  Delta's
  universe is GUniv at the horn classifier (canonicity-11: DeltaClassifier,
  toFib through DeltaFibIff).
- GSubst.MorC split: MorP (moving problems, no composition) + MorC.
- Generic (inside IvBase, level-polymorphic):
  GLocal   the generalised points P X = y X * y Iv; a line l is the map
           s_l : P X -> G, s_l (f , i) = l f i on the nose; problems over
           G at a point over the image of a line d are PULLED BACK (Pull,
           PP: points, sides, partial elements, inserted empty sides);
  GLocal2  pulling back commutes with restriction (tvP-shift, part-shift);
  GLocal3  LocComp: A over G has a line composition (with ESI) once each
           pullback A[s_l] over P X has one, coherently in l (coh);
  GTransfer  composition along a context map with a FIBREWISE ISOMORPHISM,
           across levels k <= l (MorC is the case ph = id, one level);
  GProbEq  two problems agreeing pointwise have the same composite.
- Poset instance: PElL (ElP: El[s_l] is F along the pairing P X = y(X*Iv),
  F = l pr1 pr2, up to the fibrewise identification Pv; PhN = the action
  of El is F's; the local compositions cl), PElL2 (coh: F_Y = F_X along
  h * Iv, J on that path, MorC, ProbEq + VAL by cyl-pair; fibEGen :
  FibEL UCtx, El fibrant both ways with ESI).  All files < 5 s.
- NEXT: univalence for U_L (Sigma (X : U) X ~ A contractible, from
  extEquiv / GExtFib), Comp(1, U_L) as its corollary; then move the
  poset users from UnivCtx.PU (box classifier) to U_L and retire the box
  universe chain (UAct, UEnc, EGenComp*, EGenEsi, UnivEl, ElFam*, UnivOp,
  ExtSide, ExtRel*, UBoxData, Transp*, BC*).

### Univalence, generic (2026-10-15, canonicity-96 + canonicity-11; DONE for both bases)

MILESTONE (full check 318/318, slowest file 6.8 s): univalence, Comp(1, U)
and the KESI of ua are proved generically; the simplicial universe is
fibrant (DFibU.fibU) and the poset one too (PCompU.fibU).  Deferred, for
Thierry: one sieve per cofibration, levels, V-codes, the resolver fix.


Built, inside IvBase, every file under 10 s with --only:
- G1 equivalence data along a substitution: GEquivSub (SubMap), GEquivSub2
  (FibIso: HFib(al[s]) ~ HFib(al)[ls]; EqSub.eqSub, kopL/kopB read the
  moved extension), GEquivSub3 (EqSubEsi).  Moved to their one home:
  GCofib (SubE, ContrSub, contr-ext), GCofEsi (isProp-KESI, RetEsi, SubEsi).
- G2 laws and the univalence type: GEqExt (EqDat: moves along a path of
  triples, ext, ext-inv), GEqLaws (TyEqPw, triExt, triExtPw, eqD-id),
  GEqLaws2 (eqD-o), GUnivEq (UaU[classifier].UaTy over UCtx; codes; q4-id
  / q4-o; strict laws).
- G3a-d gluing along a classifying map kap : D -> Q4: GTransfer now has
  three levels (moves compositions down too); GElC (El along a code map,
  fibrancy from El's structure (cE , eE) moved down; elSub / elCnat /
  ElCong / Yon.elYon, Ids of codes); GYonCon; GUaGlue1 (glued B, A, al);
  GUaGlue1b (GSub / GCong / GYonQ: the glued triple is natural, Yoneda);
  GYonEq1-3 (equivalence structures glue along Yoneda maps from local ones
  with an Id-coherence: pointwise coherence derived once via ext-inv,
  lamPhi, lam-inj); GUaGlue2 (the glued equivalence structure + KESI).
- Why not the universal form (glue once over UaCtx, pull back along kap):
  UaCtx is a level-a+ presheaf; the local data of a point are level-a
  structures on the code's own types, identified with the universal
  triple only by Yoneda (codes equal propositionally), so the coherence is
  not definitional there either, and the pull-back would need two-level
  SubE / ContrSub / FibIso / EqSub plus a cross-level ContrOp transfer.
  Over D the coherence is a 3-step Id (transport along T_x, kapnat, back).

- (A) Ext in local-data form: GExt.LD / LocCode (codes as functions of
  the local data at rho); GExtSub1-6 (along s: ldEq, extObEq, Phi, PhiNat,
  tyEq : Ext(alpha[s]) = Ext(alpha)[s]; trPhi / toBPhi / toBPhi0).
- (B) Theorem 7 along s, one locked congruence per step, psi only through
  full / Lands (delta of alpha[s] = delta of the moved problem by ap of
  forallU on the generator lines, as GExtComp4 does for restriction):
  B0 GTransfer.TrF (fillers moved down a code map), GTransferComp (TrF
  along a composite = moved TrF; GElC.ElF / ElF.FSub: El's fillers and
  their naturality); B1 GExtNat1 (FBv-S; ExtMove: extPhi, alPhi);
  B2-B3 GExtNat2 (dlEq, fbS, FAv-S); B4 GFibMove (fibres along a square)
  + GExtNat3-5 (thS, FvS, uS, glueS, v0S, extEqS); B5 GExtNat6 (vEeq,
  copS, compS: extCompAt(alpha[s]) = GTransfer.Tr of extCompAt(alpha)),
  GTransferSub (Tr along the transport of Q : B = B[s] is SubC, by J;
  fibEq), GExtNat7.N7.Sb.FS : extFib(alpha[s]) = subFibEL s extFib(alpha),
  under HA0 / HA1 / HB0 / HB1 / Heal (the given structures on the
  substituted data are the moved ones).  Every file under 6.5 s.

- (C) poset ElYonCl: PElYon.EY[Z, F].elYonCl : Id (FibEL (y Z)) (El along
  the Yoneda code of F, with EGen's structure moved down) F.  El's
  composite there is, by construction, F's composite of the problem moved
  along x^ o pair o diagonal (GLocal3 / PElL / selEq); GProbEq.cop-eq
  compares it with the problem read in F (Hl: x^ o pair = x by the line's
  naturality; He / Hv: values through cVpair / cVback / sideVal); then
  GTransferSub.TrId.trId along elYon.  PElYon 6.2 s.

- GUaOp (in progress, posets first; generic over the classifier with
  parameters tautCl (El's tautological classifier along a code map) and
  glueCl (by cases on psi), never toCl of a given classifier):
  GUaOp1 (psi_p, D, kap_p, Glue2), GUaOp2 (A_X = El at F's Yoneda code,
  alpha, El's fillers, extFib), GUaOp3 (kop = (Ext , glueCl (tautCl B_g)
  extFib) , ext and extEquiv along elYon), GUaOp4/5 (kfull: at a problem
  with a side containing id, kop is that side; data by GExtFull.eqFull,
  GYonEq4.yonL, Tx.Wx; codes by tautCl-sub / tcong / tautCl-yon; one
  per-problem fact clFull left to the instance).  Tools: GExtFull (Ext over
  a full psi), GExtNat8 (eqNat: extEquiv natural as data), GExtNat9/10
  (canonical structures of alpha[s]: FS and eqNat unconditionally),
  GYonEq5 (YonDet: structures determined along Yoneda maps), GUaGlue3
  (glueSub: gluing natural with its structure), GTransfer.kmove/unique,
  GTransferComp.TrCComp.  kside = kunif + kfull; kunif = naturality of the
  output in its input record + (record of p|h) = (record of p)[y h].
- DONE (generic): GUaOp9.UaOp[...].ua : Partials[UCtx, UaTy].ContrOp.
  kunif (GUaOp8): GUaOp6.OutNat (Out natural along y h, at p|h's own
  cofibration via ExtSub's GQ = pre-comp) + GUaOp7.OutCong with the A group
  by GElC.ElF.PB (pulled-back El fillers are El's) and the B group by comb3
  of data (GExtNat9.dS, QA move, GUaGlue3.glueSub, glueCong), fillers (PB)
  and classifier (tautCl-sub, TCg.tcong); kside = kunif then kfull.
  Instance obligations: tautCl, tautCl-sub, tautCl-yon, glueCl, glueCl-sub
  (fed with FS), clFullOp.
- DONE (generic at the line classifier, + poset instance): FaU.GUaOpL.UaL
  [cE, eE, kU0, kU1, kU0e, kU1e, HU0, HU1, yon].ua, any base, Cl = ClL:
  tautCl = El's fib (GElC.ElC.Fam.fib), glueCl (c , e) = (c , e),
  glueCl-sub = symH FS, tautCl-sub = GElC.ElF.FibSub.elFibSub (trSub along
  elSub + TrCComp + the proof arguments of Tr are propositions, TrP),
  clFullOp = GExtFullC.ExtFullC.Full.extFull (over a full psi Ext's
  composite is the top of the B-filler (C5.full), whose end is B's
  composite: HU0/HU1 through GTransferEnd.trEnd and GElC.ElF.Fam.End; then
  TrSub.trSub along tyFull).  HU = "the composition read off the end of
  kU is cE": for fillers made from cE by connections this is
  GFillFib.EndC.endCa, which needs the connection unit law cI-itgt
  (cI tgt j = j; added to Cn, PCnB and DCn) and the ESI of cE (the problem
  at i = tgt d is the given one with an empty side inserted first).
  Poset: PUaOp.ua (fillers PCnB.GFillFib from PElL2.fibEGen, yon =
  PElYon.elYonCl).  Delta: canonicity-11's DUaOp (glueCl by cases on psi,
  clFullOp generic in (c , e) there).
- extOb is locked after GExt4 (opaque GExt2.ExtB2.extOb; interface
  extOb-B / -P / -sub of GExt3).  Not the cost of GExtNat4 / DGlueClSub:
  GExtNat4's 2.3 s are s1Lev/s1Eq/s2Eq, type-level unfolds (V.Ix, extP,
  CofL.resCtx, ExtDef.G') of types over resCtx along sR.
- DONE G7 (Comp(1, U) from univalence, generic, IvBase.Cn): GCompU1..5.
  A line of codes l at W (a point of PU = pth UCtx, level a+) gives El at
  its ends over y W (level a) and the transport data: GTE16.TrU's
  universal data on EGen over PU, moved DOWN a level along the codes of l
  (GTransferEq: TrMap / TrEq / trKesi, the equivalence analogue of
  GTransfer.TrF; fibre maps the identity).  Natural in W (GCompU2.natDat):
  GTransferEqSub.eqNat (EqSub of a moved structure = moved along sg o s)
  + GTransferEqCong (two moved structures along a path of triples whose
  Psi / PsiB commute with the fibre maps are equal as data, the GExtNat8
  pattern).  Moved to the codes by ElCong + elYon and presented as
  UaU.R (classifiers moved back, GCompU3; rEq by comb), these are the
  sides of p' (GCompU4); cop = code of ua.kop at p', cside / cunif from
  ua.kside / kunif (GCompU5.CU); ESI from the KESI of ua (U6, a function
  argument of CU.cesi); FibU.fibU : FibEL (UTy G).  Poset: PCompU (the
  compositions now; fibU once U6 lands).  The level crossing is why
  GTransferEq exists: the only base whose points are lines of codes is
  UCtx (level a+), the data UaT0 wants is level a (flagged by seg-62).
- DONE U6 (KESI of ua), = invariance of the univalence operation under
  inserting ONE EMPTY generator into the cofibration (canonicity-11 +
  canonicity-96): ExtSub over (psi', fullS) (GExtSub2.PQ is the GQ form),
  GCofIns.InsC / fullS-ins, FaU field forallU-ins (GensIns: delta equal, or
  one empty delta side inserted).  The GExtNat chain is presentation-free
  at (psi', fullS); its only generator-indexed steps (the A-filler's joined
  sides, GExtNat4; delta, GExtNat2 / GExtNat6) take the generator
  correspondence as a hypothesis (FJ; Hd : GensIns), with both sources side
  by side (GQ: NQ / FJQ; insertion: NI / FJI), proved by GCofEsi2.joinEq2
  (inl) or joinIns2 + kesiH (inr).  GExtNat10.N10I.FS-ins, GUaOp6/8 at
  (psi', fullS) (OutNatG, K8G), GUaOp10.UaK.uaKesi.
- DONE: the universe is FIBRANT, generically (GCompU5.FibU) and in both
  instances: Delta DFibU.fibU (Classical.Cl), posets PCompU.fibU.
- ExtSub takes the substituted cofibration as data (psi' : Cof[D'] ,
  fullS : full' d = full (s d)): Ext reads psi only through full, so any
  psi' with psi's extent along s will do (canonicity-11, 2026-10-15; also
  LDS / ExtObS / PhiS / ActS, GExtNat1.ExtMove, and glueCl-sub).  The
  generator-wise form (cQ2 on D' with GQ : cQ2 X d l = cQ X (s d) l) is
  GExtSub2.PQ (psi' = mkCof, fullS from GQ; default Dflt = psi[s], GQ =
  refl); GExtSub2.HQ.hg states it as GensIns (the same list).  Needed
  because p|h's own cofibration has generators pre g (pre h Q_l), equal to
  psi_p[y h]'s pre (h g) Q_l only by pre-comp.  The other instance is a
  RE-PRESENTATION with one empty generator inserted (GCofIns.InsC,
  fullS-ins, hg-ins), for the KESI of ua (U6).
- NOT proved (deferred to the one-sieve redesign): invariance of Ext and
  its structures (extFib, extEquiv) under RE-PRESENTATION of psi (another
  list with the same sieve; it would need the KESI of the A-filler, since
  delta's sides are indexed by the list).  GUaOp does not need it: psi_p[y h]
  and psi_{p|h} have the same list with generators equal by pre-comp, so
  they are equal as Cof records (GCofib.cof-ext) and J carries everything.

Open (questions to Thierry via seg-62):
1. RESOLVED: Ext in local-data form, then (B) as above.
2. RESOLVED (Thierry): the classifier of the glued type is defined BY CASES
   ON psi, as Ext itself.  Delta (horn op, natural in the context, not
   uniform): for a horn problem at rho, if full(rho) use B's own horn op
   (the side's classifier; the horn data lie in B since full is stable
   under restriction), else fibToHorn (extFib).  Natural (full of psi[s] at
   rho' = full of psi at s rho', toCl-sub on the other branch); on psi it
   is the side's classifier by definition: no round trip, no
   normalisation, no choice.  Generic step: a "glue classifier" parameter
   (from B's classifier on psi and Ext's FibEL, Ext's classifier
   restricting to B's on psi), replacing ElYonCl.  Options (b) normalised
   horn ops and (c) propositional isFib are dropped.  Posets: toCl
   (extFib) = extFib with extComp-full (on psi the composites are B's).
