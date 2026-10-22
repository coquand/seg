# The univalence operation on the universal glue data (Step 3, VV form)

Fixed r.  GDr is the presheaf (level a+) of glue data with r generators;
over it the universal data (AU , psiU , BU , alU , eqU) and its Ext,
ExtBig, with the map ext and the equivalence structure extEquiv
(Theorem 7, once, at a+).  SA is the small copy of ExtBig (GExtCmp's
fibrewise iso).  CU = CU.resCtx is the sub-presheaf of full points.

## 1. Substituting small structures (GXsubEq)

For small types B , A over a large context G, a map al : B -> A and an
equivalence structure k on it, and s : D -> G (XSub), the data
s*(al , k) over D on (xsub B s , xsub A s) is k moved along s with identity
fibre maps.  Laws:

- (o)   t*(s*(al,k)) = (s o t)*(al,k)          for t : T -> D
- (L)   s'*(u*(al,k)) = (u o s')*(al,k)        for u : G' -> G large
- (up)  moving a structure up and back down is substituting it.

## 2. The universal univalence datum

U := (SA , AU , alSA , eSA) over GDr: ext and extEquiv moved onto SA, once.

## 3. kop and kunif

For a problem (X , F , p), d_p its point of GDr (GUaPt), yd its Yoneda map:

    kop p  :=  yd*(U)        (A side read as F by Yoneda; code smallCl yd)

kunif: yd_(p|h) = yd_p o y h (GUaPtNat.natP), then (o) and smallCl-sub.

## 4. Full points

    inclR*(U) = (BU , AU' , alU , eqU)     on CU

(GExtFull along inclR at a+): over a full cofibration Ext is B.

## 5. kfull

When a side of p contains id, x = (d_p , full) is a point of CU and
yd = inclR o yx.  Then

    kop p = yx*(inclR*(U))          (L)
          = yx*(BU , eqU)           (4)
          = the local data of d_p   (yonL, (up))
          = the side's value        (glueES; the Yoneda chain of GUaGlue2)

The code: smallCl at a full point is B's code (parameter smallCl-full).

## 6. kesi, ua

kesi: an empty side inserted changes r to r+1; the two points are related
by the map GDr_r -> GDr_(r+1) inserting an empty generator, which
preserves U (one equation), so kesi is (L).  ua = ContrOp[kop, kside, kunif]
with kside = kunif then kfull.

## Status (2026-10-16, end of session)

Done, on the copy only (full copy check 346/346, each file < 10 s):
GXsubEq, GTransferEqTwice, GExtFullPt, GUaUniv (U, kop, kunif), GUaFull,
GUaLoc, GUaLoc2, GUaKfull (kfull, parameter smallCl-full), GUaOpN (generic
ua), GUaFullL1 + GUaFullL (posets smallCl-full), GUaOpNL, PUaOp.uaN.
Edits to generic files: GYonEq4 level-polymorphic + yonE; GExtCmp.CM.At.PF.
Removed: GUaOut, GUaOutNat, GUaKunif.

Open: kesi for the new kop.  With cofibrations as lists, kesi needs
ins_k : GDr_r -> GDr_(r+1) and Theorem 7 natural along it (GExtNat's
content); decision: defer to the one-sieve-per-cofibration redesign, where
ins_k is the identity.  Until then PUaOp.uaKesi / fibU use the old ua, and
GUaOp1-10, GUaOpL, GExtNat stay (about 3,100 lines deletable afterwards).

## Step 4: one sieve per cofibration (2026-10-16, copy step4)

Poset sieves as subsets of points (Constr.PosB: Subset X = El X -> Bool,
f lands iff its image is inside) are NOT closed under union: (i=0) or
(i=1) on [1] is the whole of [1] as a subset, yet id lands in neither.  So:

- PosS: posets as an IvBase instance with CANONICAL sieves (CSieve:
  decidable sieves of maps, as DeltaBase does for Delta).  A union is one
  sieve (bigU); forall of a list of lines is one sieve, decided at the
  generic point (pr1 , pr2) of W * [1] (PSFaU, forallUn = 1); connections
  are PosetConn's.  Constr.PosB stays for the old Subset files.
- GCofOne (generic, parameters bigU / bigU-in / bigU-out): a partial
  element is one sieve with a section (PSide); a list of compatible sides
  presents the side on the union (one p).  restrictP commutes with one
  (one-restr), an inserted empty side does not change it (one-ins).
  Wrap k: kop p = k.kop (one p); KESI is apH k.kop (one-ins ..).
- The poset chain (PElL, PElL2, PElYon, PElYon2, PUaOp, PCompU) now lives
  on PosS; PUaOp.ua = Wrap(GUaOpN's ua), uaKesi = Wrap's kesi; PCompU's
  fibU uses them.  GUaOpL deleted.
- Not yet deletable: GUaOp1-10, GExtNat*, GCofIns, GensIns / forallU-ins
  (Delta: DUaOp, DFibU, DClFull, DTautCl, DeltaForall).  Delta's sieves are
  already canonical, so Delta's switch is bigU (anyF, as here) + Wrap +
  smallCl-full for GUaOpN.

seg notes: comparing `new` records built at different sites is not
reliable (use partExtH / kop-cong, as GCofib's restrictP-o does); BSD sed
has no \b.

## Step 5: the Delta switch (2026-10-16, copy step5)

Statements are about the SIEVE; a list of faces is only a presentation of
it (its union).  Cof / Partial in Theorem 7 and FibE keep their lists for
now, read through GCofOne: a partial element is the one side on the union
of its sides, and an operation used through GCofOne.Wrap does not see the
presentation (KESI is apH of the union's invariance).  Rewriting the
lists away everywhere is a separate decision.

Filling operations, generic (next to GSmall):
- GFillS: a filling operation for a family of sieves (index, condition,
  object, sieve); op-ext, hd-eq, OpExt.isOpExt.  Delta's horn filling is
  the instance (m , k), k <= m+1, [m+1], the horn (DeltaClassifier).
- GFillX: pullback along a cartesian map with fibrewise bijections (D at
  level k, G at level l).  DeltaClassifier.Sub is an instance; GFillXS is
  the small-over-large instance along GSmall.XSub.

Delta's classifier parameters of GUaOpN, in universal form:
- DSmallCl: hBig = ONE horn filling on Ext of the universal glue data
  (DGlueCl.GC at a+: B's code at full points, toCl of Theorem 7's
  composition elsewhere; B's = El's pulled back along bmap);
  smallCl = hBig pulled back along (al , ph , ps); smallCl-sub = the moved
  data have the same values.
- DSmallFull / DSmallFull2: smallCl-full, on GUaFullT (the
  classifier-independent part, shared with posets' GUaFullL / GUaFullL1).
- DUaOp.ua = Wrap(GUaOpN's ua); DFibU.uaKesi = Wrap's kesi.

Deleted: GUaOp1-10, GExtNat1-10 + 4J, GCofIns, GCofEsi2, GFibMove,
DGlueClSub, DClFull, GFillXC (3,756 lines); GensIns, FaU.forallU-ins and
its instances (PosS, DeltaForall, Constr), GExtSub2.HQ.
