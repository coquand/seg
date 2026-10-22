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
