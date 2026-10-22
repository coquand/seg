Integration note (2026-10-20)
=============================
This is the integrated primrec/horrocks copy of COLL/horrocks-review.
SEG sources retain all reviewed hashes; dependencies are relative links
to the live repository. The original review directory remains untouched.

Run the standalone check from this directory:
  ../dist-newstyle/build/aarch64-osx/ghc-9.6.7/segd-0.1.0.0/x/segd/build/segd/segd All.seg
Integrated standalone result: 4982 declarations, 0 failed, 2.85 s.
The complete geometry and isolated export are checked from ../picard/:
  python3 check.py --isolated
That includes Horrocks and proves Proposition 4.6 from SAG alone.
See ../picard/README.txt and HANDOFF-B.txt. Nothing is committed.

Original external review documentation follows; its paths and packaging
instructions refer specifically to COLL/horrocks-review.
======================================================================

Appendix 1: rank-one affine Horrocks, checked
=============================================

HorrocksProof.Over[A,setA].horrocks : HorrocksInterface.Over[A,setA].Horrocks

The theorem holds for an arbitrary commutative ring A (with a set as
carrier). It uses no SAG axioms, determinants or Schanuel lemma, and
the interface type is unchanged. The only global assumptions are those
of the project foundation (univalence and replacement, see All.seg).

Work is isolated here because the CANONICITY repository is outside this
session's writable roots. No source file in that repository was modified.
Nothing was committed. Worker A's files and worker B's Laurent algebra
are unchanged.

Check
-----

    python3 /Users/coquand/COLL/horrocks-review/check.py
    python3 /Users/coquand/COLL/horrocks-review/check.py --isolated

The script accepts --checker PATH for another SEG checker executable.
It verifies dependency/source hashes and rejects links outside this
package. The isolated mode copies the package into a fresh temporary
directory and checks there, without access to live source dependencies.

horrocks/ contains the new source files and relative links into
dependencies/. DEPENDENCIES.txt records the original source locations
and SHA-256 hashes of the frozen dependencies. SOURCES.sha256 records
the new SEG sources. REVIEW-FILES.txt lists the files to review.
All.seg uses the same foundation parameters as the original project:
univalence and replacement, with truncation and effective quotients
derived as in the existing library. No new algebraic axioms were added.

Main checked results
--------------------

MonicLifting.Over[A,C,setA,phi,lift-unit].At[...].lift
  Full monic lifting in a relative formulation. Given an ideal I of
  A[X], a monic f in I, and g in I whose image is monic of degree r,
  produce h in I monic of degree r with exactly the same reduction.
  The map phi must make every element mapping to 1 invertible.
  Polynomial bounds are explicit; no actual-degree decision is used.

FiniteRadicalLifting.Over[A,setA,m,fs].At[radical].Lifting
  Instantiates the preceding result with the actual quotient A/(fs),
  where (fs) is contained in the Jacobson radical. The kernel and
  unit-lifting conditions are proved, not assumed as extra axioms.
  This is the finite-ideal version needed at formal gcd nodes S(I;U).

LocalMonicGenerator.Over[A,setA,m,fs].At[...].Reduction[generates].factors
  Lemma 7.6 in the form needed for the row ideal of the existing
  scalar factorisation certificate. Given:
    * a finite Jacobson-radical ideal J=(fs) of A;
    * X_i Y_j=f^k E_ij and sum_i Y_i X_i=f^k, with f monic;
    * a monic h=sum_i Y_i hc_i;
    * coefficients a_i with Y_i=h*a_i modulo J[A[X]];
  merely produce coefficients b_i with Y_i=h*b_i in A[X].
  Its .free corollary returns the existing Free E type.
  This theorem uses no residual discreteness and needs no projector
  axioms beyond the supplied scalar factorisation certificate.

PolynomialNakayama...Given[...].all-zero
  If a ring receiving A[X] kills a monic h, and finitely many v_i
  satisfy v_i=sum_j q_ij(X)*v_j with every coefficient of each q_ij in
  a finite Jacobson-radical ideal of A, then all v_i vanish.
  The proof expands in the finite power basis, forms a rectangular
  finite family, and eliminates its generators over A.
  The degree-zero case is handled explicitly.

CertificateDescent.Over[B].At[...].descend
  A principal row ideal descends a scalar factorisation to Factors E
  whenever its scalar denominator is regular. It requires neither a
  trace calculation nor determinants.

MonicRegular...At[lower].power-regular
  The actual polynomial-ring element representing a monic, and every
  natural power of it, is regular. Degree zero and the zero ring are
  included. PolynomialMap proves preservation under base change.

FiniteGluing...Compatible[...].glued / .restrict / .unique
  The algebraic gluing formula for compatible numerators once a
  common denominator and a partition of unity have been supplied.
  This is NOT the full localization/gluing step in Corollary 7.7.

Global assembly
---------------

FormalGcd.compute
  The formal gcd tree over the monoids S(I;U). Each leaf carries a monic
  member of the row ideal that generates it modulo the leaf's radical.

FormalMonoidTree.comaximal, TreeLeaves.Partition.partition
  Any choice of one denominator per leaf generates the unit ideal.

PolynomialClearing
  Over a monoid localization A_S: polynomials times some s in S come from
  A[X]; a polynomial of A[X] vanishing over A_S is killed by some s in S.

LeafClearing
  At a leaf, Lemma 7.6 (LocalMonicGenerator) gives h = sum y_j c_j,
  y_j = h b_j over A_S[X]. Clearing gives d, tau in S and, in A[X],
  p = sum y_j z_j, p = d h over A_S, tau y_j = p bb_j.

LeafOverlap
  For two leaves, over the product monoid S1 S2 both monic generators
  generate the row ideal, so they are equal (MonicUniqueness, including
  different degrees). Hence u v (d2 p1 - d1 p2) = 0 with u in S1, v in S2.

CompatibleNumerators
  r_i = prod_k u_ik v_ki, s_i = d_i r_i, H_i = r_i p_i, t_i = r_i tau_i
  satisfy s_i H_j = s_j H_i and t_i y_j = H_i bb_ij exactly in A[X].

HorrocksProof
  Two partitions of unity for (s_i) and (t_i), PrincipalRowGluing gives
  g with g in (y) and y_j = g a_j; CertificateDescent cancels f^k.

The global generator g need not be monic. The leaf degrees may differ.
