Proposition 4.6 of projective.pdf: complete
==========================================

Final entry point:
  PicardComplete[l].Over[R,setR,sag].equivalence
    : Equiv (Line * Degree) (P1 -> Line)

The forward map is (a,d) |-> (p |-> a tensor O(d)(p)). Its inverse is
B |-> (B([0:1]), degree B), with both inverse equations checked.
Line is the small type of R^*-torsors. P1 is the two-chart quotient.

Assumptions
-----------
Univalence and replacement (with the existing all-level surjectivity
schema), and SAG's Loc, uniform SQC and Z-choice. No additional algebraic
or chart-triviality hypothesis, no postulates and no checker changes.

The previous conditional interfaces remain available:
  PicardSAG.Over[R,setR,sag,charts]
  PicardSAG.FromLocSQC[R,setR,sqc,loc,charts]
The latter avoids Z-choice but takes chart triviality as a hypothesis.
PicardComplete discharges that hypothesis through ChartTriviality.

New geometric bridge
--------------------
AffineLineProjector constructs a finite rank-one projector over a finitely
presented affine algebra, with fixed vectors equivalent to global sections.
The completion adds eleven files (545 lines):

LineFrameRecovery: a line vector with a normalised functional determines a
unique torsor frame. Mere inhabitation is used only for a proposition.
AffineFreeFrames: a global projector factorisation gives a global frame.
AffineScalarFactor: any line/dual pair factors the projector up to a scalar.
AffineScalarClearing: equality on D(f) is killed by a power of f, via 7.1.8.
AffineLocalFrames: extend a local frame and its dual by 7.1.8. Their pairing
agrees with a power of f on D(f). Clear this ONE scalar difference to obtain
exactly HorrocksInterface's local certificate.
MonicLineTriviality: Horrocks now proves triviality over Spec R[X] from a
frame on a monic standard open (the torsor form of Proposition 2.2).
AffineLineCoordinate: Spec R[X] is R, compatibly with polynomial evaluation.
ReciprocalMonic: reverse and normalise a polynomial with invertible constant
coefficient, and multiply by X, obtaining a monic open in the other chart.
LineFrameNearZero: Z-choice supplies a polynomial neighbourhood of zero
with a frame. No choice of an actual polynomial degree is needed.
ChartTriviality: apply monic triviality to the opposite chart, in both
directions. corollary-2-3 has the interface type; paper-corollary-2-3 states
mere constancy at the respective chart origins, as in the paper.
PicardComplete: combine the proved charts with the proved Laurent algebra.

All truncations of frames are OUTSIDE the whole space of sections.
Pointwise mere triviality is not substituted for a chart trivialisation.

Horrocks integration
-------------------
../horrocks/ contains the completed COLL/horrocks-review package: all
66 package sources and 90 dependency files match its reviewed SHA-256
hashes. HorrocksProof.Over[A,setA].horrocks uses no SAG axioms and applies
to any commutative set-valued ring A.

The combined namespace required three private compatibility copies here:
LocalMonicGenerator and FormalRowIdeal rename their nested Vanish modules
to VanishingResult; FormalGcd updates the corresponding qualified reference.
These avoid the torsor library's root Vanish module. The Horrocks package,
external review directory and other workers' libraries are unchanged.
Older compatibility copies remain: PicardTorSum (Tensor -> TensorMaps),
LocalizationIdeal and RegularQC (SectionLocalizationKernel alias).

Conventions
-----------
lo(x)=[x:1]; hi(y)=[1:y]; overlap xy=1.
e_hi = x^d . e_lo after transport from hi(x^-1) to lo(x).
Degree nonneg(n) denotes n; negative(n) denotes -(n+1).
The older projective/Algebra.CRing implementation is not used: the short
chart quotient is ported to the common Ring.CRing. An explicit comparison
with that older implementation is not part of this package.

Verification
------------
  python3 check.py
  python3 check.py --isolated
An alternative executable can be supplied with --checker PATH.
The script checks the full source closure, without --only. An isolated
export contains regular copies of every reachable source and a hash manifest.

Latest isolated check: 278 sources, 9773 declarations, 0 failed, 4.92 s.
Ten expected inherited negative tests. All 277 imported modules check
individually, maximum 0.71 s. A false replacement for the final proof was
rejected in the isolated export; the original was restored and every
source reverified against the manifest. See CHECKED.txt.

Nothing is committed. Isolated source closure is checked; availability of
all these uncommitted files in a fresh clone is not claimed.
