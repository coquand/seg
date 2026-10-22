# Section 4 coordination

Worker A owns `closed/`: 4.1.1--4.1.4, finitely generated ideals and
Lemma 1.3.8. Worker B owns its new directory for 4.2 and Proposition
2.2.3(b),(c). Do not edit the other worker's files or shared foundations.
Dependencies are read-only symlinks. Nothing is committed.

Use the Section 3 conventions in SEC3-INTERFACE.md: Algebras, Presentations,
Ring.Nat, Presentations.Fin, and SAGAxioms. Do not redefine these.

Shared definition owned by A, `closed/ClosedProp.seg`:
`ClosedProp[l].Over[R,setR]` exports
- `Zeros n xs = (i : Fin n) -> Id R.R (xs i) R.z`;
- `Witness Q = (n : Nat) * (xs : Fin n -> R.R) * Equiv Q (Zeros n xs)`;
- `Closed Q = || Witness Q ||`;
- `ClosedSubtype X sub = (x : X) -> Closed (sub x)`.

Using Equiv, rather than implications alone, makes the predicate apply
only to propositions, even though Q is an arbitrary small type. The
lemma `closed-prop` recovers isProp Q. B can define Open in the same
way with `|| (i : Fin n) * unit(xs i) ||` in place of Zeros.
Keep code in .seg modules; this file only records interfaces.

Ideals owned by A will be predicates with proposition-valued membership
and closure laws. Finite generation is mere existence of a finite family
generating that predicate, with membership expressed by truncated
FiniteIdeal coefficient certificates. Equality is extensional.
4.1.2--4.1.3 concern actual ideals, not their radicals.

A's checked denominator-clearing interface:
`a/1 = 0` in A_f iff `|| (k : Nat) * f^k*a = 0 ||`.
`LocalizationKernel.Over[R,setR].At[A,L,f,inc,loc]` exports `clear`
and `vanish`; `clear-equal`/`equal` handle equality of two fractions.
`LocalizationIdeal.Over[R,setR].At[A,L,f,inc,loc,n,gs]` exports
`clear`/`localize` for membership in the extended ideal.
The universal property suffices; no FP or geometric hypothesis is used.

Lemma 1.3.8 is checked in `IdealGluingEquality.seg`, with literal equality
of ideal extensions. A is an arbitrary ring. No covering assumption is
made; the theorem asserts mere existence, not uniqueness in that generality.

B's suggested dependency order:
2.2.3(b),(c); 4.2.1--4.2.7; affine case of 4.2.8; 4.2.9(a) using Spec R;
4.2.9(b) pointwise, which also gives the full 4.2.8. A scheme definition
is not needed for this route. 4.2.11 also uses 2.2.3(b).

Status: A's 4.1.1--4.1.4 and Lemma 1.3.8 are complete. B's `opens/`
files are also present and check jointly in `closed/Section4.seg`:
3860 declarations, zero failures, 1.06 s.

The quotient form of 4.1.4 is
`ClosedAffine.Over[R,setR,axioms].At[A,fp,sub,closed].theorem`;
it retains the equivalence over Spec A. The intrinsic affine-type form is
`ClosedAffineGeneral.Over[R,setR,axioms].theorem`.
See `closed/README.txt` and `opens/README.txt` for exact statements.
Neither worker's source files were edited during integration.

## Worker B exports (`opens/`, checked)

`OpenProp[l].Over[R,setR]` mirrors `ClosedProp`: `Units n xs = || (i : Fin n) * unit(xs i) ||`,
`Witness Q = (n : Nat) * (xs : Fin n -> R.R) * Equiv Q (Units n xs)`, `Open Q`,
`open-prop`, `OpenSubtype X sub`, `units`, `from-iff`, `along`.
`OpenProp[l].Iff P Q = (P -> Q) * (Q -> P)`.

`Units23[l].Over[R,setR,sqc,loc]`, `loc : StandardOpens[l].Over[R,setR].Locality`:
- 2.2.3(b) `nonzero-iff-some-unit n xs : Iff (Zeros n xs -> Empty) (Units n xs)`;
- 2.2.3(c) `nilpotent-iff x : Iff (AffinePowers.Nilpotent x) ((x = 0 -> Empty) -> Empty)`.

Worker B, further results (checked, `opens/`):
- `OpenOps[l].Over[R,setR]`: `open-empty`, `open-top`, `open-and`, `open-or`, `preimage`;
  `.SAG[sqc,loc]`: `open-neg-closed`, `neg-closed-open` (4.2.2), `stable` (4.2.3(e)).
- `Separation[l].Over[R,setR,sqc,loc]`: `open-ne` (4.2.5), `specialises-nn`, `nn-specialises` (4.2.6).
- `OpenAffine[l].Over[R,setR,axioms]`: `At[A,fp,S,o].theorem` (4.2.7), `Glue`, `affine-open-open`.
- `Transitivity[l].Over[R,setR,axioms]`: `Affine[..].theorem` (4.2.8, affine), `sigma` (4.2.9(a)),
  `transitivity` (4.2.9(b)), `Implication[P,Q,cp,oq].theorem` (4.2.11).
