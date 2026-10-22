# Shared Section 3 interface

Worker A owns `affine/`; Worker B owns `tensor/`. Shared dependencies remain unchanged in `presentations/`. No checker changes or new foundational axioms.

Use `Algebras[l].Over[R,setR]` for algebras, homomorphisms and `Spec`; `Presentations[l].Over[R,setR]` for `Presents`, `FP`, uniform `SQC`; `Ring[l]` for `Nat`, lists and rings; `Presentations[l].Fin` for finite families.

`affine/SAGAxioms.seg` states SAG §2.1:
`SAGAxioms[l,k].Over[R,setR]` has `Loc`, `SQC`, `ZChoice`, and `Assumptions`.
The family in Z-choice lives in `U k`, independently of the ring's `U l`.
Unimodularity is mere existence of coefficients with sum `f_i*r_i=1`.

## Localization: available to Worker B

`AffineInterface[l].Over[R,setR]` (abbreviated I):

- `I.D A f = (x : Spec A) * unit(x(f))`.
- `I.LocalizationWitness A f = (L : Algebra) * FP L * (inc : Hom A L) * Localizes A L f inc`.
- `Localizes` includes the inverse of `inc(f)` and the canonical universal property for *every* R-algebra target B.
- `I.localize A fp f : || I.LocalizationWitness A f ||` in `U l+`.
- `I.spectrum A f loc : Equiv (Spec loc.1) (I.D A f)`. Its forward map restricts an algebra map along `loc.2.2.1`.

All of these definitions and proofs check. This is mere existence with UP, as for Worker B's tensor products; no choice of a presentation from `FP`.

For 3.3.4, eliminate `localize` into the proposition “the given function on D(f) merely has a bound”, apply `UniformBounded` to `loc.1,loc.2.1`, and transfer through `I.spectrum`.

This integration is now implemented in `affine/UniformChoice.seg`:
`Over[R,setR,axioms].At[A,fp,family,prop,up].theorem` proves 3.3.4
from pointwise mere inhabitants. `axioms` has type
`SAGAxioms[l,l].Over[R,setR].Assumptions`.

`FiniteQuotient[l].Over[R,setR]` similarly provides `quotient A fp n fs : || Witness A n fs ||`, with the actual quotient inclusion, finite presentability, canonical UP, and spectrum equivalence to simultaneous zeros.

## Integration

Worker A's generation lemma is `AffineGenerated.seg`; Worker B's is `Generated.seg`, so their modules can coexist. Other new Worker A filenames are distinct from Worker B's files. Use the import order in `affine/All.seg` for Worker A's dependencies.

`affine/Section3.seg` checks both developments together (2646 declarations,
zero failures, 0.83 s). `Section3Examples.seg` turns Worker B's tensor and
pullback results into `FunctionAlgebra.Over[R,setR].Affine`.
`AffineUniqueness.Over[R,setR,sqc].At[X].proposition` proves uniqueness of
the full affine witness; `function-algebra-fp` gives finite presentability
of the canonical algebra R^X. Worker B's files have not been edited.
