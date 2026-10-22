# Section 5: shared interface and ownership

Worker A owns `schemes/SmallAffine.seg`, `SchemeMaps.seg`, `Schemes.seg`,
`SchemeSubtype.seg`, `SchemeFinite.seg`, `SchemeCover.seg`, `SchemeBasics.seg`,
and subsequent Section 5.1, 5.2, 5.4, 5.5 and 5.6 lemmas.
Worker B owns the gluing construction, Section 5.3, in a separate directory.
Dependencies remain read-only. Do not modify the checker or shared foundations.

The checked core interface is:

- `SmallAffine[l].Over[R,setR]`:
  `Sol p`, `sol-set p`, `Witness X = Σ p. Equiv X (Sol p)`,
  `Affine X = ||Witness X||`, `from-affine`, `to-affine`.
  Both the witness and its truncation are in `U l`.
- `SchemeMaps[l]`:
  `Fiber A X f x`, `Embedding A X f` (proposition-valued fibres),
  `Image A X f x` (truncated fibre), `Embedded[...].equivalence`
  from A to its total image, and `Subtype[...].embedding`.
- `Schemes[l].Over[R,setR]`:
  `Chart[X]` has `presentation`, `map`, `embedding`, `open-image`;
  `Cover[X]` has `size`, `charts`, `covers`.
  `Scheme X = ||Cover[X]|| : U l`; `set X : Scheme X -> isSet X`.
  `Domain X c` and `Image X c` expose a chart's domain and image.
  `from-cover X` introduces schemehood.

These definitions and the sethood proof use no Loc, SQC or Z-choice.
They keep the existing `SAGAxioms[l,l]` sufficient for later choice.
`SchemeSubtype[l].Over[R,setR]` supplies:

- `Witness[X]`: `size`, `subtypes`, `opens`, `affines`, `covers`, where
  `affines` uses the existing `FunctionAlgebra.Affine`.
- `Property X = ||Witness[X]||` at level l+.
- `From[X,w].scheme : Scheme X` for an actual subtype cover.
- `to-witness X c` converts an actual small chart cover to a subtype cover.
- `to-subtypes`, `from-subtypes`, and `equivalence` identify the two
  proposition-valued definitions. This uses finite choice, no Z-choice.

`SchemeCover[l].Over[R,setR,axioms].At[X,n,us,opens,schemes,cover].theorem`
proves that a finite open cover by schemes makes X a scheme.
Here `schemes i : Scheme (Σ x:X. us i x)` and
`cover x : ||Σ i:Fin n. us i x||`. Its construction uses finite choice,
concatenation, and `Transitivity.sigma`. It takes the existing
`SAGAxioms[l,l]` bundle because that is the interface of open transitivity;
there is no new call to Z-choice or 4.2.7 in the flattening construction.

`SchemeBasics[l].Over[R,setR]` supplies:

- `empty : Scheme Empty`;
- `affine X : FunctionAlgebra.Affine X -> Scheme X`;
- `small-affine X : SmallAffine.Affine X -> Scheme X`;
- `solutions p : Scheme (SmallAffine.Sol p)`;
- `top-affine` and `top : Scheme Top`;
- `along X Y e : Scheme X -> Scheme Y` for `e : Equiv X Y`.

All of these statements have passed the direct checker. `SchemeExamples`
also checks an application of `SAGAxioms[l,l].ZChoice` to the family
`x -> Cover[Ys x]`, verifying that no higher-universe choice is required.

Worker A's remaining results are now checked:

- **5.1.3:** `SchemeChoice[l].Over[R,setR,axioms].theorem X scheme B inhabited`
  produces `||Witness X B||`, where the small witness contains a finite
  affine open cover and sections of B on each chart domain.
  `theorem-on-images` gives sections on chart images instead.
  `FromCover[X,c,B,inhabited].refinement` retains the standard-open
  refinement of each original chart, its unimodular functions, and image
  equivalences. B is at level l; there is no higher-universe Z-choice.
- **5.2.1:** `SchemeSpecialisation[l].Over[R,setR,axioms].theorem X scheme x y`
  identifies specialisation with double-negated equality. This proof uses
  the full bundle through open transitivity; it does not establish the
  paper's weaker Loc/SQC-only assumption list.
- **5.4.1--3:** `SchemeSubtypes[l].Over[R,setR,axioms]` defines
  `Subscheme X sub = ((x:X) -> isProp(sub x)) * Scheme(Σx. sub x)`.
  `open-subscheme` and `closed-subscheme` prove this predicate;
  `open-subtype` and `closed-subtype` return just schemehood of the total
  subtype. `open-proposition Q op : Scheme Q` is also available.
  `SchemeAffineOpen.theorem` supplies the affine case using 4.2.7 and
  localization spectra.
- **5.5.1:** `AffineEquality[l].Over[R,setR]` exports `closed`, `affine`,
  `scheme`, and `diagonal` for equality in an affine type, with no geometric
  axioms. `closed-affine Q closed` proves every closed proposition affine.
- **5.5.2:** `SchemeEquality[l].Over[R,setR,axioms].theorem X scheme x y`
  gives `Scheme (Id X x y)`.

The new geometric results use the existing full `SAGAxioms[l,l]` bundle,
including 5.1.3 (the paper labels that proposition Z-choice).
These are results under the full SAG hypotheses; minimal dependencies
have not been recovered for 5.1.3 and 5.2.1.

Worker B's gluing implementation is checked in `gluing/`:

- `GluePushout[l].Glue[X,Y,V,sX,sY,f,g,ef,eg]` exports `P`, `set`, the
  inclusions `il`, `ir`, their embedding proofs, `glue`, `meets`, and
  `pushout B sB`. The latter proves that restriction is an equivalence
  from maps `P -> B` to cocones, for sets `B : U l`.
- `OpenEmbedding[l].Over[R,setR,axioms].Compose[...]` exports `comp`,
  `embedding`, and `open-image` for a composite of open embeddings
  with set-valued final codomain.
- `GlueScheme[l].Over[R,setR,axioms].Gluing[...]` exports `P`, `il-open`,
  `ir-open`, and `scheme : Schemes.Over[R,setR].Scheme P`.

The quotient construction reuses `projective/Quotient.seg` and requires
no geometric axiom. Geometric assumptions enter through open transitivity.
The universal property against arbitrary types, or target sets in a
separate larger universe, is not part of the checked statement.

The empty-gluing example establishes schemehood of the quotient and
disjointness of its inclusions. An explicit equivalence of that quotient
with the literal coproduct `X + Y` is not yet in the example.

Section 5.6 is checked, with these public interfaces:

- `SchemeSums[l].Over[R,setR,axioms].theorem X scheme Y schemes`
  proves `Scheme (Σx:X. Y x)` for arbitrary `Y : X -> U l` (5.6.1).
- `SchemeFamilies[l].Over[R,setR,axioms].At[X,scheme]` exports
  `theorem-5-6-2`, the actual equivalence between maps of schemes into X
  and X-indexed scheme families. `Subtype[Y,prop].theorem-5-6-3` identifies
  subschemehood with pointwise schemehood. `Family[Y].equivalence` gives
  the total-space / pointwise-scheme equivalence for arbitrary families.
- `SchemePullbacks[l].Over[R,setR,axioms].theorem X Y Z sX sY sZ f g`
  proves schemehood of `Σx:X. Σy:Y. Id Z (f x) (g y)` (5.6.4).
  `product` and `fibre` are also exported.
- `AffineSigma[l].Over[R,setR,axioms].bounded X affX Y w N bound`
  proves an affine total space when affine fibres have chosen small
  presentation witnesses `w` with variable counts bounded by N.
  `SchemeAffineSums.theorem` handles arbitrary affine fibres but concludes
  only schemehood. Do not interchange these two assertions.

`PresentationPadding` adds zero-coordinate constraints; `SchemeCoverPadding`
adds empty charts (using 1≠0). Neither silently adds free coordinates or
inhabited charts. `SchemeBounded`, `CoverSigma`, and `SigmaTools` supply
intrinsic affine boundedness, cover pullback, and dependent transport.
The proof uses only the existing level-l Z-choice and full SAG bundle.

Check from `primrec/schemes` with the direct `segd` executable and `All.seg`.
`Section5.seg` additionally checks all four gluing modules together with
Worker A's 5.1, 5.2, 5.4--5.6: 5194 declarations, no failures, 1.30 s.
All imports from Sections 3--4, projective/, and the foundations are symlinks.
Do not edit those files through this directory.

This completes Section 5 with the assumption and pushout-scope qualifications
above. Nothing is committed.
