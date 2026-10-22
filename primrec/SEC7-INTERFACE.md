# Section 7.1: shared interface and ownership

Worker B owns `bridge7/` and this module interface: modules over
`Ring[l].CRing`, the translation to `torsor/Alg73`, and the bridge that
makes 7.3.6 a theorem from Loc, SQC and Z-choice.
Worker A owns boundedness on schemes and 7.1.2-7.1.8, in a separate directory.
Dependencies remain read-only; `torsor/` is not modified.

Check with the direct `segd` on `bridge7/All.seg` (Sections 2-5 and
`torsor/` loaded together: 6248 declarations, 1.8 s).

## Small types (`NatFin[l]`)

Sections 2-5 and `torsor/` use different copies of `Nat` and `Fin`.

- `toN : Nat -> Base.Nat`, `fromN`, `to-from`, `from-to`.
- `toF n : Fin n -> Cech.Fin (toN n)` (old elements to `some`, the new one
  to `none`), `fromF n`, `from-toF`.

Constructors are resolved by type, so `zero`, `suc`, `none`, `some`,
`inl`, `inr` need no qualification.

## Rings (`RingBridge[l].Over[R,setR]`)

- `ring : Alg73.CRing`, the same carrier and operations.
- `unit-to`, `unit-from`: the unit types are the same type.
- `power x n : RA.pw x (toN n) = AffinePowers.power x n`.
- `sum n h : Reg.sumR (toN n) h = FiniteIdeal.Sums.sum n (h . toF n)`.
- `loc X Mx lc : Aff[ring,X,Mx].LocR` from `StandardOpens.Locality`.

## Modules (`Modules[l]`)

- `le-plus m n : CB.le m n -> (d : Base.Nat) * (d + toN m = toN n)`, the
  form of `<=` used by `Alg73`.

`Modules[l].Over[R,setR]`:

- `Module = Alg73.Mod[ring]`. All of `Alg73.MA` applies
  (`sub`, `sumM`, `sm-zr`, `sm-sub`, `FEq`, `Zero`, `zero-raise`, ...).
- `regular : Module`, R over itself.
- `pi X Mx : Module`: M(X) = (x : X) -> M x with pointwise structure
  (7.1.1). Sections over a subtype U are `pi (Σ x. U x) (Mx . fst)`.
- `Fractions[Md]`, with exponents in Ring's `Nat` (the `Nat` of 3.3.4):
  - `Kills g x K`: g^K x = 0; `kills-prop`; `kills-up` (upwards closed
    along `CB.le`), the shape needed for uniform exponents.
  - `Same g x p x' p' K`: K witnesses x/g^p = x'/g^p'.
  - `value g u x N`: x/g^N on D(g), with u an inverse of g.
- `WeaklyQC Md`: 7.1.5 as the two fraction clauses of `torsor`'s `WQC`
  over the point. A section over D(g) is merely m/g^N, and an m that
  vanishes on D(g) is merely killed by a power of g.
- `WqcBundle X Mx = (x : X) -> WeaklyQC (Mx x)` (7.1.7).
- `Restriction X Mx = Aff[ring,X,Mx].WQC`: 7.1.8 for U = X, in exactly the
  form used as the hypothesis of `torsor`'s 7.3.6.

Target for worker A's 7.1.8: for a scheme X and `w : WqcBundle X Mx`,
produce `Restriction X Mx` (only U = X is needed for 7.3.6).

The fraction-level statements are clauses, not equalities of modules:
M_f is not constructed as a type. 7.1.2 in the paper's form, an
equality of modules, would need it (a quotient by `Same`, with `Quot`).

## Theorem 7.3.6 (worker B, checked)

- `ZBridge[l].Over[R,setR,axioms].At[X,Mx,A,fp,e].zchoice`:
  torsor's `Aff.ZChoice` for X equivalent to Spec A, A finitely presented,
  from `SAGAxioms.ZChoice`.
- `Theorem736[l].Over[R,setR,axioms].Torsors[X,Mx,wq,T,ts]`:
  `presented A fp e`, `affine aff`, `small-affine aff`, each giving
  `||(x : X) -> T x||` for every M-torsor family T, from Loc, SQC,
  Z-choice and `wq : Restriction X Mx`.

`wq` is discharged by worker A (`qc-schemes/`, checked independently:
6415 declarations, 0 failed, 1.84 s):

- `Restriction718[l].Over[R,setR,axioms].At[X,scheme,Mx,w].theorem-7-1-8
  : Restriction X Mx` from `w : WqcBundle X Mx`; `Open[...]` for open
  subtypes.
- `AffineVanishing[l].Over[R,setR,axioms].Torsors[X,Mx,w,T,ts]`: 7.3.6
  with the paper's hypothesis, fibrewise weak quasi-coherence only.

## Kernels, quotients and cokernels (worker B, `cokernel7/`, checked)

Generic over `Alg73.CRing` (`Submodules`, `QuotientModule`, `PointQC`):

- `Linear P Q`, `Submodule[Rg,P]` (record: `S`, `prop`, `zero`, `add`,
  `neg`, `scale`), `Sub[P,K].carrier`, `Kernel[P,Q,f].sub`,
  `Image[P,Q,f].sub`, `Image.onto`.
- `QuotientModule.Over[Rg].Quot[P,K]`: `carrier`, `projection`,
  `surjective`, `kernel`, `in-kernel`.
- `PointQC.At[Md].WQC`: 7.1.5 at scalars; `from-aff`/`to-aff` convert
  with `Modules.WeaklyQC`.

With the SAG axioms (`Cokernel7113[l].Over[R,setR,axioms]`):

- `kernel M N f wM wN : WeaklyQC (ker f)` (7.1.6);
- `At[M,N,f,wM,wN].theorem : WeaklyQC (N / f(M))` (7.1.13), and
  `image-qc`.

`cokernel7/All.seg` loads all of Section 7.1 (figures below).

## The localised module (worker B, `cokernel7/`, checked)

- `Localisation[l].Over[Rg].At[Md,r]`: `L` (= M_r), `frac m p`, `phi`
  (M_r -> M^D(r)); `FromQC[rep,kill].equiv` and `ToQC[e].rep/kill`:
  phi is an equivalence iff the `PointQC` clauses hold at r.
- `LocalisationModule[l].Over[Rg].At[Md,r]`: `carrier` (M_r as a module),
  `phi-add`, `phi-scale`.
- `Localisation712[l].Over[R,setR,axioms].At[X,scheme,Mx,f]`: `equivalence`
  (7.1.2: M(X)_f = prod_x (M x)_(f x) over the ring X -> R), `psi-add`,
  `psi-scale`; `Restrict[w].theorem` (7.1.8 for U = X);
  `Open[X,scheme,Mx,w,sub,op,f].theorem` (7.1.8 for open U).

- `ModuleSIP[l].Over[Rg].sip A B (e,add,scale) : Id (Mod[Rg]) A B`.
- `LocalisationEq[l].Over[R,setR,axioms].At[X,scheme,Mx,f]`: `lemma-7-1-2`,
  `Restrict[w].lemma-7-1-8` (equalities of modules over X -> R);
  `Open[...].lemma-7-1-8` for open U.

`cokernel7/All.seg`: 7167 declarations, 0 failed, 3.43 s.
