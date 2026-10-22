# Handoff: indexed inductive types by Fordism, in the surface language of Unit

This was set aside by Thierry on 2026-10-17 as work "for another day, but very interesting".

## Why

The goal is to formalise in the checker, as future work, the typing rules of type theory with one univalent universe (Russell style) and their semantics in the model of `seg/core`. The bridge from Russell to Tarski is the Coquand–Sterbac equivalence: `~/DOMAIN/sterbac3.pdf`, with the Agda version in `~/DOMAIN/ERT`.

Its derivations (`WfCtx`, `IsType`, `HasType`, `ConvTy`, `ConvTm`) are **indexed inductive families**. The checker deliberately has none. See memory `future-tt-interpretation`.

## The idea: Fordism

Reference: Pujet–Tabareau, *Observational Equality Meets CIC*, §2.2, `~/CANONICITY/fordism.pdf`. They credit Fordism to Coquand's proof assistant Half in the 1990s.

An indexed family becomes a family with parameters: the index becomes a parameter, and each constructor gets an equation argument.

```
vec (A) : N -> U          vnil : vec A 0 ;  vcons m a v : vec A (S m)
  ~>
vecF (A) (n : N) = vnil (e : Id N 0 n) | vcons (m : N) (a : A) (v : vecF A m) (e : Id N (S m) n)
```

The eliminator of the indexed type is `split` followed by `idJ` on the equation. It has exactly the computation rules of the indexed type, because `idJ A a C d a (refl a) = d` is a rule of the core.

- **No change to the core is needed.** Pujet–Tabareau need a whole paper only because their cast does not compute on reflexivity for open terms.
- **Cubical type theories cannot do this** (the regularity problem; they use Cavallo–Harper's `fcoe` instead).
- **Decidable equality of the indices is irrelevant** for the eliminator and its computation rules. It matters only for which closed inhabitants exist.

## Proposal: surface syntax closer to indexed types, translated before checking

The core stays unchanged; it only ever sees forded sums, `split` and `idJ`. The translation is like `calc`, `open` and hidden arguments, which are already translated away. It is still a change to `src/` (`SegParse.hs`, and the filling pass of `Seg.hs` §12), so **ask Thierry before editing**.

### Level 1: indexed `data`, by the resolver

```
data vec (A : U l) : N -> U l = vnil : vec A zero
                              | vcons (m : N) (a : A) (v : vec A m) : vec A (suc m) ;
```

- The resolver produces the forded sum. Each equation goes from the constructor's index to the parameter, so that `idJ` based at the constructor's index applies directly.
- Using a constructor at its own index (`vnil`, `vcons m a v`) fills the equation with `refl`.
- Also generate the derived eliminator, like `mkM` for segments, plus injectivity and no-confusion lemmas for the constructors (by double `split` into the universe, as in the earlier `mtt` work).

### Level 2: `split` on an indexed type whose indices are distinct variables

- A branch is written as in Agda (`vnil -> t`), at the goal instantiated at the constructor's index.
- The elaborator wraps it in `idJ` along the equation. The motive is the goal abstracted over the index and the equation.
- This is deterministic, because the goal is known. It is the "path induction without writing the motive" recommended in memory `seg-lessons`.
- It covers the inversion lemmas of the ERT derivations, whose indices are generic.

### Level 3: indices that are not variables (Cockx)

- Splitting `v : vec A (suc n)` produces equations such as `Id N zero (suc n)`, to refute, and `Id N (suc m) (suc n)`, to invert.
- Cockx's rules without K apply (thesis `~/CANONICITY/jcockx.pdf`, *Dependent pattern matching and proof-relevant unification*): solution (by J), injectivity, conflict, and no deletion.
- Each step can be generated deterministically from the shapes of the indices, using the lemmas of level 1.
- This solves equations between indices, not unknowns in terms, so it is consistent with the "no unifier" ruling (memory `seg-hidden-args`).
- It is the largest piece; it can be postponed, with explicit lemmas used instead.

## Suggested order and first test

1. Level 1 on `vec` and on Martin-Löf's identity type written as an indexed type. Check that the derived eliminator computes (`#conv`) at `refl`.
2. Level 2 on a small typing judgement: Π and one universe, with `HasType`/`IsType` as one forded sum indexed by the kind of judgement, or as mutually defined sums.
3. Port a fragment of `~/DOMAIN/ERT`, for instance the erasure lemma (Lemma 4.6), to measure the cost against Agda.
4. Level 3 only if the explicit lemmas turn out to be too heavy.

## Rules

- Every file must check in under 5 s.
- All checking goes through `./segc DIR changed`.
- Never commit without Thierry's request.
- Write the design in a note first (as for `notes/model.tex`): the translation of a declaration, of a constructor use, and of a `split` branch, with the generated motives.
