# Handoff: SAG Section 3, worker B (§3.2 and §3.3)

Two LLMs formalise Section 3 of SAG (`/Users/coquand/COLL/SAG.pdf`, pages 9–11)
in parallel, in the primrec prototype (`seg/primrec`).

- **Worker A** (the other LLM): §3.1, i.e. affine schemes, quotients by
  finitely many elements, localisation A[f⁻¹], D(f) = Spec A[f⁻¹] (3.1.6),
  3.1.7–3.1.9.
- **Worker B** (you): §3.2 and §3.3.

## Scope of worker B

1. **3.2.1** Spec A × Spec B = Spec(A ⊗ B). Construct A ⊗_R B for finitely
   presented A, B, with its universal property (coproduct of commutative
   R-algebras: Hom(A⊗B, C) ≃ Hom(A, C) × Hom(B, C)) and finite presentation.
   A natural route is to concatenate presentations: variables n + m, the
   equations of both, renamed along the two inclusions. The result is
   independent of the chosen presentations by the universal property.
2. **3.2.2** Pullback Spec A ×_{Spec C} Spec B = Spec(A ⊗_C B). This is the
   pushout of R-algebras. Add equations identifying the images of the
   generators of C in A and in B.
   - **To verify first:** that every element of a presented algebra is
     merely the value of an expression (needed to write those images as
     expressions).
3. **3.3.1** A ⊗ B ≃ (Spec A → B) for finitely presented A, B. Follow the
   paper's chain of equivalences: SQC for A ⊗ B, 3.2.1, currying, then SQC
   for B.
4. **3.3.2** Eventually vanishing families of sequences have a common
   bound: apply 3.3.1 with B = R[X].
5. **3.3.3** is already proved twice, by a simplified route (SQC for A[T]
   and R[T], no tensor product): `bounded/Bounded.seg` and
   `presentations/UniformBounded.seg`.
   - Add the paper's route from 3.3.2 only as a corollary.
   - Say which hypotheses each route uses.
6. **3.3.4** (Loc, SQC, Z-choice). It needs worker A's
   D(f) = Spec A[f⁻¹]; do it last, after integration. The max over finitely
   many bounds exists already: `torsor/Alg73.seg` (`bound`, `Bnd`, a sum of
   the numbers).

## Existing material to reuse (read first)

- `presentations/README.txt` and `presentations/CHECKED.txt`:
  - `Over[R,setR].Algebra`, `Hom`, expressions `Expr`, `Presents P A`, `FP A`
    (truncated), uniform SQC;
  - `AddVariable` (A[X] presented by one more variable);
  - `PresentationExistence` (every presentation has a presented algebra);
  - certificates (`PrincipalCertificates`, `WeakNullstellensatz`).
- Universe convention there: expressions and solutions live in U l;
  `Presents` and `FP` live in U l+. No resizing.
- `polynomial/`: A[X] and its universal property.
- `replacement/`: truncation, quotients.
- `notes/sag.tex`: what is formalised so far, and the style of the note.
- `torsor/Affine.seg`: how Loc and Z-choice are stated as hypotheses there,
  with X → R in place of A. Align with worker A's interface, not with this.

## Coordination

- **Work in a new directory**, e.g. `seg/primrec/tensor/`. Link shared files
  read-only (symlinks, as in the other directories).
- **Do not modify** files of other directories, nor anything worker A
  creates.
- **Worker A owns the shared interface**: the Loc/SQC/Z-choice record,
  algebra maps, finite-presentability conventions. If
  `seg/primrec/SEC3-INTERFACE.md` exists, follow it. If it does not, start
  with 3.2.1, which needs only the presentations library, and ask Thierry
  before fixing a shared convention.

## Rules (Thierry's standing instructions)

- Every file checks in under 5 s; a slow check signals a mismatch between
  the mathematics and its formalisation, so restructure rather than wait.
- No shell command over 1 minute; anything long runs in the background.
- Small checks first, with `./segc DIR all` (or `changed`) from
  `seg/primrec`.
- Never commit unless Thierry asks.
- Write concisely, no jargon; README per directory. At the end, add a
  subsection to `notes/sag.tex` and rebuild `sag.pdf`.

## Checker reminders

- `split` only as the body of a definition. Recursive results are named
  `| r`; a definition is not in scope in its own body.
- Records: `mkR params fields`.
- Not allowed:
  - `module G = F x` (write `(F x).name` or `F[x].name`);
  - parametric module aliases.
- `Not` may be out of scope; write `A -> Empty`.
- Name clashes between a file module and its inner module are errors.
- Hidden-argument helpers: `symH`, `transH`, `apH`, `substH` (Paths.seg),
  and `calc A { a =< p > b ... }`.
