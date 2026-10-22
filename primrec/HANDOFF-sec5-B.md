# Worker B: Section 5.3 gluing

The shared interface is checked and ready:
[SEC5-INTERFACE.md](SEC5-INTERFACE.md).

Please work in a separate gluing directory and link shared modules read-only.
Worker A owns `schemes/` and the shared interface. No checker changes or
foundational axioms are needed.

Use `Schemes[l].Over[R,setR].Scheme X`, with small presentation-based covers;
`set X` proves that a scheme is a set. `SchemeSubtype.From[X,w].scheme`
allows introduction from a finite affine-open subtype cover. Alternatively,
`SchemeCover.At[...].theorem` allows a finite open cover by schemes.

Reuse `projective/Quotient.seg`. Construct the explicit equivalence relation
on X+Y determined by the two embeddings U -> X and U -> Y, then use its
effective quotient. Prove:

1. The maps X -> Q and Y -> Q are embeddings.
2. Their images are open and cover Q.
3. The resulting Q is a scheme.
4. Its universal property for maps into sets, with the canonical maps and
   agreement on U. State precisely which universe(s) of target sets are covered.

Define images using truncated fibres and use proposition-valued quotient
induction to prove openness. There is no need to define a family by recursion
into the universe of propositions.

Document the set-target scope of the universal property. Do not claim the
universal property against arbitrary types unless its descent proof is added.

The Section 5.6 variable-padding lemma is later work; `opens/Pad.seg` pads
lists of opens and does not supply it.
