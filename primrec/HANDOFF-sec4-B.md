# Worker B: open subtypes

Own a new directory for Section 4.2; Worker A owns `closed/`.
Read SEC4-INTERFACE.md and SEC3-INTERFACE.md before fixing interfaces.
Do not edit Worker A's files, the checker, or shared dependencies.

Implement Proposition 2.2.3(b),(c), then 4.2.1--4.2.11.
Reuse `closed/ClosedProp.seg` for closed propositions. Put the new
2.2.3(b),(c) proofs in your directory and record their callable interface.

For (b), nonzero means not all coordinates vanish, and “some coordinate”
means truncated existence; use R/(x_i), certificates, and Loc.
For (c), use the checked localization-nilpotence theorem and 2.2.3(a).

For transitivity, first prove the affine case of 4.2.8, then 4.2.9(a)
using Spec R, and 4.2.9(b) pointwise. This proves the statement needed for
schemes without waiting for a scheme definition.

Shared geometric axioms: SAGAxioms in affine/. No additional foundational
axioms or implicit choice. Link dependencies read-only. Test under five
seconds per file, report exact hypotheses, and do not commit.
Keep documentation in your own directory until integration.
