# Worker A: closed subtypes

Completed. `closed/All.seg`: 3529 declarations, zero failures, 0.99 s.
Combined `closed/Section4.seg`: 3860 declarations, zero failures, 1.06 s.
See closed/README.txt and CHECKED.txt for statements and hypotheses.
All five steps below are implemented, including literal ideal equalities
in Lemma 1.3.8 and the quotient equivalence over Spec A in 4.1.4.

Own `closed/`; do not edit Worker B's files or the shared checker/libraries.
Read SEC4-INTERFACE.md and SEC3-INTERFACE.md.

Implement:
1. Localization kernel/denominator clearing for arbitrary algebra elements.
2. Finitely generated ideals with proposition-valued membership,
   extension, and extensional equality.
3. ClosedProp and SAG 4.1.2--4.1.3 from SQC and quotient certificates.
4. Ideal-membership denominator clearing and Lemma 1.3.8, without a
   covering assumption.
5. 4.1.4 using Z-choice, bounded lists of equations, SQC on localizations,
   and gluing.

Use only univalence and replacement as foundations, with geometric
axioms explicit. Check every module, without --only, in under five seconds.
Record exact statements and hypotheses, and do not commit.
