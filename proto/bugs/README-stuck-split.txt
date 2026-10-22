"refl ... does not prove Id V (extOb X id) (ExtV X id (full X id) (refl (full X id)))"

Reproduce: put proto/bugs/CExtL-stuck-split.seg in place of core/CExtL.seg and run `./segc core check CExtL`.
Probe in module EL.At.Cmp (marked PROBE):
  t1 : ExtT.tob X rho = CA.obD                   accepted (xsub -> SA.tob -> S0 -> CExtCmp.At.obD)
  t2 : CA.obD = E2.extOb X (idH X)               accepted (obD's ExtB2 instance vs E2, same arguments)
  t3 : E2.extOb X (idH X) = E2.ExtV X (idH X) (CA.DT.CL.full X (idH X)) (refl ...)   REJECTED
In CExt2.ExtB2, extOb X rho is by definition ExtV X rho (full X rho) (refl (full X rho)), where ExtV is a split on
Bool; the scrutinee full X (idH X) is stuck (allS of a sieve variable). So t3 is an unfolding of extOb, except that
`full` is written via CA.DT.CL = CCof.CofL[yP X, CExtU.psiD X ph] (from CExtU.XU.Dat) while ExtB2 uses the `full` it
opens from GP.CofL[G, psi] with the same G = yP X and psi = CExtU.psiD X ph.
So the two candidates are: (1) the two CofL instances' `full` are not identified, or (2) a stuck split applied to
equal arguments is not identified with its own unfolding. A tiny standalone with a split stuck on a variable,
reached through a nested module instance, is accepted, so (2) alone is not enough to trigger it.
Workaround used in core: CExt3.ExtB3.extOb-B / extOb-P (lemmas proved inside the instance), see core/CExtL.seg Cmp.

RESOLVED (seg-62, 2026-10-17): not a checker bug.  core/CExt4.seg:217 has
  opaque CExt2[l].ExtB2.extOb ;
so extOb is locked after its characterising lemmas (the opacity principle), and
t3 asks to unfold it.  Probes: a copy extOb' with the same body converts with
its unfolding; extOb does not.  The lemmas CExt3.ExtB3.extOb-B / extOb-P are
exactly the intended interface, so the "workaround" in core/CExtL.seg is the
right proof.
