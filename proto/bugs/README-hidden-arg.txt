"hidden argument N of transH was found, but it cannot be written in this scope: no name for ..."

Reproduce: put proto/bugs/CDNormD-hidden-arg.seg in place of core/CDNormD.seg and run `./segc core check CDNormD`.
coreG fails at `transH (fill-cong ...) (low.2.2 ...)`. That code checks unchanged in seg/model/DNormD.seg.

The inferred hidden argument is the type GPre.TyL.EI{...} of the Delta instance CB[...] (core/CDeltaBase.seg, module DB).
That instance is applied to LAMBDA arguments, e.g. `\ n m -> homV (lin n) (lin m)`. The checker then finds no name
for the instance's types inside the hidden argument. All recurring cases (CPosEl5, CPosFinal, CSmallFull3) also
involve a CB instance or module applied to lambdas, e.g. CG/CC with `\ W v -> refl ...` arguments.

Workaround: give the hidden argument explicitly (transH {KA.TS.EI (suc N')} ...), or use calc.

Finding (CDNormD): what matters is a NAMED ALIAS for the module instance in scope. CDNormD reaches KA only
through chains of opens (open NCm ; open NBm ; open SAm). Adding
  module SAx = CDStageA[a, lz].SA[G, A, e] ; module KTSx = SAx.KA.TS ; module KPEx = SAx.KA.TS.PE ;
fixed every failure. It also removed a 10 s overrun in degI, so the failed write-back seems to cost time as well.
The checker apparently writes back only through aliases declared in scope, not through names reached by `open`.
