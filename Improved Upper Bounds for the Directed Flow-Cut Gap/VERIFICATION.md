# Verification gates for the pending 193-component candidate

Lean: 4.34.0. Mathlib: 5ed2965256430c3649e86755f9576b54eca72435.
Only propext, Classical.choice and Quot.sound are allowed axioms.

The previously verified 174-component source is commit
fc11ede6a4c581c35163dba0698128057895c34d, CI 38011321856. It passed the clean
repository build, module-index checks, recursive audit of 11,053 owned
declarations, every component kernel replay, binary-cover execution and final
independent source reconciliation. Its import-only root was built and indexed;
a separate root replay is not inferred from that historical run.

This candidate adds nineteen components. Fourteen have standalone strict
compilation results. The final five graph-bound/cost components completed
development elaboration with zero diagnostics; this is not standalone build
verification. No aggregate pass is asserted at publication.

Required gates for this exact candidate:

- Clean full repository build and complete module index.
- Exhaustive recursive audit of all owned declarations under the allowed axioms.
- Official kernel replay of every component, with explicit replay output.
- Existing binary-cover regression: sixteen complete input states and a
  stopped-state case, retaining events, stopping scans and charge checks.
- Weighted regression: 125 integer-mass lists, 64 rational triples and 1,032
  padded binary draws, empty/zero/duplicate/out-of-range inputs, five wide
  80-bit/129-padding cases, and four actual varying-oracle packing traces.
- Independent exact-source semantic reconciliation. The six new finite-data
  routines and binary graph execution also require their dedicated execution
  checks before the candidate can be promoted.

Reproduce from the repository root:

```sh
lake exe cache get
lake build
bash scripts/CheckModuleIndex.sh
lake env lean scripts/AxiomAudit.lean
bash scripts/KernelCheck.sh
lake env lean -DautoImplicit=false -DwarningAsError=true "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/BinaryCoverEntrySmoke.lean"
lake env lean -DautoImplicit=false -DwarningAsError=true "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/WeightedCombinedSmoke.lean"
```

These are source-specific mathematical and execution checks. They do not
establish the still-unfinished full paper, native compiler/allocator correctness,
or an unproved substitution of word operations by binary operations. Exact CI
may discharge aggregate gates without an identical full local replay.
