# Verification of this partial checkpoint

This checkpoint contains 153 Lean modules and their aggregate import file.
It is a partial formalization of arXiv:2604.03412v3. The main mathematical
rounding bounds are proved, while complete algorithmic composition and
polynomial bit complexity remain unfinished.

- Lean 4.34.0; mathlib 5ed2965256430c3649e86755f9576b54eca72435.
- All included modules compile with autoImplicit=false and warningAsError=true.
- A fresh recursive audit checked all 9,789 unique owned declarations,
  permitting only propext, Classical.choice and Quot.sound.
- The exact unchanged 130-module baseline retains its source/object/kernel
  checks. All 23 additions have fresh strict builds, recursive owned-declaration
  audits, isolated official LeanChecker replays and independent semantic reviews.
- The 153-module aggregate separately passed compilation, recursive axiom audit,
  complete source-ownership enumeration and official root replay.
- Exact source hashes are recorded in verification/component-verification.json.

The new substantive execution tests cover actual raw graph-cover updates and
objective guesses, original-input weighted preparation, uniform chain and heavy
residual masks, binary arithmetic and long division, and full-state monadic bit
sampling. The bounded sampler includes its intentional legal-default bias;
no biased output is called exactly uniform.

The previous checked 130 commit b4454f60a78e9163aa6e9228a1403535c7509af7 passed
all CI stages in run 37917912734. This commit's remote CI is a separate gate and
must be checked at its exact SHA.

Reproduce the library and exhaustive checks from the repository root:

```sh
lake exe cache get
lake build DirectedFlowCutGap
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/AxiomAudit.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/KernelReplay.lean"
```

The additional public smoke drivers listed in component-verification.json can
each be run with lake env lean. Boolean/list instruction counts are explicit
component models. They do not assert native Lean interpreter performance or
complete the pending logarithmic-cost RAM composition.
