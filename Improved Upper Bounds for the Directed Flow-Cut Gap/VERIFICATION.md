# Verification of this partial checkpoint

This checkpoint contains 162 Lean modules and their aggregate import file.
It is a partial formalization of arXiv:2604.03412v3. The main mathematical
rounding bounds are proved; full encoded algorithm composition and polynomial
bit complexity remain unfinished.

- Lean 4.34.0; mathlib 5ed2965256430c3649e86755f9576b54eca72435.
- All included modules have strict compilation receipts with autoImplicit=false
  and warningAsError=true.
- A fresh recursive audit checked all 10,328 unique owned declarations,
  permitting only propext, Classical.choice and Quot.sound.
- The exact unchanged 153-module baseline retains its source/object/kernel
  checks. All nine additions have fresh strict builds, exhaustive recursive
  owned-declaration audits, isolated official replays and independent semantic reviews.
- The 162-module aggregate separately passed compilation, recursive axiom audit,
  complete source-ownership enumeration and official root replay.
- Exact source hashes are in verification/component-verification.json.

New executed tests cover 4,092 binary word cases, 20,682 padded bounded-sampler
cases with complete source-state comparison, binary rational operations with
wide and zero inputs, 1,542 bounded logarithms, 131 exact epoch parameter cases,
2,080 positive dyadic-root cases, zero denominators and 128-bit inputs.

The controller's small exact-charge tests and terminal sampled-entry test
passed. Two larger instrumented nonterminal controller tests did not complete;
the separate sampled nonterminal execution test remains pending. The universal
full-Result refinements and charge inequalities are compiled and kernel checked.
These facts are kept distinct from execution tests and from the still-pending
binary, storage and address-cost realization. No claim about native Lean
interpreter performance or free evaluation of instrumentation is made.

The bounded sampler's legal-default failure bias is explicit. Its biased output
is never labelled exactly uniform; the outer probability composition must
account for failures.

The previous checked 153 commit 46f5a5777c70f1c03f09c5d026fb67239e802b8d passed
all CI stages in run 37931631063, including every project module's isolated
kernel replay. This commit's remote CI is a separate gate and must be checked
at its exact SHA.

From the repository root:

```sh
lake exe cache get
lake build DirectedFlowCutGap
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/AxiomAudit.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/KernelReplay.lean"
```

Public smoke drivers listed in component-verification.json can each be run with
lake env lean. Every component retains its stated boundary; complete full-paper
semantic and runtime verification remains open.
