# Verification of this partial candidate

This candidate contains 174 Lean modules and the aggregate import file.
It is a partial formalization of arXiv:2604.03412v3. Main mathematical rounding
bounds are proved in the checked baseline; the complete encoded algorithm,
probability and polynomial bit-runtime composition remain unfinished.

## Status at publication

All twelve new sources passed local strict compilation with autoImplicit=false
and warningAsError=true, and scoped independent source reviews. The 162-module
baseline at commit 2f3c83e2f3988e75a8800132004c9650a425368f passed the full
GitHub Actions run 37960050945, including every project module's kernel replay.
That baseline result is not a verification of these twelve additions together.

This is an explicitly pending candidate. The current verification status is
established by the GitHub Actions run for this exact commit, plus the following
source-specific gates. Until all those gates pass, do not call it verified.

- Clean full repository build under Lean 4.34.0 and mathlib
  5ed2965256430c3649e86755f9576b54eca72435.
- Complete module-index check, exhaustive recursive owned-declaration axiom
  audit allowing only propext, Classical.choice and Quot.sound, and isolated
  official kernel replay of every project module in that exact-commit CI run.
- Combined binary-cover execution test: sixteen padded input cases preserve
  every raw state field and event, all twelve stopping tests, and the displayed
  entry operation bound; the one-resource case retains post-stop guard scans.
- The unchanged signed-binary execution test already passed 4,624 padded
  arithmetic cases and 160-bit signed cancellation checks at the reviewed source hash.
- The unchanged storage execution test already passed its actual padded/empty
  copy, allocation, tabulation and callback-order examples at the reviewed hash.
- Independent semantic/source reconciliation for every added component.

The binary-cover execution test is pending at publication. The source hashes
are listed in verification/component-verification.json. This record makes no
claim about native Lean performance or free evaluation of instrumentation.
The actual graph oracle, full fixed-body runtime, edge-resource adapter,
weighted outer algorithm and efficient exact-W weak-decomposition construction
remain separate obligations.

## Reproduce the checks

From the repository root:

```sh
lake exe cache get
lake build
bash scripts/CheckModuleIndex.sh
lake env lean scripts/AxiomAudit.lean
bash scripts/KernelCheck.sh
lake env lean -DautoImplicit=false -DwarningAsError=true "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/BinaryCoverEntrySmoke.lean"
lake env lean -DautoImplicit=false -DwarningAsError=true "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/SignedBinarySmoke.lean"
lake env lean -DautoImplicit=false -DwarningAsError=true "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/StorageConstructorSmoke.lean"
```

Kernel replay in CI is used as the clean exact-source gate; an identical full
local replay is not required a second time. This does not remove either the
independent mathematical review or the source-specific execution checks.
