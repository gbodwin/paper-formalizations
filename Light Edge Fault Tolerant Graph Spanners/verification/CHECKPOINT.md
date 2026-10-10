# Initial checked components — 10 October 2026, 18:19 UTC

Status: partial proof checkpoint, not a main-result completion.

- Four modules and their aggregate root compile with Lean 4.34.0 and pinned mathlib.
- All 65 declarations, including generated/private declarations, pass the allowed-axiom check (propext, Classical.choice, Quot.sound only).
- All four modules pass separate leanchecker kernel replay. The module index passes.
- Independent hash-pinned semantic review passes. See INITIAL_SEMANTIC_REVIEW.md.
- Actual seeded greedy correctness (Theorem 18), finite-fault graph semantics, minimum denominator existence and the finite Bernoulli 1/(4f) survival repair are included.
- Initial exact CI is running for commit 1d0f4662ebd8ca22ca1c681180c2ca27b689919b: https://github.com/gbodwin/paper-formalizations/actions/runs/38075175713 . This documentation/audit-helper repair successor still requires its own exact CI.
- The initial standalone audit helper had an elaboration typo; it is corrected here and the complete local gate rerun passed. The main repository audit uses a separate correctly configured checker.
- Main upper/lower/runtime theorems, forest packing, actual graph-weight sampling assembly and multigraph extension remain open.
