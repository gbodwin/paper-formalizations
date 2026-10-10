# Initial checkpoint — 10 October 2026

Status: partial source checkpoint, not a main-result completion.

- Four modules have each compiled locally with Lean 4.34.0 and pinned mathlib.
- Actual seeded greedy correctness (Theorem 18), finite-fault graph semantics, minimum denominator existence and a finite Bernoulli repair are included.
- Aggregate root build, all-declaration allowed-axiom audit and independent kernel replay are queued under the shared single-thread compiler lock.
- Independent semantic review is running. No passed review is claimed yet.
- Exact-commit CI has not yet completed.
- Main upper/lower/runtime theorems, forest packing and multigraph extension remain open.
- Source hashes and the 37-item inventory are included. Source corrections are separately explained.
