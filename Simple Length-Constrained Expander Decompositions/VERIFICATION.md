# Verification record

## Initial checkpoint — 10 October 2026

Three modules compiled successfully using the pinned Lean 4.34.0 binary (293d5d0c0c3f3dded4688b3ccd6a33939ac5102b) and pinned mathlib 5ed2965256430c3649e86755f9576b54eca72435:

- `LengthExpander.Demands`: finite directed demand budgets; corrected sparse-witness cost bound; ratio-of-sums bound.
- `LengthExpander.Metric`: actual graph-walk lengths; near/far semantics; monotonicity; applying and composing length-increase cuts; strict triangle separation; exact rescaling identity.
- `LengthExpander.SourceCorrections`: asymmetric demand versus symmetric edge counts, reciprocal incidence capacity, nonintegral half-unit, and two local algebraic counterexamples.

Compilation is not a full verification gate. Independent kernel replay, all-declarations dependency audit and exact-commit CI are still pending at this checkpoint. The Appendix A source-convention findings were independently reviewed against the complete PDF/HTML, including surrounding definitions. No main theorem is certified.

The companion's complete source reading edition, local styles and hiker interaction are drafted. JavaScript syntax passed; all 139 local anchor references resolve to unique IDs. Browser visual QA and Sites publication remain pending.

The original four active paper efforts remain independent and are not altered by this branch. Shared toolchain/dependency directories are reused read-only; all compilation uses one thread and the shared serialization lock.
