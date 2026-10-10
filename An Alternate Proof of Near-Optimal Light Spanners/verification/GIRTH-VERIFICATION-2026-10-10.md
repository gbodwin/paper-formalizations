# One-edge weighted-girth transfer — 2026-10-10

This extends the independently verified cycle-contraction checkpoint
`6d98b7359b7885c96309d31aa1332aae596879a5`. Lean 4.34.0 and mathlib
`5ed2965256430c3649e86755f9576b54eca72435` are unchanged.

## New mathematical result

`WeightedGirthAbove.subdivideEdge` proves an actual graph-level transfer:
if an original graph has weighted girth above a nonnegative threshold `g`,
and an edge is replaced by two nonnegative-weight edges with the same total
weight, the explicitly constructed subdivision also has weighted girth above
`g`. It handles arbitrary simple cycles, including cycles through the newly
inserted vertex. No finite-graph assumption is needed.

For cycles avoiding the new vertex, the old-graph embedding preserves edge
weights and cycle weights. For cycles through it, the contraction produces
an actual old cycle; each new piece weighs at most the old edge, and all old
edges retain their weights. Rotation handles cycles with other basepoints.
The proof reuses the checked cycle and walk constructions. It does not assume
the weighted-girth conclusion or insert an arithmetic-only replacement for
cycle extraction.

This proves nondecrease of lower bounds, not equality of normalized weighted
girth. Full repeated subdivision, tree/minimum-weight/lightness transfer,
Euler-tour vertex copying, bucket-path dispersion and counting, edge sampling,
and the final lightness theorem remain unproved.

## Checks completed on the corrected source

- `lake build LightSpanners`: passed, 16 source modules plus aggregate, 1349 jobs.
- All-declarations permitted-axiom audit: passed, 221 declarations including generated/private declarations.
- Selected axiom audit includes `WeightedGirthAbove.subdivideEdge`: passed.
- Sequential independent `leanchecker -v` replay: passed for all 16 source modules.
- Source import-index equality: all 16 module files match the aggregate imports.
- `git diff --check`: passed.

Only `propext`, `Classical.choice`, and `Quot.sound` are permitted by the audit;
no project axiom or `sorryAx` is allowed. Logs prefixed `girth-2026-10-10-` record
the targeted checks. Repository-wide GitHub Actions must be checked for the
exact corrected commit independently of these local checks.
