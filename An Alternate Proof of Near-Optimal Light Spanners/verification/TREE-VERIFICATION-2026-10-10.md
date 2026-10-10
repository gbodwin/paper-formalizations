# One-edge tree, MST, and lightness transfer — 2026-10-10

This extends the full-CI-verified checkpoint
`1e6c5775598ed3270e395a68a359112386acae6b`. Lean 4.34.0 and mathlib
`5ed2965256430c3649e86755f9576b54eca72435` are unchanged.

## New mathematical results

`SubdivisionTree.lean` adds actual graph-level reduction ingredients:

- Subdivision is monotone in the graph, preserves acyclicity of an actual
  forest edge, and preserves the spanning-tree property.
- Every edge-bounded walk lifts to an edge-bounded walk when both replacement
  pieces weigh at most the old edge. This is a bottleneck bound, separate from
  the existing total-walk-weight preservation theorem.
- A bottleneck-path certificate transfers when an edge of the tree is split
  into two nonnegative pieces of the same total weight. Combining this with
  the proved edge-exchange theorem establishes actual MST minimality in the
  subdivided graph.
- An exact finite-edge decomposition proves preservation of the total graph
  weight and total tree weight, and therefore exact preservation of lightness.
  The finite-sum and ratio equalities do not need positivity assumptions.

The MST transfer takes a bottleneck-certified tree, as supplied by the
existing Kruskal construction. It does not assume that the resulting tree is
minimal. The graph, tree, walk, and finite-sum conclusions are constructed and
proved, rather than accepted as interfaces for missing reductions.

## Verification

- Targeted `lake build LightSpanners`: passed, 17 source modules plus aggregate,
  1350 jobs (cached dependencies included).
- Every declaration in these modules: permitted-axiom audit passed, 247
  declarations including private/generated declarations.
- Selected axiom checks include the new MST and exact-weight theorems: passed.
- Independent sequential `leanchecker -v` replay: passed for all 17 source modules.
- Source import-index equality: 17 sources, 17 aggregate imports.
- `git diff --check`: passed before checkpoint publication.

Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. The targeted
logs prefixed `tree-2026-10-10-` record these checks. Exact-commit repository-wide
CI must be checked separately after publication.

## Remaining scope

This closes the one-edge tree/MST/lightness transfer. Full repeated heavy-edge
subdivision with an actual vertex-budget bound, Euler-tour vertex copying,
bucket-safe paths, dispersion, the light-spanner hiker suffix exchange,
truncation/deletion, independent edge sampling, and Theorem 5.1 remain open.
The separately verified weighted-girth transfer is nondecrease of lower
bounds, not an equality theorem for normalized weighted girth.
