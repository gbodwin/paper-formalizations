# Actual unit-MST reduction — 2026-10-10

This extends full-CI-verified checkpoint
`4a9fed240dbd94e81de5ffae9358b8701be3db8b`. Lean 4.34.0 and mathlib
`5ed2965256430c3649e86755f9576b54eca72435` are unchanged.

## New graph-level milestone

`unit_tree_reduction_of_mst` completes the unit-MST half of Lemma 3.5 for a
finite positive-weight non-forest graph, a nonnegative weighted-girth
threshold, and an explicit reference MST (with at least two vertices).
It constructs an actual finite graph and actual MST with:

- at most `2n−1` vertices;
- all graph edges of weight at least one;
- all tree edges of weight exactly one;
- a preserved weighted-girth lower bound;
- a non-forest output graph;
- lightness at least half the original lightness.

The conclusion is existential over an actual vertex type, its finite
instance, graphs, and weights. No post-subdivision graph, path family,
cardinality bound, normalization, or bottleneck certificate is assumed by
the final theorem.

## Proof components

Kruskal constructs a bottleneck-certified spanning tree of the input graph.
MST-weight independence relates its lightness to the supplied reference MST.
Positive scaling normalizes its tree weight to `n−1`.

The integer potential is the sum of `ceil(w(e))−1` over the tree edges.
Splitting a heavy edge into a first piece `w/ceil(w)` and the positive
remainder strictly decreases this potential. Each actual `Option`-vertex
subdivision adds one vertex. Strong induction constructs the repeated
subdivision and proves its vertex bound; the potential is bounded by the
normalized tree weight even for arbitrarily light old tree edges.

One-edge graph/tree weight preservation and weighted-girth transfer compose
through the recursion. Positivity and strict subgraph-weight comparison
preserve the non-forest condition. Finally, global cardinality controls the
rounded unit MST's weight. This is the repaired rounding argument documented
in `SOURCE-CORRECTIONS.md`.

## Checks

- `lake build LightSpanners`: passed, 19 source modules plus aggregate,
  1352 jobs including cached dependencies.
- All-declarations permitted-axiom audit: passed, 282 declarations, including
  private/generated declarations.
- Selected axiom audit includes the final unit-MST theorem: passed.
- Sequential independent `leanchecker -v` replay: passed for all 19 source modules.
- Module index: 19 sources, 19 aggregate imports.
- `git diff --check`: passed before publication.

Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Logs
prefixed `unit-tree-2026-10-10-` record the local gate. Repository-wide CI is
checked separately for the exact published commit.

## Still open

The unit-MST stage is complete within the hypotheses above. The Euler-tour
vertex-copy construction producing a unit spanning cycle, bucket-safe paths,
dispersion, hiker suffix exchange, truncation/deletion, edge sampling, and the
final lightness theorem remain unproved. The reduction preserves girth lower
bounds; no equality of normalized weighted girth is claimed.
