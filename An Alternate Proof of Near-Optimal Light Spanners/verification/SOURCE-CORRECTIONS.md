# Source clarifications and repaired proof steps

These observations concern individual proof statements in
[the paper, arXiv v6](https://arxiv.org/html/2305.18647v6).
They do not refute the light-spanner theorem. The formalization records the
needed hypotheses and proves corrected statements.

## Section 3.2: rounding the subdivided MST

The normalization fixes the total MST weight to `n−1`; it does not bound each
individual tree edge below. Subdividing only edges heavier than one therefore
does not imply that every resulting tree edge has weight at least one half.

For example, take a triangle whose weights are `1/10, 19/10, 19/10`. Its MST
has weight `2 = n−1`; its weighted girth is `39/19 > 2`, so it is positive,
connected, and non-forest with a valid weighted-girth threshold. Subdividing
the chosen heavy MST edge replaces `19/10` by `19/20 + 19/20`. The other tree
edge still weighs `1/10 < 1/2`.

The required factor-two bound nevertheless follows from the global vertex
budget. All resulting tree edges have weight at most one. After rounding,
they form a unit-weight spanning tree. Since every graph edge now weighs at
least one, that tree is an MST and weighs exactly `n′−1`. The budget
`n′ ≤ 2n−1` then bounds this weight by `2(n−1)`. Graph weight cannot decrease
under rounding, so lightness falls by at most a factor of two.

`RoundingTree.lean` formalizes this repair:

- `tree_round_up_weight`: exact rounded tree weight;
- `round_up_isMinimumSpanningTree`: actual MST minimality after rounding;
- `round_up_lightness_ge_half`: global-budget factor-two lightness transfer;
- `normalized_round_up_lightness`: specialization to the normalized weights
  and the actual cardinality bound `card(V) ≤ 2n−1`.

No pointwise lower bound on old tree-edge weights appears in these theorems.
The actual cardinality bound is an input to the standalone rounding theorem.
`unit_tree_reduction_of_mst` in `TreeReduction.lean` now supplies it from a constructed
repeated subdivision, and combines the rounding theorem with scaling and
Kruskal. Thus the complete unit-MST stage no longer assumes that bound or the
post-subdivision graph. The Euler-tour spanning-cycle stage remains open.

## Lemma 3.7: distinguish chords from spanning-cycle edges

The strict bound obtained by adjoining an edge to the shorter spanning-cycle
arc applies to a chord. A cycle edge may coincide with the shorter arc, so
that union does not necessarily give a simple cycle.

The formal statement `UnitSpanningCycle.chord_weight_lt` therefore assumes
that the edge is not in the unit spanning cycle. For all edges,
`UnitSpanningCycle.edge_weight_le_max` supplies the bound
`max 1 (n / (2 * (g−1)))`. Unit cycle edges are handled by their known weight
one. This clarification predates the current continuation.
