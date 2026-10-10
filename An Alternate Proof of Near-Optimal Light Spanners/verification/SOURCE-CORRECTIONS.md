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
post-subdivision graph. `unit_spanning_cycle_reduction_of_mst` in
`CycleReduction.lean` also constructs the subsequent spanning-cycle stage,
completing Lemma 3.5 with explicit constants `4n−4` and one-quarter lightness.

## Lemma 3.7: distinguish chords from spanning-cycle edges

The strict bound obtained by adjoining an edge to the shorter spanning-cycle
arc applies to a chord. A cycle edge may coincide with the shorter arc, so
that union does not necessarily give a simple cycle.

The formal statement `UnitSpanningCycle.chord_weight_lt` therefore assumes
that the edge is not in the unit spanning cycle. For all edges,
`UnitSpanningCycle.edge_weight_le_max` supplies the bound
`max 1 (n / (2 * (g−1)))`. Unit cycle edges are handled by their known weight
one. This clarification predates the current continuation.


## Lemma 5.8: subunit shuttle budgets

The displayed estimate `2 floor(x) ≥ x`, used with `x=εk2^(i−1)`, is false
for `0<x<1`. In that range the stated protocol has no shuttle positions at
which to insert a chord, so its claimed positive per-chord traversal lower
bound does not follow.

The formal proof repairs the construction. Before any shuttle move, process
all bucket chords once by endpoint transpositions. Then repeat a forward
shuttle move followed by a full chord layer `t=floor(x)` times. There are
`t+1` chord layers but only `t` forward moves. After backward completion and
cancellation of the terminal forward-only suffix, each walk is extra-safe,
its endpoint is a permutation of the morning endpoint, and every chord
traversal is preserved. The exact squad count is `2(t+1)|B_i|`, including
`t=0`. The elementary inequality `floor(x)+1>x` gives the required
`εk w(e)/4` lower bound without a lower bound on x.

`HikerSquads`, `HikerLayers`, `HikerCompletion`, `HikerDay`, and `HikerTour`
construct these actual walks and count them. `DyadicEnumeration` constructs
the finite bucket family from all graph chords. `UnitSpanningCycle.weak_counting`
in `WeakCounting.lean` completes Lemma 5.8 under
its stated positive-ε and positive-integer-k assumptions. The original safety
budget k is retained when the produced walk contains k′≥k chords.
The subsequent medium and sampling counting lemmas now use this constructed weak-counting result.


## Theorems 4.1 and 5.1: finite-uniform epsilon domain

Theorem 5.1 states epsilon>0 without an upper restriction and displays
O(epsilon^(-1)n^(1+1/k)). A constant uniform in epsilon,n,k cannot hold in
that form: take the actual unit n-cycle, k=2, epsilon=n/32, and n>8. Its
weighted girth is n>4+n/2, its total weight is n, and its ratio to the
displayed scale is sqrt(n)/32, which is unbounded. For Theorem 4.1 take
epsilon=n/16; the ratio to its displayed k/epsilon scale is again sqrt(n)/32.

`LightSpanners.no_uniform_all_epsilon_bound` and
`no_uniform_warmup_epsilon_bound` construct these actual cycle counterexamples
for every proposed constant. This concerns the finite-uniform reading only.
Fixed-epsilon asymptotics with epsilon-dependent thresholds and the explicitly
O_epsilon formulation of Theorem 1.4 are unaffected.

The formalized finite-uniform repair is
`UnitSpanningCycle.unit_cycle_weight_bound`:

    w(H) <= n + (8/epsilon) n n^(1/k).

For 0<epsilon<=1, `unit_cycle_weight_bound_small_epsilon` gives the usual
no-baseline form with constant 9. After the actual graph reduction and stretch
reparameterization, the unrestricted main theorem has coefficient
8+2048/epsilon multiplying n^(1/k). No hidden epsilon<=1 premise enters it.
