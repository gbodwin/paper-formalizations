# Current upper-bound coverage

Checkpoint 185 locally proves and component-reviews the sparsity upper. Full
exact-commit CI follows publication; whole-paper audit is not yet eligible.

| Source item | Actual Lean result | Domain / remaining scope |
|---|---|---|
| Theorem 9 | full_density_witness, fullDensityLoss_polylog | Positive edge density, finite nonempty host, h>0; actual induced witness and explicit degree-nine logarithmic loss. |
| Lemma 16 | girth_minor_free_edge_bound | Finite simple graph, r>=1, h>0, actual girth and clique-minor exclusion; no witness oracle. |
| Theorem 13 / sparsity half of Theorem 6 | greedy_minor_free_sparsity | Actual sorted-edge greedy output,positive real weights,stretch 2r-1,uniform polylog sparsity. |
| Lightness half of Theorem 6 | OPEN | Actual clustering hierarchy and charging joins still required. |

The constructions select finite mathematical objects classically; no runtime
claim is inferred. The explicit coefficient is large but independent of the
stretch integer. The h=1 and empty/edgeless domains are handled by the actual
theorems, rather than suppressed in asymptotic notation. Prior source corrections
and all article annotations are unchanged.

## Actual high-degree lightness phase (193)

`exists_weighted_high_degree_phase` constructs actual radius-two quotient groups,
weighted original-host branch unions and a conserved reserve/payment inequality
for every original marked edge. Its graph density bound and quotient girth are
derived internally. This is one phase, with an explicit previous-level cluster
family and numeric scale/credit inequalities. The remaining initialization,
low-degree, absorption and global charging obligations are open.

## Actual unit-tree initialization (201)

`initial_unit_tree_phase` constructs all initial branches and their credit
budgets from an actual connected unit-weight tree. Whole residual components
attach to internally selected connected cores. All original vertices are covered,
and each actual internal tree edge contributes credit at most once. The small-tree
case is explicit. Low-degree/path phases, absorption and global charging remain.

## Actual low-degree branching phase (217)

`exists_weighted_branching_phase` constructs the actual residual forest and
disjoint branching cores, lifts their supported paths and pays every original
heavy edge incident to each selected new branch. The old family covers all
host vertices explicitly. Chosen original unit connectors are distinct and
fresh relative to every old internal edge. `branching_phase_conservation`
pools actual old credits and connector weights without duplication. The
large-residual degree-at-most-two conclusion concerns the chosen forest.
Path-only residuals, absorption, deferred edges and global charging remain.

## Actual four-arm path phase (227)

`exists_weighted_four_arm_phase` constructs actual threshold arms, a finite
maximum disjoint carrier family and original-host supported cluster paths.
It pays every incident original heavy edge while retaining cb/2, under the
explicit scale inequalities. The residual excludes heavy edges joining far
centers of disjoint original paths. Same-path short-cycle cases, absorption,
deferred edges and global multilevel charging remain open in this checkpoint.
