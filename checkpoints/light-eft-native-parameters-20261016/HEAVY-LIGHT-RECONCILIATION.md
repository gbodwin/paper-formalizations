# Preserved heavy/light proof and native bridge

Scope: static reconciliation of existing source at accepted evidence `743b63b81c0c5572d27664028f873a4014483289`, followed by NEW native counting proofs at `9cba496646e7a7c73513325b708cbfd0545a3133`. The preserved heavy/light closure was not freshly compiled or replayed. Exact source hashes are in `evidence/heavy-light-source-reconciliation.json`. No preserved proof body was edited.

## What the preserved proof actually establishes

`ConstructedExtremalSquareRoot.constructed_output_extremal_sqrt_bound` concerns a finite **simple graph**, real weights nonnegative everywhere and strictly positive on actual edges, an optimum seed at competition 2f, positive f/k/epsilon, and the simple-graph greedy output. It constructs doubled forest packing and uses `SeededExtremalForests.seeded_output_from_extremal_forests`, which splits the forests into their actual component trees and invokes the subtree heavy/light result. This is not an original-edge-ID multigraph theorem.

`ExtremalHeavyLight.subtree_extremal_heavy_light_bound` uses a fixed blocker family B and partitions nonseed candidates by the residual count `|(B e) minus Q| <= r`. On the heavy side the residual cap is r, the seed cap is f, and one unblocked host suffices. On the light side the residual count is greater than r, so the seed cap is at most f-r; congestion two leaves at least 2r+1 hosts. Sampling still uses residual cap f on that light side. `ExtremalAssignments.candidate_extremal_packing_bound` keeps seed cap b, multiplicity h, and residual sampling cap r as separate parameters. With r>0, r<=f and f<=r*(2r+1), the two weighted contributions each cost at most 8r*L times seed weight. The established square-root choice is r=Nat.sqrt f with those inequalities proved explicitly.

The simple proof's competitiveLightness is a totalized quotient. Its zero-seed branch uses division by zero; this alone is not a native zero-total-weight conclusion. The accepted native soundness checkpoint instead has a direct zero-weight preserver theorem. The native extension must retain that stronger treatment and nonnegative weights.

## What is now proved for native IDs

`NativeHeavyLightCounts` proves that host assignment is literally unchanged when the blocker set is intersected with the seed, provided the host's original IDs lie in the seed. Both cardinal and weighted host multiplicity therefore depend on the seed cap b independently of the residual sampling cap.

The heavy/light filtered weight identity partitions the finite set of original IDs exactly, without endpoint projection or duplicate charging. The light-side seed-cap inequality follows from the exact intersection/difference cardinality identity.

`native_traced_heavy_light_counts` chooses one actual `TracedBlockers` family for the existing native greedy trace at q=2f. Every nonseed selected ID has at least one unblocked forest. For each ID, either the residual cap is at most r, or its seed cap is at most f-r and its assignment has at least 2r+1 forests. The conclusion uses the same full blocker family as the cycle theorem. It does not discard seed blockers from cycle exclusion, simplify parallel IDs, or choose inconsistent blocker families per component.

## Precise remaining bridge

The current native `exists_sampled_component_host` takes a cap on the **full** blocker set and charges 4f times the sampled host. `native_assigned_component_bound` and `native_candidate_extremal_charge` likewise use the full candidate family and that cap. Replacing f by Nat.sqrt f in those statements is not justified by the new counting result.

A next native lemma must support a candidate subfamily U, a residual sample cap r, and the fixed original full blockers. Its sampler may use `block e minus H`, because U is outside H, but its output must remain disjoint from the original full blockers: seed blockers are excluded by host assignment, residual blockers by sampling. Actual selected-ID containment and the existing full-blocker cycle certificate must be preserved. Then the established native minimum-tree pruning and full-girth bound must be transported for that subfamily, retaining L+1. A generalized component/forest aggregate can combine separate seed cap b, multiplicity h and residual cap r. Only after those weighted lemmas are proved can the heavy and light bounds be combined and r=Nat.sqrt f justified.

This checkpoint proves the counting interface and the numerical parameter specialization. It does **not** prove the native square-root-f estimate or Theorem 11. The q=2f,h=1 specialization remains linear in f. The prior corrected stretch+1 threshold remains necessary; no new paper counterexample is asserted here.
