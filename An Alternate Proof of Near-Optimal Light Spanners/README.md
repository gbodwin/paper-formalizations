# An Alternate Proof of Near-Optimal Light Spanners

Initial Lean formalization of Greg Bodwin's paper, TheoretiCS 4 (2025), Article 2.
Source: https://arxiv.org/abs/2305.18647v6
DOI: https://doi.org/10.46298/theoretics.25.2

This package is partial. It does not yet prove Theorem 5.1 or the final lightness guarantee.
There are no `sorry` proofs, project axioms, or hidden assumptions standing in for the missing lemmas.

## Build

Run from the repository root. Lean 4.34.0 and the root mathlib revision are unchanged.

```sh
lake exe cache get
lake build LightSpanners
bash scripts/CheckModuleIndex.sh
lake env lean scripts/AxiomAudit.lean
bash scripts/KernelCheck.sh
```

## Correspondence to the paper

| Paper | Lean declaration | Scope |
|---|---|---|
| Definition 1.1 | `IsSpanner` | Every actual input graph walk has a replacement of at most t times its weight. This implies the usual finite positive-weight distance definition; equivalence to an explicit shortest-distance definition is not yet a Lean theorem here. |
| Algorithm 1 | `greedyEdges` | Exact noncomputable mathematical edge test, with real-valued stretch. |
| Algorithm 1 correctness | `greedy_isSpanner` | Subgraph and walk-stretch guarantees for the implemented algorithm, t >= 1 and nonnegative weights. |
| Definition 3.1 | `WeightedGirthAbove` | Every cycle has weight greater than g times the weight of each of its edges. For positive weights and g >= 0 this is equivalent to normalized weighted girth > g, and it is vacuously true for forests. |
| Lemma 3.2 | `greedy_weightedGirth` | The implemented greedy output has weighted girth > t+1. The cycle-complement and last-processed-edge arguments are proved on mathlib graph walks. Equal-weight ties are allowed. |
| Section 3.2 scaling | `normalized_scale` | Positive scaling preserves a normalized cycle ratio; the graph reduction itself remains unproved. |
| Lemma 5.5 arithmetic | `dyadic_sum`, `bucket_budget`, `dispersion_arithmetic` | Dyadic budget and normalized cycle-weight contradiction. Existence of the extracted cycle remains unproved. |
| Endpoint upper bound | `endpoint_count` | Endpoint injectivity implies at most n² paths. Injectivity for bucket paths is an explicit, unproved input. |
| Lemma 5.13 algebra | `sampling_bootstrap` | Rearrangement of the expectation identity; the probability space and counting input are unproved. |
| Final counting comparison | `counting_sandwich` | Explicit lower and upper path-count inequalities imply the normalized degree power bound. |
| Stretch reparameterization | `stretch_reparameterization` | With eta = eps(2k-1)/(8k), the target greedy weighted-girth threshold equals 2k(1+4eta). |

Graph edges are unordered vertex pairs `Sym2 V`, so weights are intrinsically undirected. All paths and cycles in the graph-theoretic results use mathlib `SimpleGraph.Walk`; `IsCycle` excludes repeated edges. The greedy input is a list processed tail-first; the theorem's pairwise descending-weight premise therefore specifies increasing processing order. The list can enumerate any finite simple graph.

## Remaining work, following the paper's outline

1. Prove MST containment by greedy and connect walk stretch to a shortest-distance API.
2. Formalize Lemma 3.5: scaling, subdivision, rounding and the spanning-cycle construction, preserving weighted girth and lightness up to constants. Define graph total weight and MST lightness.
3. Prove the graph-theoretic maximum-edge-weight bound (Lemma 3.7).
4. Define edge-safe and bucket-safe walks, balanced forward/backward cycle steps, extra-safety, and bucket-monotone concatenation. Empty bucket blocks must be allowed. Non-backtracking is imposed within a bucket, not on the entire concatenation.
5. Formalize Claim 2 and the extraction of a cycle containing an edge from the last differing bucket; apply the checked budget arithmetic to prove Lemma 5.5.
6. Formalize the dawn/morning/afternoon hiker protocol of Lemma 5.8, including suffix swaps, the occupancy invariant, cancellation, and integer rounding. Explicitly handle small buckets: the displayed floor estimate cannot be used without a suitable lower bound on its argument.
7. Prove the truncation/extension/deletion argument of Lemma 5.10 and distinctness of non-cycle edges (Claim 3).
8. Construct the independent edge-sampling probability space, prove survival probabilities and expectation bounds, and obtain Lemma 5.13.
9. Assemble Theorem 5.1 with explicit constants, then transfer it back to the target greedy lightness result. Optional warmups (§2 and §4) can reuse the same counting infrastructure.

The current arithmetic lemmas are helpers for these steps, not substitutes for their combinatorial hypotheses. In particular no declaration named as the main lightness theorem is present.

## Validation and provenance

The logs in `verification/` record local verification. The all-declarations audit rejects any axiom outside `propext`, `Classical.choice`, and `Quot.sound`.

Normal compilation succeeded for all modules, and all 49 project declarations passed the axiom audit. Separate `leanchecker` replay succeeded for `Basic`, `Greedy`, and `Counting`. An earlier runtime error reported during verification was resolved by an isolated successful replay of `Counting` before publication. These checks verify the stated partial scope, not the complete paper.

The graph-walk utilities adapt the same conventions as the existing VFTSpanners package in `gbodwin/paper-formalizations`; this package has no dependency on that paper's modules. Code follows that repository's MIT license. The mathematical paper is CC BY 4.0.

## Repository integration

`LightSpanners` is included in the root Lake default build, the module-index check, the all-declarations axiom audit, and the per-module kernel replay. Existing paper modules and the pinned dependency versions are preserved.
