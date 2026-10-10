# Exact statement coverage and main-result scope

Source: [arXiv 2305.18647v6](https://arxiv.org/html/2305.18647v6).
This inventory covers all 52 displayed theorem/definition/claim/proof/solution blocks.
It does not equate end-to-end main-result verification with literal verification of
all unused exposition or cited background. The machine-readable companion is
`statement-coverage.json`.

The final theorem constructs an actual stretch-(1+epsilon)(2k−1) spanner with
lightness at most (8+2048/epsilon)n^(1/k), for every epsilon>0 and integer k≥1,
on a finite connected graph with positive edge weights. The source's Definition
1.3 footnote explicitly permits assuming connectivity for its MST convention.
Disconnected minimum-spanning-forest assembly is not included. Singleton inputs
are covered using Lean's totalized zero division convention. The greedy theorem
uses globally nonnegative weights; the existence wrapper internally extends
arbitrary off-graph weights by max(w,0) and transfers all actual-edge quantities.
It does not assert definitional equality of two differently extended greedy runs.

The unrestricted finite-uniform auxiliary bound retains +n. Its usual no-baseline
form is proved for epsilon≤1. This preserves the source's explicitly O_epsilon
main theorem; the counterexample concerns a constant uniform over all epsilon,n.
See `SOURCE-CORRECTIONS.md` for four detailed source repairs.

All listed Lean declarations have compiled under autoImplicit=false. Aggregate
axiom/kernel checks, exact-commit CI and a fresh independent skeptical end-to-end
audit are recorded separately in `MAIN-RESULT-VERIFICATION-2026-10-10.md`.

| Source block | Status | Lean correspondence / scope |
|---|---|---|
| [Definition 1.1 (Spanners [26, 25]).](https://arxiv.org/html/2305.18647v6#S1.Thmtheorem1) | proved | `isSpanner_iff_distance`. Positive stretch; nonnegative weights, including disconnected pairs. |
| [Theorem 1.2 ([3]).](https://arxiv.org/html/2305.18647v6#S1.Thmtheorem2) | not claimed | `—`. Cited sparsity theorem and conditional tightness are outside this main-result package. |
| [Definition 1.3 (Spanner Lightness).](https://arxiv.org/html/2305.18647v6#S1.Thmtheorem3) | defined and validated | `lightness; lightness_mst_independent`. Explicit reference MST; tied MSTs give the same denominator. |
| [Theorem 1.4 ([13]).](https://arxiv.org/html/2305.18647v6#S1.Thmtheorem4) | proved in connected-MST domain | `near_optimal_greedy_spanner; near_optimal_greedy_lightness; exists_near_optimal_spanner`. Actual greedy output for globally nonnegative weights; positivity only on actual edges for the existence wrapper. Disconnected MSF assembly and conditional lower-bound tightness are not claimed. |
| [Theorem 2.1 (Moore Bounds).](https://arxiv.org/html/2305.18647v6#S2.Thmtheorem1) | not separately formalized | `—`. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Lemma 2.2 (Unweighted Dispersion Lemma).](https://arxiv.org/html/2305.18647v6#S2.Thmtheorem2) | not separately formalized | `—`. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Proof 2.3.](https://arxiv.org/html/2305.18647v6#S2.Thmtheorem3) | not separately formalized | `—`. Proof associated with the preceding statement. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Lemma 2.4 (Unweighted Weak Counting Lemma).](https://arxiv.org/html/2305.18647v6#S2.Thmtheorem4) | not separately formalized | `—`. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Proof 2.5.](https://arxiv.org/html/2305.18647v6#S2.Thmtheorem5) | not separately formalized | `—`. Proof associated with the preceding statement. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Lemma 2.6 (Unweighted Medium Counting Lemma).](https://arxiv.org/html/2305.18647v6#S2.Thmtheorem6) | not separately formalized | `—`. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Proof 2.7.](https://arxiv.org/html/2305.18647v6#S2.Thmtheorem7) | not separately formalized | `—`. Proof associated with the preceding statement. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Lemma 2.8 (Unweighted Full Counting Lemma).](https://arxiv.org/html/2305.18647v6#S2.Thmtheorem8) | not separately formalized | `—`. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Proof 2.9.](https://arxiv.org/html/2305.18647v6#S2.Thmtheorem9) | not separately formalized | `—`. Proof associated with the preceding statement. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Definition 3.1 (Normalized Weight and Weighted Girth [15]).](https://arxiv.org/html/2305.18647v6#S3.Thmtheorem1) | defined and validated | `weightedGirthAbove_iff_normalized`. Positive graph weights; nonnegative threshold. |
| [Lemma 3.2 ([15]).](https://arxiv.org/html/2305.18647v6#S3.Thmtheorem2) | proved | `greedy_weightedGirth; greedyOutput_preliminaries`. Actual sorted greedy output, including equal-weight ties. |
| [Proof 3.3.](https://arxiv.org/html/2305.18647v6#S3.Thmtheorem3) | proved | `greedy_weightedGirth; greedyOutput_preliminaries`. Proof associated with the preceding statement. Actual sorted greedy output, including equal-weight ties. |
| [Definition 3.4 (Unit-Weight Spanning Cycles).](https://arxiv.org/html/2305.18647v6#S3.Thmtheorem4) | defined and constructed | `UnitSpanningCycle`. Actual oriented Hamiltonian cycle, cycle weights one, all graph-edge weights at least one. |
| [Lemma 3.5.](https://arxiv.org/html/2305.18647v6#S3.Thmtheorem5) | proved with corrected rounding | `unit_spanning_cycle_reduction_of_mst`. Actual graph with at most 4n−4 vertices and at least quarter lightness; positive nonforest input and reference MST. |
| [Proof 3.6.](https://arxiv.org/html/2305.18647v6#S3.Thmtheorem6) | proved with corrected rounding | `unit_spanning_cycle_reduction_of_mst`. Proof associated with the preceding statement. Actual graph with at most 4n−4 vertices and at least quarter lightness; positive nonforest input and reference MST. |
| [Lemma 3.7.](https://arxiv.org/html/2305.18647v6#S3.Thmtheorem7) | corrected chord statement proved | `UnitSpanningCycle.chord_weight_lt; edge_weight_le_max`. Strict source bound applies to chords; all edges need max with one. |
| [Proof 3.8.](https://arxiv.org/html/2305.18647v6#S3.Thmtheorem8) | corrected chord statement proved | `UnitSpanningCycle.chord_weight_lt; edge_weight_le_max`. Proof associated with the preceding statement. Strict source bound applies to chords; all edges need max with one. |
| [Theorem 4.1 (Warmup).](https://arxiv.org/html/2305.18647v6#S4.Thmtheorem1) | uniform-epsilon source correction proved; warmup proof not reproduced | `no_uniform_warmup_epsilon_bound`. Actual unit-cycle family refutes a finite constant uniform over all epsilon. Fixed-epsilon reading is not refuted. Main stronger counting route suffices for the main result. |
| [Definition 4.2 (Edge-Safe Paths).](https://arxiv.org/html/2305.18647v6#S4.Thmtheorem2) | not separately formalized | `—`. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Claim 1.](https://arxiv.org/html/2305.18647v6#Thmthm1) | not separately formalized | `—`. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Proof 4.3.](https://arxiv.org/html/2305.18647v6#S4.Thmtheorem3) | not separately formalized | `—`. Proof associated with the preceding statement. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Definition 4.4 (Safe k-Paths).](https://arxiv.org/html/2305.18647v6#S4.Thmtheorem4) | not separately formalized | `—`. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Definition 4.5 (Monotone Safe k-Paths).](https://arxiv.org/html/2305.18647v6#S4.Thmtheorem5) | not separately formalized | `—`. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Lemma 4.6 (Monotone Dispersion Lemma).](https://arxiv.org/html/2305.18647v6#S4.Thmtheorem6) | not separately formalized | `—`. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Proof 4.7.](https://arxiv.org/html/2305.18647v6#S4.Thmtheorem7) | not separately formalized | `—`. Proof associated with the preceding statement. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Solution 4.8.](https://arxiv.org/html/2305.18647v6#S4.Thmtheorem8) | not separately formalized | `—`. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Lemma 4.9 (Warmup Weak Counting Lemma).](https://arxiv.org/html/2305.18647v6#S4.Thmtheorem9) | not separately formalized | `—`. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Proof 4.10.](https://arxiv.org/html/2305.18647v6#S4.Thmtheorem10) | not separately formalized | `—`. Proof associated with the preceding statement. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Lemma 4.11 (Warmup Medium Counting Lemma).](https://arxiv.org/html/2305.18647v6#S4.Thmtheorem11) | not separately formalized | `—`. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Proof 4.12.](https://arxiv.org/html/2305.18647v6#S4.Thmtheorem12) | not separately formalized | `—`. Proof associated with the preceding statement. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Lemma 4.13 (Warmup Full Counting Lemma).](https://arxiv.org/html/2305.18647v6#S4.Thmtheorem13) | not separately formalized | `—`. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Proof 4.14.](https://arxiv.org/html/2305.18647v6#S4.Thmtheorem14) | not separately formalized | `—`. Proof associated with the preceding statement. Unused unweighted/warmup exposition; no literal full-paper coverage claim. |
| [Theorem 5.1 (Main Theorem).](https://arxiv.org/html/2305.18647v6#S5.Thmtheorem1) | repaired finite-uniform form proved | `UnitSpanningCycle.unit_cycle_weight_bound; unit_cycle_weight_bound_small_epsilon`. For all epsilon>0: weight ≤ n+(8/epsilon)n*n^(1/k). For epsilon≤1: weight ≤(9/epsilon)n^(1+1/k). no_uniform_all_epsilon_bound proves necessity of the baseline under uniform quantification. |
| [Definition 5.2 (Bucket-Safe Paths).](https://arxiv.org/html/2305.18647v6#S5.Thmtheorem2) | defined | `BucketWalk; BucketSafe; BucketExtraSafe`. Actual forward/backward cycle darts and half-open dyadic chord buckets; empty chord blocks are proved nil. |
| [Claim 2.](https://arxiv.org/html/2305.18647v6#Thmthm2) | proved | `BucketSafe.unique_of_chordDarts`. Equal oriented chord words and common terminal vertex identify actual walks, allowing different starts/bucket indices. |
| [Proof 5.3.](https://arxiv.org/html/2305.18647v6#S5.Thmtheorem3) | proved | `BucketSafe.unique_of_chordDarts`. Proof associated with the preceding statement. Equal oriented chord words and common terminal vertex identify actual walks, allowing different starts/bucket indices. |
| [Definition 5.4 (Bucket-Monotone Safe k-Paths).](https://arxiv.org/html/2305.18647v6#S5.Thmtheorem4) | defined | `BucketMonotoneWalk; BucketMonotoneKPath`. Empty blocks and boundary backtracking are permitted as in the source. |
| [Lemma 5.5 (Dispersion Lemma).](https://arxiv.org/html/2305.18647v6#S5.Thmtheorem5) | proved | `BucketMonotoneKPath.unique`. Actual endpoint uniqueness; no supplied dispersion or cycle-extraction oracle. |
| [Proof 5.6.](https://arxiv.org/html/2305.18647v6#S5.Thmtheorem6) | proved | `BucketMonotoneKPath.unique`. Proof associated with the preceding statement. Actual endpoint uniqueness; no supplied dispersion or cycle-extraction oracle. |
| [Solution 5.7.](https://arxiv.org/html/2305.18647v6#S5.Thmtheorem7) | construction subsumed, puzzle not separately encoded | `WalkSquad; HikerDay; HikerTour`. Actual graph hiker protocol proves the needed invariant; informal puzzle vocabulary has no separate theorem. |
| [Lemma 5.8 (Weak Counting Lemma).](https://arxiv.org/html/2305.18647v6#S5.Thmtheorem8) | proved with corrected floor protocol | `UnitSpanningCycle.weak_counting`. Constructs buckets and hikers internally; t+1 chord layers, t shuttles, original ambient safety budget k. |
| [Proof 5.9.](https://arxiv.org/html/2305.18647v6#S5.Thmtheorem9) | proved with corrected floor protocol | `UnitSpanningCycle.weak_counting`. Proof associated with the preceding statement. Constructs buckets and hikers internally; t+1 chord layers, t shuttles, original ambient safety budget k. |
| [Lemma 5.10 (Medium Counting Lemma).](https://arxiv.org/html/2305.18647v6#S5.Thmtheorem10) | proved with explicit constant | `UnitSpanningCycle.medium_counting`. Actual retained graph, truncation, useful padded family and deletion induction: endpoint count ≥ epsilon*offcycleWeight/4−n. |
| [Proof 5.11.](https://arxiv.org/html/2305.18647v6#S5.Thmtheorem11) | proved with explicit constant | `UnitSpanningCycle.medium_counting`. Proof associated with the preceding statement. Actual retained graph, truncation, useful padded family and deletion induction: endpoint count ≥ epsilon*offcycleWeight/4−n. |
| [Claim 3.](https://arxiv.org/html/2305.18647v6#Thmthm3) | proved | `BucketMonotoneKPath.chordEdges_nodup`. Exactly k distinct actual chord edges, derived from girth and bucket safety. |
| [Proof 5.12.](https://arxiv.org/html/2305.18647v6#S5.Thmtheorem12) | proved | `BucketMonotoneKPath.chordEdges_nodup`. Proof associated with the preceding statement. Exactly k distinct actual chord edges, derived from girth and bucket safety. |
| [Lemma 5.13 (Full Counting Lemma).](https://arxiv.org/html/2305.18647v6#S5.Thmtheorem13) | proved with explicit constant | `UnitSpanningCycle.full_counting`. Under offcycleWeight≥5n/epsilon: endpoint count ≥(n/4)*(epsilon*offcycleWeight/(5n))^k; actual finite Bernoulli survival and expectations. |
| [Proof 5.14.](https://arxiv.org/html/2305.18647v6#S5.Thmtheorem14) | proved with explicit constant | `UnitSpanningCycle.full_counting`. Proof associated with the preceding statement. Under offcycleWeight≥5n/epsilon: endpoint count ≥(n/4)*(epsilon*offcycleWeight/(5n))^k; actual finite Bernoulli survival and expectations. |
