# Improved Online Reachability Preservers

Lean formalization of [Bodwin–Le, arXiv:2410.20471v1](https://arxiv.org/abs/2410.20471v1).

## Checked results

- [`forwardPath_spec`](OnlineReachabilityPreservers/Growth.lean) proves the
  forward path specification, including priority for previously purchased edges.
  The reachability computation is exact. Each path search uses at most `n` steps.
- [`compressed_total`, `no_earlier_first_arc`, and `no_earlier_last_arc`](OnlineReachabilityPreservers/Bridges.lean)
  cover the counting identity and ordered bridge exclusions in Lemma 10.
  An unreachable request can be represented by a singleton terminal with no purchase.
- [`theorem11_sinks` and `theorem11_sources`](OnlineReachabilityPreservers/Restricted.lean)
  prove a DAG bound of `n + sqrt(2npσ)`. Each collision of purchased edge
  tails is charged to its earlier round and later sink.
- [`theorem9_lift`, `theorem2_sources`, and `theorem2_sinks`](OnlineReachabilityPreservers/DagReduction.lean)
  extend to arbitrary finite directed graphs. The Lean functions take the input graph
  and the revealed prefix. The proof uses `S` only to bound the actual output by
  `3n + sqrt(2npσ)`, with `σ = |S|`. The functions retain all previously bought
  edges and preserve original reachability for every demand in the prefix.
- [`theorem15_known_budget`](OnlineReachabilityPreservers/KnownBudget.lean) verifies
  the known-budget path assignment and the factor-two union bound.
  [`theorem16_index_sensitive`](OnlineReachabilityPreservers/IndexSensitive.lean)
  verifies dyadic assignment using the two growth inequalities in footnote 4.
- [`theorem5_sinks_known_p`, `theorem5_sources_known_p`, `theorem5_sinks_indexed`, and `theorem5_sources_indexed`](OnlineReachabilityPreservers/RestrictedNonAdaptive.lean)
  verify the endpoint-restricted size and path guarantees of Theorem 5 on
  general digraphs. Write `F = n + floor(sqrt(2npσ))`. The guarantees are
  `2n + 2F` with known `p` and `2n + 48F` with the arrival index, where `p`
  is the prefix length in the indexed bound. The preserver is precisely the
  union of the assigned simple paths, and the assignments give prefix monotonicity.
- [`theorem5_pairwise_rounded` and `theorem5_pairwise_limiting_rate`](OnlineReachabilityPreservers/PairwiseNonAdaptive.lean)
  prove both pairwise rates for both assignment models. The executable rules
  find a certified integer budget by simulating the expensive-pair phase.
  The real-valued rates bound the budget in the proof. The indexed rule uses
  dyadic quotas starting at `Nat.sqrt n + 1` and is correct at every prefix.
- [The Steiner hit phase](OnlineReachabilityPreservers/SteinerHubs.lean)
  proves the exact uniform sample failure count for a fixed pair and an
  inverse-power failure bound over all thick pairs. It serves both hub legs
  in original edges with prefix monotonicity and checks the logarithmic
  competitive contribution at the thresholds of Theorem 21.
- [The thin-demand fractional cover](OnlineReachabilityPreservers/SteinerThinCover.lean)
  checks capacity doubling on the local directed cuts. Every request's cuts
  remain covered, and the capacity sum is bounded by
  `1 + OPT * (1 + floor(log₂ |E|))` after normalization when `|E| > 0`.
  [The rounded preserver](OnlineReachabilityPreservers/SteinerThinRound.lean)
  uses a single independent integer threshold per edge. It is correct at
  every prefix, uses a graph purchase on failure, and has the expected
  logarithmic-factor thin-demand edge bound on a fixed distinct trace.
  The [cut separator](OnlineReachabilityPreservers/SteinerCutFlow.lean)
  uses at most `|E|` unit augmentations. When it stops early the residual
  reachable set supplies a violating cut. Lean checks the augmentation and
  doubling counts.
- [The Steiner phase composition](OnlineReachabilityPreservers/SteinerAssembly.lean)
  starts empty, serves every revealed demand, and preserves every purchased
  edge. It checks the mean cost of the two late phases over independent finite
  choices and adds an explicit early cost. The cited early competitive bound
  and the full running time remain open.
- [The late-phase exponent bound](OnlineReachabilityPreservers/SteinerRate.lean)
  uses integer thresholds for \(n^{6/5}\) and \(n^{3/5}\). It absorbs both
  logarithmic losses and the bad-hub cost into \(O(n^{3/5+\varepsilon})\)
  times the offline solution size, with the early purchases kept explicit.
- [`lemma24_left_injective`, `lemma24_right_monotone`](OnlineReachabilityPreservers/IntersectionOrder.lean)
  order the intersection chains on each pair of outer paths in Appendix A.
  [`lemma26_chain_lower` and `lemma27_acyclic`](OnlineReachabilityPreservers/PairwiseInitial.lean)
  prove the initial incidence bound on systems with a common vertex order by
  counting high-degree incidences with enough predecessors. The same module's
  `pairwise_initial` proves an online `O(n + (np)^(2/3))` edge bound on general
  digraphs, with the exact cubic inequality stated in Lean.
- [`lemma28_from_incidence`, `lemma28_mean_lower`, and `lemma41_branch_count`](OnlineReachabilityPreservers/ClosePairs.lean)
  give the finite close-pair and sampled-subsystem counts used in Appendices A
  and B for systems with a common vertex order. Summing over the base paths
  gives the numerator of the uniform expectation. In the dense regime the
  expectation is at least the squared product of the two averages divided by
  `4096`. The proof also retains the factor that grows with the window size.
  The full-bridge-free proof
  bounds the contribution by the ordered pairs of vertices on the restricted paths.
- [`theorem38_root`, `theorem38_exponent_limits`, and `theorem43_exponent_limit`](OnlineReachabilityPreservers/ExponentLimits.lean)
  check the online cubic root and both arithmetic iterations.
  [OfflineBound](OnlineReachabilityPreservers/OfflineBound.lean) applies each
  Appendix B update to acyclic full-bridge-free systems, including the
  integer branching window, split budgets, and sparse regimes.
- [`lemma37_acyclic_update` and `theorem38_acyclic_iteration`](OnlineReachabilityPreservers/OnlineBound.lean)
  prove the corrected Appendix A update and each finite online iterate.
  The chosen integer window scales with the constant in the inductive estimate.
  The lower mean absorbs the linear contribution and the two window
  exceptions give the claimed rates directly.
- [`theorem1_rounded` and `theorem1_limiting_rate`](OnlineReachabilityPreservers/OnlineSharp.lean)
  prove both adaptive online edge bounds for the actual forward-growth
  preserver on arbitrary finite digraphs, at every prefix. The limiting proof
  chooses one nonnegative slack function of the vertex count that tends to
  zero and works for every demand count. The small-demand bound keeps the
  coefficient of the linear term fixed.
- [`theorem14_dag_compression` and `offline_pairwise_initial`](OnlineReachabilityPreservers/OfflineIndependence.lean)
  prove the constructive independence reduction on DAGs and its initial
  offline pairwise consequence on arbitrary digraphs. The algorithm deletes
  each dispensable edge and the proof assigns the surviving edges to requests
  that require them. The resulting acyclic system has size `m+p` and is fully
  bridge-free. The extremal lower direction remains open.
- [`theorem4_rounded` and `theorem4_sharp`](OnlineReachabilityPreservers/OfflineSharp.lean)
  prove both offline edge bounds for the constructed preserver on arbitrary
  finite digraphs. Two acyclic updates suffice for the rounded bound.
  A single invariant constant gives the limiting rate
  `O(n + n^(3/4) p^(1/2) + n^(2−sqrt(2)) p^(1/sqrt(2)))`.
  This gives the limiting exponents with zero slack. Formal runtime remains open.
- [`lemma37_first_term`, `lemma37_third_term`, and `lemma42_third_term`](OnlineReachabilityPreservers/BootstrapArithmetic.lean)
  verify the rearrangements of those individual branching-count terms.
  The third term of Lemma 42 gives vertex exponent `1/(b+1)`, the exponent
  implicit in Theorem 43. [OfflineArithmetic](OnlineReachabilityPreservers/OfflineArithmetic.lean)
  checks the complete three-term scalar comparison, including absorption of the
  logarithmic term into the two updated powers.
- [`lemma30_integral_square_sum`](OnlineReachabilityPreservers/IntegralMajorization.lean)
  checks the integral majorization step with explicit integrability hypotheses.
  [`lemma31_acyclic_moment`](OnlineReachabilityPreservers/SecondMoment.lean)
  proves the second-moment estimate given the inductive bound on subfamilies.
  It orders the actual path lengths and bounds four clipped powers with
  finite sums and integrals.
- [BranchingDegrees](OnlineReachabilityPreservers/BranchingDegrees.lean)
  checks the predecessor count and average in Lemmas 32–33 under the
  inductive size bound and a maximum-degree cap. It also proves the dyadic
  upper bound on off-base tuples in terms of the path moments of sampled
  vertex sets. A finite square-root triangle inequality retains each bucket
  moment without a separate factor for the number of buckets.
  [OffBaseMoment](OnlineReachabilityPreservers/OffBaseMoment.lean) expresses
  those inequalities as uniform means of the actual bucket statistics.
  [OffBaseAverage](OnlineReachabilityPreservers/OffBaseAverage.lean)
  proves the three off-base powers with no logarithmic loss and combines
  them with the on-base estimate by partitioning the qualifying tuples.
- [OnBaseCounting](OnlineReachabilityPreservers/OnBaseCounting.lean)
  proves the source-restricted bound for the actual systems in Lemma 35
  and counts tuples with their second endpoint on the base. The proof
  groups them by the left branching degree and charges each group to
  important incidences in the induced system.
  [OnBaseAverage](OnlineReachabilityPreservers/OnBaseAverage.lean) sums both
  sides of the dyadic threshold geometrically. Under the inductive incidence
  bound and uniform caps, the resulting expectation is bounded by a constant
  times `ℓ²d² + ℓ^(3/2)d²h^(5/4)` with no logarithmic loss.
- [Regularization](OnlineReachabilityPreservers/Regularization.lean)
  verifies an acyclic upper-cap reduction for Appendices A and B. Splitting
  vertices and consecutive path blocks preserves every incidence and both
  bridge conditions through size four. The new sizes are at most twice their
  original values, and each cap is at most four times the corresponding new average.
- [OfflineMoment](OnlineReachabilityPreservers/OfflineMoment.lean)
  checks the logarithmic second-moment bound and the resulting upper count
  on the actual offline sample. The proof uses the inductive size bound on
  full-bridge-free subfamilies and an ambient sample size at least the degree cap.
- [`lemma20_opt_squared` and `lemma22_hub_count`](OnlineReachabilityPreservers/SteinerCounting.lean)
  prove the terminal-counting lower bounds used in the Steiner application.
  [`lemma29_square_sum`](OnlineReachabilityPreservers/Majorization.lean) proves
  the weak-majorization step used in Appendix A.

Here `p` counts processed requests. For the paper's ordered set of distinct demands,
this is its demand cardinality. The model admits self-pairs and unreachable pairs.
For component contraction, unused vertex labels are isolated in the DAG, keeping
the budget parameter `n` equal to the original vertex count.

The algorithms are executable bounded searches on finite sets. The graph searches
iterate at most `n` times over finite vertex and edge sets, with a deterministic
minimum choice. SCC labels, internal trees, and crossing representatives depend only on the
input graph and can be precomputed. A formal time bound in a specified cost model
is outside the current checked coverage.

## Source and verification

The [statement map](STATEMENT_MAP.md) records the paper's claims, dependencies,
and remaining proofs. The [source notes](SOURCE_NOTES.md) record exact discrepancies.
[SourceAudit](OnlineReachabilityPreservers/SourceAudit.lean) verifies the counterexample
and corrected tail inequality for Lemma 25 and the recurrence discrepancy in Theorem 38.
[SplitAudit](OnlineReachabilityPreservers/SplitAudit.lean) checks that the path
split printed in Lemmas 23 and 39 can introduce a forbidden bridge in a general
path system.

Build from the repository root with `lake build OnlineReachabilityPreservers`.
The library is included in the repository's module index, declaration audit,
and kernel replay.

The [companion PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
includes an interactive trace and a source-linked proof map. The unrestricted
path-system estimates, formal runtime, and full Steiner competitive guarantee
remain open.
