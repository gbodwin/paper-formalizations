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
- [`lemma24_left_injective`, `lemma24_right_monotone`](OnlineReachabilityPreservers/IntersectionOrder.lean)
  order the intersection chains on each pair of outer paths in Appendix A.
  [`lemma26_chain_lower` and `lemma27_acyclic`](OnlineReachabilityPreservers/PairwiseInitial.lean)
  prove the initial incidence bound on systems with a common vertex order by
  counting high-degree incidences with enough predecessors. The same module's
  `pairwise_initial` proves an online `O(n + (np)^(2/3))` edge bound on general
  digraphs, with the exact cubic inequality stated in Lean.
- [`lemma28_from_incidence` and `lemma41_branch_count`](OnlineReachabilityPreservers/ClosePairs.lean)
  give the finite close-pair and sampled-subsystem counts used in Appendices A
  and B for systems with a common vertex order. Summing over the base paths
  gives the numerator of the uniform expectation. The full-bridge-free proof
  bounds the contribution by the ordered pairs of vertices on the restricted paths.
- [`theorem38_root`, `theorem38_exponent_limits`, and `theorem43_exponent_limit`](OnlineReachabilityPreservers/ExponentLimits.lean)
  check the online cubic root and both arithmetic iterations. The extremal
  estimates that make the updates valid for preserver bounds remain open.
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
includes an interactive trace and a source-linked proof map. The pairwise
extremal estimates and the full Steiner competitive guarantee remain open.
