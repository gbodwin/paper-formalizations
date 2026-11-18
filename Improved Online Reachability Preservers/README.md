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

Here `p` counts processed requests. For the paper's ordered set of distinct demands,
this is its demand cardinality. The model admits self-pairs and unreachable pairs.
For component contraction, unused vertex labels are isolated in the DAG, keeping
the budget parameter `n` equal to the original vertex count.

The algorithms are executable bounded searches on finite sets. The graph searches
iterate at most `n` times over finite vertex and edge sets, with a deterministic
minimum choice. SCC labels, internal trees, and crossing representatives are fixed
using the input before the requests. A formal time bound in a specified cost model
is outside the current checked coverage.

## Source and verification

The [statement map](STATEMENT_MAP.md) records the paper's claims, dependencies,
and remaining proofs. The [source notes](SOURCE_NOTES.md) record exact discrepancies.
[SourceAudit](OnlineReachabilityPreservers/SourceAudit.lean) verifies the counterexample
and corrected tail inequality for Lemma 25 and the recurrence discrepancy in Theorem 38.

Build from the repository root with `lake build OnlineReachabilityPreservers`.
The library is included in the repository's module index, declaration audit,
and kernel replay.
