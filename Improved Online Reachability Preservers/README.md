# Improved Online Reachability Preservers

Lean formalization of [Bodwin–Le, arXiv:2410.20471v1](https://arxiv.org/abs/2410.20471v1).

The initial checkpoint covers deterministic path growth and the DAG case of
the restricted online bounds. In a DAG with `n` vertices, for any demand
prefix of `p` requests whose sinks lie in a set of `σ` vertices,
[`theorem11_sinks`](OnlineReachabilityPreservers/Restricted.lean) proves that
the actual forward-growth output preserves reachability and has at most
`n + sqrt (2 * n * p * σ)` edges. [`theorem11_sources`](OnlineReachabilityPreservers/Restricted.lean)
proves the source case by reversing arcs. The monotonicity declarations in
[Online](OnlineReachabilityPreservers/Online.lean) and
[Restricted](OnlineReachabilityPreservers/Restricted.lean) give irrevocability
under prefix extension. The computation sees neither the endpoint promise
nor the final number of demands.

The [statement map](STATEMENT_MAP.md) records the complete source inventory and
coverage. [Source notes](SOURCE_NOTES.md) record exact discrepancies.
[SourceAudit](OnlineReachabilityPreservers/SourceAudit.lean) verifies the
counterexample and corrected tail inequality for Lemma 25 and the algebraic
recurrence discrepancy in Theorem 38.

Build from the repository root with `lake build OnlineReachabilityPreservers`.
The library is included in the repository's module index, declaration audit,
and kernel replay.
