# Faithful connector-star metric obstruction

This follow-on is an actual graph theorem, not a proof of the original
unweighted near-threshold existential assertion. It is outside the frozen
40db5842 corrected-scope audit and has its own bounded component review.

For a finite connected unweighted graph G, a nontrivial finite indexed port
family, and natural arm lengths a_i, suppose every distinct pair of indices
satisfies edist_G(port_i,port_j) >= a_i+a_j. Then

    |V(G)| >= 1 + sum_i a_i.

Zero arm lengths are allowed. The uniform D>=2, arm-length-L consequence is
|V(G)| >= D*L+1 when pairwise native distances are at least 2L. No tree,
bounded-degree, private-path or subdivision hypothesis is assumed.

The proof uses genuine shortest walks. Each port supplies its first a_i
vertices, with exact distance equal to the position. Triangle separation
makes all these prefixes jointly injective. A midpoint at distance a_i0
from a chosen port is outside every strict prefix, producing the extra
vertex through an Option-indexed injection. Connectedness explicitly
justifies the native edist-to-natural-dist conversion.

This prevents compressing one faithfully stretched connector star by replacing
it with an arbitrary shared high-degree unweighted gadget. It does not bound
constructions with different transition metrics, nor permit adding the bounds
for overlapping gadgets. Multi-copy critical routes and cross-gadget sharing
remain separate possibilities. No arbitrary graph-existence refutation follows.

## Verification

- Strict warning-clean source build with autoImplicit=false and -j1.
- All 8 defining-module declarations use only propext, Classical.choice and Quot.sound.
- Official independent kernel replay of ConnectorPacking passed.
- DP root: 115 modules and 1,979 declarations audited; all four paper indexes pass.
- Every one of the 114 mathematical modules from b577184d is byte-unchanged.
- [Independent exact-source semantic review](connector-packing-source-review.md): PASS.
- Full exact successor CI will run after publication; preparation-time status is pending.

The qualified full-package audit and its exclusions remain
[available here](independent-audit-40db5842/REPORT.md). This component does not
extend that whole-package audit retrospectively.
