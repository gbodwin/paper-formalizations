# Weighted superquadratic consequence and a subdivision obstruction

These are two separate follow-ons to the existing finite graph theorems. They
do not settle the original unweighted square-root-deficit existential assertion.

## Literal weighted Theorem 3 consequence

`TheoremThree.superquadratic_weighted_finite` fixes an arbitrary real target
factor B before N,T. For every `2 <= T <= N` satisfying

    T <= N^(2/3) / (32768 * (max B 0 + 1)),

it constructs an actual graph on `Fin N`, finite weights strictly positive and
symmetric on its edges, and exactly T terminals, such that every subgraph
preserving all their actual weighted distances has more than `B*T^2` edges.
No graph, geometric, parameter-selection or asymptotic certificate is supplied
by the caller. It uses the already proved Theorem 3 cube inequality, with its
constant C specialized to one. Taking the positive cube root and cancelling
positive numerical factors preserves the strict final factor.

`TheoremThree.superquadratic_weighted_little_o` states the source corollary
using Mathlib's actual `Asymptotics.IsLittleO` and the natural-number `atTop`
filter. For every natural terminal-count sequence T(N) that is eventually
between 2 and N and satisfies `T(N) = o(N^(2/3))`, every fixed real B is
eventually exceeded by the edge/terminal-square ratio of all preservers of
actual exact-size witnesses. The eventual threshold is chosen after B;
the graph may depend on N, as in the source existential assertion.

## Actual graph-shape obstruction for private subdivision

`SubdivisionBarrier.edges_le_degree_cover` bounds the actual edge finset of
any finite simple graph by k times the size of a vertex cover whose vertices
all have degree at most k. Degrees outside the cover may be arbitrarily large.

If a set of old vertices is independent and every new vertex has degree at
most two, `edges_le_twice_new_vertices` gives

    |E(G)| <= 2 * (|V(G)| - |old|) <= 2 * |V(G)|.

The whole actual graph G is a native extended-distance preserver for every
terminal set, including disconnected terminal pairs. Consequently,
`exists_preserver_lt_terminal_square` gives a preserver with fewer than T^2
edges whenever `2*|V(G)| < T^2`.

This graph criterion captures full private subdivisions in which every
original edge is replaced by a private path with at least one new internal
vertex. No all-edge subdivision operation or execution trace is formalized
here. It does not bound partially subdivided graphs, shared high-degree
metric gadgets, or arbitrary graph constructions. In particular, it is not
a refutation of the unresolved source existential lower bound.

## Verification boundary

The two production modules are byte-identical copies of their reviewed drafts.
The adjacent assembly, local gate and exact-source review receipts record the
source hashes and stages. The complete new-commit CI is a separate gate.
The historical qualified whole-package audit remains scoped to 939a39a9.
The exact-layer predecessor 01b651bf completed full CI at 21:21:44 UTC with
3,684 build jobs, 1,826 paper declarations and all 141 project kernel replays,
including 107 paper modules; its terminal receipt is included here.

## Reproduction

From the pinned repository root, after dependency builds:

    lake build LinearDistancePreservers
    lake env lean -j1 -DautoImplicit=false "New Results on Linear Size Distance Preservers/verification/AuditConsequences.lean"
    bash scripts/CheckModuleIndex.sh
    lake env leanchecker -v LinearDistancePreservers.WeightedSuperquadratic
    lake env leanchecker -v LinearDistancePreservers.SubdivisionBarrier
