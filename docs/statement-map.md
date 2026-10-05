# Bodwin–Patel (2019): statement map

Source: Greg Bodwin and Shyamal Patel, *A Trivial Yet Optimal Solution to Vertex
Fault Tolerant Spanners*, arXiv:1812.05778v2, 1 June 2019, Section 2.

## Exact result currently encoded

Let `G` be a simple undirected graph, `B` a vertex–edge `k`-blocking set,
and `S` any subset of its vertices. Restrict to `S`, then remove every edge
`e` for which `(v,e)` belongs to `B` for some `v` in `S`. Every simple cycle
in the resulting graph has length strictly greater than `k`.

This is the deterministic cycle-elimination step in Lemma 4. Set `k` here to
the paper's `k+1` to obtain its girth claim. The proof makes no claim about
how many edges remain.

## Encoding choices

- Graphs use mathlib's `SimpleGraph`; edges use `Sym2 V`, so they are unordered.
- Cycles use `SimpleGraph.Walk.IsCycle`, with vertices in `support` and edges
  in `edges`.
- A blocking pair is a vertex and an original graph edge, with the vertex
  excluded from the edge's endpoints, as in Definition 3.
- The pruned graph's vertex type is the subtype `S`, rather than all original
  vertices with extra isolated vertices.
- The result states a lower bound on every cycle's length, avoiding a convention
  for the girth of an acyclic graph.
- Finiteness, bounds on `|B|`, and random sampling are unnecessary for the step
  proved here. The omitted quantitative statements will need those assumptions.
- The endpoint-exclusion condition is encoded but unused in cycle elimination.
  It will matter for the three-distinct-vertices sampling probability.

## Next milestones

1. Define weighted greedy construction and fault witnesses; prove Lemma 3,
   including the blocking-set cardinality bound.
2. Prove exact fixed-size sampling probabilities and the expected surviving
   edge bound in Lemma 4, with explicit finite-size hypotheses.
3. Derive the existential high-girth subgraph and the size bound in Theorem 1.
4. State the precise dependency on a Moore bound before claiming Corollary 2.
