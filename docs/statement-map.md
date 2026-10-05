# Bodwin–Patel (2019): statement map

Source: Greg Bodwin and Shyamal Patel, *A Trivial Yet Optimal Solution to Vertex
Fault Tolerant Spanners*, arXiv:1812.05778v2, 1 June 2019, Section 2.

## Exact result currently encoded

Let `G` be a simple undirected graph, `B` a vertex–edge `k`-blocking set,
and `S` any subset of its vertices. Restrict to `S`, then remove every edge
`e` for which `(v,e)` belongs to `B` for some `v` in `S`. Every simple cycle
in the resulting graph has length strictly greater than `k`.

This is the deterministic cycle-elimination step in Lemma 4. Set `k` here to
the paper's `k+1` to obtain its girth claim. The quantitative extension below
counts the surviving edges.

## Exact finite sampling result

Let `G` have `n` vertices and `m` edges, with a finite `k`-blocking set `B`.
For every integer `r` with `3 ≤ r ≤ n`, there exists an `r`-vertex sample `S`
such that its pruned graph has no cycle of length at most `k`, and its actual
edge count `q` satisfies

`m * choose(n-2,r-2) ≤ choose(n,r) * q + |B| * choose(n-3,r-3)`.

The theorem is `exists_dense_high_girth_sample` in `Sampling.lean`.
Its proof establishes the following steps independently:

1. Double count item/sample incidences: an item supported on exactly `d`
   ambient vertices survives in exactly `choose(n-d,r-d)` samples.
2. Every graph edge has two distinct endpoints, so the total sampled-edge
   count is `m * choose(n-2,r-2)`.
3. Every blocking pair has three distinct vertices, so the total sampled-pair
   count is `|B| * choose(n-3,r-3)`.
4. Edge deletion costs at most one edge per surviving pair. Sum this inequality
   over all samples, then choose a sample maximizing the retained edge count.
5. Map pruned graph edges injectively to their original unordered labels and
   prove that the image is exactly the counted retained edge set.
6. Apply the proved cycle-elimination theorem to that same sampled graph.

There are `choose(n,r)` equiprobable samples. Dividing the incidence counts by
this number gives the website's exact survival probabilities. The formal
theorem uses integer coefficients, so it does not require a probability-space
implementation or division by a sample count. It does not yet specialize the
sample size to `ceil(n/(2f))` or encode the asymptotic `Omega(m/f^2)` statement.

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
- Finiteness is unnecessary for cycle elimination; the quantitative extension
  uses a finite vertex type and a finite set of blocking pairs.
- The endpoint-exclusion condition is unused in cycle elimination but is used
  to prove that every blocking pair involves exactly three distinct vertices.

## Next milestones

1. Define weighted greedy construction and fault witnesses; prove Lemma 3,
   including the blocking-set cardinality bound.
2. Specialize the exact finite sampling bound to `ceil(n/(2f))` and prove the
   finite constants underlying the asymptotic bound in Lemma 4.
3. Derive the existential high-girth subgraph and the size bound in Theorem 1.
4. State the precise dependency on a Moore bound before claiming Corollary 2.
