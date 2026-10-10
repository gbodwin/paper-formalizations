# Explicit source corrections

Source: https://arxiv.org/abs/2504.16463v1. Page numbers below are printed
PDF pages (the title page is unnumbered). Source text and equations are
preserved in the companion reading edition; corrections are presented as
separate commentary.

## Claim 19: the greedy weighted-girth threshold

- Construction, printed p.8: k is a **positive integer**, ε is sufficiently
  small and positive, and greedy stretch is `(1+sε)(2k−1)`.
- Claim 19, p.8, https://arxiv.org/html/2504.16463v1#Thmtheorem19,
  claims weighted girth `>(1+sε)2k`. Its proof calls this expression the
  approximation parameter, inconsistent with the actual construction.
- Exact greedy guarantee: `t+1=(1+sε)(2k−1)+1`, smaller by `sε`.
- For k=1 and any `0<a=sε<2/3`, a triangle with edge weights
  `1,(1+3a/2)/2,(1+3a/2)/2` is retained by actual greedy at stretch `1+a`.
  Its normalized cycle weight is `2+3a/2 < 2+2a`, contradicting the printed
  Claim 19. The family works for arbitrarily small positive a.
- Repair for the numerical contradiction in Claim 23, p.11:
  `s≥4g`, `k≥1`, `g≥0`, `ε≥0` imply
  `(1+sε)(2k−1)+1 ≥ (1+2gε)2k`.
  This matches the lifted-cycle upper bound. The overall clustering proof
  remains a separate open obligation; this repair alone is not a proof of
  Theorem 17.

## Lower-bound parameter domain

Theorem 13 (https://arxiv.org/html/2504.16463v1#Thmtheorem13) uses all positive
integers k,h,n. Its lower-bound proof, printed p.7, explicitly claims all
positive k,h and sufficiently large n, then proposes a tree for bounded h.
That case needs **h≥3**: K₂-minor-free graphs are edgeless, and no nonempty
K₁-minor-free graph exists. A positive linear edge lower bound is impossible
for h=2. This does not refute the intended large-h asymptotic lower bound.

## Lightness versus sparsity for an individual graph

Section 1 defines sparsity as `|E(H)|/n` and lightness as
`w(H)/w(MST(G))`. Section 1.1 opens with the unqualified assertion that a
graph's lightness is always at least its sparsity; the subsequent metric
restriction says each edge is its endpoints' unique shortest path.
Source: https://arxiv.org/html/2504.16463v1#S1.SS1, printed p.1.

A unit-weight K₄ plus a weight-10 bridge to a fifth vertex is a metric graph:
each clique edge is uniquely shortest and the bridge is unavoidable.
It has 7 edges, total weight16, and MST weight13. Thus its lightness16/13
is smaller than its sparsity7/5. The introductory sentence should be removed
or qualified. This does not refute the paper's main upper-bound tradeoff.
The concrete MST calculation is a source-checked finite calculation, not
currently advertised as a Lean-certified graph theorem.

## Graph-level implementation of the Claim19 repair

The fourth component batch carries the numerical repair through actual
cluster graphs. It chooses real host bridges, removes the heaviest coarse
edge from an actual cycle, and lifts the remaining walk while avoiding that
host edge. The intrinsic weighted-girth inequality gives the contradiction.
`claim23_for_cluster_family` proves minor exclusion and girth>2k when the
supplied connected, disjoint clusters satisfy the source's diameter and
weight-scale bounds, with s≥4g. This does not yet construct the hierarchy or
prove BLWN17's charging lemma. The original source remains preserved.
