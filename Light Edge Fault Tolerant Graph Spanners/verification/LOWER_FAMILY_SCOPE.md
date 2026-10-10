# Explicit Section 4.1 lower family

The seven-module lower-family batch joins actual graph proofs. It introduces no
custom axioms, asserted packing theorem, or final-result premise.

## Finite statement

Choose a positive integer f, a real stretch t ≥ 1, a natural competition budget
q ≤ 2f−1, and a natural m with 2⌈t⌉ ≤ m+2. Put M=m+3 and K=⌈t⌉. The graph has:

- M core vertices forming a cycle;
- f distinct degree-two branch vertices on each core-cycle edge;
- two unit edges for each branch vertex;
- the direct core-cycle edges, each of weight W=(m+2)/K ≥ 2.

Its actual vertex count is n=M(f+1). A genuine minimum-weight q-fault
connectivity preserver Q exists and has positive weight. Every f-EFT t-spanner
H satisfies

    weight(H) / weight(Q) ≥ n / (16 f² t).

For positive integer stretch k, the sharper finite result is n/(8 f² k).
For any requested lower bound N on order, the construction supplies an
admissible m with n ≥ N. The input graph itself is an eligible spanner, so the
universal statement is nonvacuous.

## Proof ingredients

For each heavy edge, delete its f unit edges incident to one endpoint. An
explicit rotated potential increases by 2 around the remaining base path.
Branch values are actual midpoint/endpoint values, chosen according to whether
the corresponding base edge is the deleted edge. Every surviving unit edge has
potential change at most one; every alternative heavy edge has potential change
at most two, hence at most W. Telescoping the potential along any actual walk
forces length at least 2(m+2). But kW=m+2, strictly smaller. Thus every eligible
spanner retains every heavy edge and weighs at least MW.

The unit-edge graph is a genuine (2f−1)-fault connectivity preserver of the
whole graph. Different color subdivisions have disjoint actual edge sets;
fewer than 2f failed edges leave a color with at most one failure. Removing one
base edge leaves a connected cycle path. The proof handles branch vertices
that become isolated: it proves equality of post-fault connectivity relations,
not the stronger and false claim that the certificate remains connected.
The unit graph weighs at most 2Mf. Consequently the positive optimum has
weight at most 2Mf, and the ratio is at least W/(2f).

For real t, an actual t-spanner is also a K-spanner because all weights are
nonnegative. Since K≤2t, the integer result gives the stated factor 16.
The normalization between finite enumerations is proved by the subsingleton
property of Fintype and transports the same edge sum; it changes no weights.

## Source correspondence and limits

Theorem 9 (printed pages 3 and 19) states a family for f,k≥1. Definition 1
(printed page 1) does not limit stretch to integer values. The real-stretch
corollary therefore keeps that full domain. Since f≤2f−1 for positive f, the
proved q-budget range includes both Theorem 9's f-competitive ratio and the
stronger (2f−1)-competitive threshold lower side.

Substituting t=(1+ε)(2k−1) retains explicit epsilon dependence and a
parameter-dependent lower admissible order. This finite proof must not be
presented as an epsilon-independent, every-n reading of Theorem 10's printed
lower display. The independently reviewed source-domain note gives the exact
qualification. Neither this batch nor a finite high-f saturation observation
refutes a fixed-parameter asymptotic statement with a parameter-dependent
sufficiently-large-n threshold.

This is the Section 4.1 lower family only. Main upper bounds, global forest
packing and host transport, Theorem 34's replacement certificate, optimized
sampling and polynomial runtime are separate remaining obligations.
