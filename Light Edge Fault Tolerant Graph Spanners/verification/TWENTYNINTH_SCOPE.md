# Corrected actual extremal-lightness joins

Fourteen frozen sources close the exact corrected lambda interface for the
finite positive-weight simple-graph upper bounds. The 152 parent bodies stay
unchanged at cad776f58e8c75d5e4eb3675e88cd83a52a4d625 (full CI passed).

Final existence statements construct a true minimum connectivity-preserver Q
and the actual seeded greedy EFT spanner H, without an extremal oracle:
- competition 2f: lightness <= 1 + 16 sqrt(f) lambda(n,s+1);
- competition floor((2+eta)f): lightness <= 1 + 8 lambda(n,s+1)/eta;
where s=(1+epsilon)(2k-1), epsilon,eta>0 and f,k are positive naturals.
Weights are globally nonnegative and strictly positive on actual graph edges.
The total zero-denominator convention remains explicit.

Please review actual semantics in dependency order:
1. ExtremalReindex transports actual edge sums, minimum trees, cycles and ratios
   under vertex equivalence. No change in threshold or graph order occurs.
2. ExactOrderSubdivision chooses a real positive MST edge using internally
   constructed Kruskal bottleneck paths, splits it into equal positive halves,
   and preserves both total weights and the exact ratio while increasing order
   by one and preserving the weighted-girth lower bound.
3. ExtremalLightnessSpectrum is a genuine supremum of exact-n graphs, not an
   at-most-n envelope. The subdivision theorem proves graph-order monotonicity.
   g>2 proves boundedness using the prior checked coarse theorem at k=1.
4. ExactExtremalDefinition proves that for n>=2,g>2 the totalized spectrum's
   supremum equals the literal actual graph/MST supremum. A real unit tree
   witnesses one; the added zero only supplies a boundary convention for n<2.
5. The host, induced host, finite candidate assignment, heavy/light and multi-vote
   joins use that actual supremum at the corrected threshold s+1. All global
   packing and minimum-seed inputs are discharged in the two final existence
   theorems. Runtime and the main multigraph extension remain outside scope.

The printed lambda(n,(1+epsilon)2k) expression remains refuted. These theorems
prove the supported correction, not the original expression. Theorem34's lower
certificate gap is independent and unchanged.

## Bounded source-domain check requested
Theorem4, printed p2, and Theorem17, printed p9, explicitly write all epsilon>0
and O(epsilon^(-1)*n^(1/k)). A unit tree has lightness1 at every girth threshold.
The new lemma no_uniform_inverse_epsilon_extremal_bound proves there is no
single C valid for all positive epsilon even at n=2,k=1. Please check global
parameter conventions and the intended quantifier order in the original v2 PDF
before characterizing this. It is at least a finite-uniform formulation boundary:
restrict epsilon to a bounded range or retain an additive constant. It does not
refute a fixed-epsilon asymptotic assertion with parameter-dependent onset, or
the main O_epsilon(n^(1/k)) bounds. Do not call a new theorem-level contradiction
without that source/quantifier qualification. Sources: sources/paper.txt lines77
and514, and the preserved v2 PDF/HTML in sources/.

Please save review/twentyninth-independent-minor-audit.json with exact hashes,
explicit scope, and any required repairs. No compiler or additional worker needed.
