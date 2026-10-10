# Independent audit of the displayed lambda upper bounds

Paper: Greg Bodwin, Michael Dinitz, Ama Koranteng, and Lily Wang, *Light Edge Fault Tolerant Graph Spanners*, arXiv:2502.10890v2.

Audit date: 2026-10-10 UTC.

## Judgment

The candidate gives a valid asymptotic counterexample to the exact displayed lambda-form upper bound in Theorem 11 and the 2f branch of Theorem 13, under the paper's explicitly stated parameter domain. A four-hub variant also contradicts Theorem 12 and the other branch of Theorem 13, with eta = 1. Thus the disjunction in Theorem 13 does not avoid the counterexample.

This is a bounded mathematical and source audit, not a Lean-certified result or a verification of the entire paper. It does not contradict the coarser O_epsilon(n^(1/k)) upper bounds or the paper's main 2f competition-threshold conclusion. The precise defect is the stretch-to-weighted-girth parameter substitution in the displayed lambda comparison. Other proof issues identified in prior reviews are outside this audit.

## Pinned sources and page convention

The PDF has an unnumbered title page, so printed page p is physical PDF page p+1.

Sources read and SHA-256 hashes independently recomputed:

- `../sources/arxiv2502.10890v2.pdf`: `8552afdf89b6a44ed642154379dfd3556bc6471cedb90c518733991123489b55`
- `../sources/arxiv2502.10890v2.html`: `b1f899f39a3fb8cf36fe0402c81b44138e4b7e14f11766114ad4e8665e6ba603`
- `../sources/paper.txt`: `acdb645018c6a6fe8f03d56427ddc8e91f532d15e90fff13294226413fb7ed68`

The principal displayed formulas on printed pp.4 and 9 were also checked visually against rendered PDF pages. The supplied finite-check JSON was read but is not used as a substitute for the uniform proof below. No compiler was run and no proof source was edited.

## Definitions and parameter restrictions

- Definition 1, printed p.1 / PDF p.2: a spanner is an edge-subgraph on the same vertex set, with inherited edge weights; its distances must approximate all input-graph distances.
- Definition 3, printed p.1 / PDF p.2: classical lightness is w(H)/w(mst(G)), and ell(G) means w(G)/w(mst(G)). Lambda therefore uses MST-normalized classical lightness, not a fault-tolerant denominator.
- Definition 5, printed p.2 / PDF p.3: the f-EFT condition quantifies over all F contained in the input edge set with |F| <= f. It includes F empty.
- Definitions 7 and 8, printed p.3 / PDF p.4: a q-EFT connectivity preserver Q must have exactly the same connected components as G after every input-edge fault set F of size at most q. Competitive lightness divides w(H) by the minimum weight of such a Q.
- Theorem 11, printed p.4 / PDF p.5, HTML `Thmtheorem11`: all positive integers f,k,n and all epsilon > 0; stretch (1+epsilon)(2k-1); upper comparison O(sqrt(f) lambda(n,(1+epsilon)2k)).
- Theorem 12, printed p.5 / PDF p.6, HTML `Thmtheorem12`: the same domain, with all eta > 0, and upper comparison O_eta(lambda(n,(1+epsilon)2k)) at competition parameter (2+eta)f.
- Theorem 13, printed pp.6 and 15 / PDF pp.7 and 16: the same domain and stretch, with the two displayed upper comparisons O(f lambda(n,(1+epsilon)2k)) and O_eta(lambda(n,(1+epsilon)2k)).
- Definitions 14 and 15, printed p.9 / PDF p.10: weighted girth is the minimum of w(C)/max_e_in_C w(e); lambda(n,s) is the supremum of classical lightness over n-node graphs of weighted girth strictly greater than s.
- Theorem 17, printed p.9 / PDF p.10, HTML `Thmtheorem17`: lambda(n,(1+epsilon)2k) <= O(epsilon^(-1) n^(1/k)). We only need its fixed parameters k=2 and epsilon=1/4, giving lambda(n,5)=O(sqrt(n)).

The PDF text and the HTML's epsilon-bearing statements and surrounding restriction language contain no global small-epsilon convention or exclusion of k=1. In particular, the declared domain includes f=k=1 and epsilon=3/2. The chosen graphs have positive unit weights, are connected and simple, and have nonzero MST weight, so no disconnected-MST convention, zero-weight convention, multigraph extension, or boundary convention affects the example. Taking eta=1 also avoids any question about rounding a noninteger fault budget.

## Uniform counterfamily proof

Fix m >= 3. Let G_m be the unit-weight complete bipartite graph K_(m,m), with sides L and R of size m. Put f=k=1 and epsilon=3/2. The required stretch is (1+epsilon)(2k-1)=5/2, while the displayed lambda argument is (1+epsilon)2k=5.

### Every eligible spanner has all m squared edges

Suppose a subgraph H omits a cross edge uv. In G_m, dist(u,v)=1. Every u-v path in H has odd length because H is bipartite, and it has length at least 3 because the edge uv is absent. If no such path exists, the distance is infinite. In either case dist_H(u,v)>5/2. Thus H is not even an ordinary stretch-5/2 spanner. Applying the EFT condition to F empty proves that every 1-EFT stretch-5/2 spanner is G_m itself. Hence w(H)=m^2.

### A linear-weight two-fault connectivity certificate

Choose three distinct left hubs A contained in L and three distinct right hubs B contained in R. Let Q_3 contain exactly the edges with a left endpoint in A or a right endpoint in B. Inclusion-exclusion gives

    |E(Q_3)| = 3m + 3m - 9 = 6m - 9.

Fix any F contained in E(G_m) with |F| <= 2, including failures outside Q_3. Each failed edge has exactly one left endpoint and one right endpoint. At most two of the three left hubs are incident to a failed edge, so there is a left hub a with no incident failure. There is likewise a clean right hub b. The edge ab survives. Every left vertex is joined to b by a surviving edge of Q_3, and every right vertex is joined to a by a surviving edge of Q_3. Therefore Q_3 minus F is connected. As it is a spanning subgraph of G_m minus F, that graph is also connected. Their connected-component partitions are identical.

Consequently Q_3 satisfies the full Definition 7 quantifier: it is a genuine 2-EFT connectivity preserver. Writing OPT_2 for the minimum allowed denominator,

    OPT_2(G_m) <= 6m - 9,
    ell_2(H | G_m) >= m^2/(6m-9) >= m/6.

The direction of the optimal-denominator inequality is important: a feasible certificate supplies an upper bound on the denominator and therefore a lower bound on competitive lightness.

### Contradiction for Theorem 11 and the first branch of Theorem 13

At these fixed parameters their displayed comparisons would require

    ell_2(H | G_m) <= O(lambda(2m,5)) = O(sqrt(m)),

where the last equality in asymptotic order uses the upper bound in Theorem 17 at its separate parameters k=2 and epsilon=1/4. But every eligible H has ell_2(H | G_m) >= m/6. No constant independent of m can satisfy both inequalities along this infinite family. Allowing the hidden constant to depend on any of the fixed parameters would not remove the contradiction.

### Theorem 12 and the second branch of Theorem 13

Fix eta=1, so the competition parameter is 3. For m >= 4, choose four hubs on each side and let Q_4 be the union of their incident edges. Then

    |E(Q_4)| = 8m - 16.

For any at-most-three input-edge failures, at least one hub on each side is clean. The preceding connecting argument applies verbatim, so Q_4 is a genuine 3-EFT connectivity preserver. Therefore

    ell_3(H | G_m) >= m^2/(8m-16) >= m/8,

whereas the displayed upper bound at fixed eta=1 is again O(lambda(2m,5))=O(sqrt(m)). Thus Theorem 12 and this branch of Theorem 13 are contradicted too. The same G_m family contradicts both alternatives of Theorem 13 at once.

Randomization or polynomial runtime cannot repair this existence obstruction: every stretch-5/2 output subgraph must have all m^2 edges, irrespective of how it is obtained.

## Precise parameter repair and preserved coarse bound

Theorems 21, 28, and 29 on printed pp.11, 13, and 14 analyze actual stretch s with the lambda argument s+1. The upper-bound deduction for Theorems 11 and 12 is on printed p.15. The polynomial-time lightness analysis likewise uses lambda(n,s+1); see Lemmas 32 and 33 and the concluding calculation on printed pp.17-19.

Substituting the advertised stretch s=(1+epsilon)(2k-1) therefore gives

    lambda(n, (1+epsilon)(2k-1)+1)
    = lambda(n, 2k + epsilon(2k-1)),

not lambda(n,(1+epsilon)2k). The latter threshold is epsilon larger. Since lambda is nonincreasing in its second argument, an upper bound by the former does not imply an upper bound by the latter. At the counterexample parameters the repaired argument is 7/2, not 5. Indeed K_(m,m) itself has weighted girth 4 and classical lightness m^2/(2m-1), so lambda(2m,7/2) is at least linear in m; the repaired comparison has no contradiction.

Thus replacing the lambda argument in the upper statements by (1+epsilon)(2k-1)+1 is the precise parameter correction supported by the underlying stretch-s results. This statement about the substitution does not by itself certify all other steps of those results.

For the coarse polynomial dependence, put

    delta = epsilon(2k-1)/(2k).

Then delta >= epsilon/2 for k>=1, and the repaired threshold equals (1+delta)2k. Applying the fixed-parameter weighted-girth upper bound gives

    lambda(n,(1+epsilon)(2k-1)+1)
        <= O(delta^(-1) n^(1/k))
        <= O(epsilon^(-1) n^(1/k)).

The factors sqrt(f), f, and the eta-dependent factor in the corresponding upper results are unaffected by this substitution. In particular the claimed O_epsilon(n^(1/k)) dependence, with its stated fault factors, is not refuted by this family. For the chosen k=1 the coarse bound permits linear lightness.

## Lower-bound expressions and scope

This counterexample targets upper comparisons only. It gives no contradiction to the lambda-form lower statements in Theorems 11 and 12. Moreover, purely at the level of parameter substitution, a lower bound involving lambda(n,s+1) can be weakened to the displayed lambda(n,(1+epsilon)2k), because s+1 < (1+epsilon)2k and lambda is nonincreasing. Thus the monotonicity issue has opposite consequences for upper and lower bounds.

Theorem 34 on printed pp.20-21 is the paper's stated source of the lambda-form lower bounds. This audit does not certify its graph construction, denominator certificate, rounding, or asymptotic vertex argument. The correct conclusion is that this particular counterfamily does not invalidate the lower comparisons, not that every lower-bound proof has been verified.

The result should be recorded as a false exact displayed lambda upper comparison requiring a parameter correction. It should not be reported as a disproof of the main 2f threshold result, the coarse polynomial upper tradeoff, or the entire paper.
