# Mathematical screening before experiments: projective incidence

Written before any experiment for this pass. All claims here are ordinary mathematical arguments awaiting review, not Lean proofs. The following specifies the actual certificate, its cost, and forcing in the full graph before spending effort on finite computations.

Fix f≥1, real c≥2, q=floor(cf)≥2f. Choose any prime p≥q. Let P and L be the projective points and projective lines of the vector space F_p³: each is the set of nonzero triples modulo nonzero scalar multiples; point x is incident to line z when x·z=0. Keep these two vertex types disjoint. Each type has m=p²+p+1 elements, each vertex has p+1 incidences, distinct points determine one common line, and distinct lines meet at one point. These follow from one- and two-equation linear algebra over F_p.

The input G has **n=2m vertices**, including all m line helpers. Include every point–line incidence edge at weight a∈(0,1]. Partition P into balanced A,B and add all A–B heavy edges of weight 1. No other edges exist. Let K be the incidence subgraph.

## Actual q-fault certificate and cost

For any distinct points u,v, let l be their common line. There is the path u–l–v. Pair the other p lines through u bijectively with the other p lines through v. Each pair of lines meets at a point z and gives a four-edge u–line–z–line–v path. These p+1 paths are edge-disjoint: the endpoint line sets are disjoint except for l, the intermediate points are distinct, and none is u or v.

Every nontrivial cut separating two points therefore contains at least p+1 incidence edges. If no points are separated, the nonempty side without points contains a line and all its p+1 incident edges cross. Thus K has minimum cut p+1≥q+1.

Construct C explicitly by q+1 rounds of a lexicographically chosen maximal forest in the residual incidence graph, removing the chosen edges after each round. For every cut, if fewer than q+1 crossing edges have yet been retained, a crossing residual edge remains; its endpoints lie in a residual component spanned by the next forest, so that forest contributes another crossing edge. Consequently every C cut has at least q+1 edges. Accepted Lemma A proves C is an actual q-fault preserver of G. All selected edges are input edges.

Each forest has at most n−1 edges, so

`w(C) ≤ a(q+1)(2m−1)`; also `w(K)=a m(p+1)`.

Every vertex of G has at least p+1≥q+1 incidence edges of minimum weight a. The accepted incident-cost lemma therefore gives

`a m(q+1) ≤ D_q(G) ≤ w(C) ≤ a(q+1)(2m−1)`.

These bounds include the helpers and do not assert C is optimal.

## Explicit forcing faults against the full graph

For a heavy edge e=uv, u∈A,v∈B, let l_uv be the unique common line and put `F_e={u–l_uv}`. This is one actual incidence-edge fault, excludes e and has size ≤f. All other heavy edges stay present.

For **1/2<a≤1**, every path in G−e−F_e has length at least `1+2a>2`:

- With no heavy edge, the sole two-incidence path was destroyed; at least four incidence edges cost 4a≥1+2a.
- With one heavy edge, any alternative needs at least two incidence edges, giving 1+2a.
- Two heavy edges alone cannot join the opposite A/B sides. If incidence edges occur too, the path costs more than 2 and at least 1+2a.
- Three or more heavy edges cost at least 3≥1+2a.

The bound is attained: choose another v'∈B, use the retained heavy u–v', then the two incidences on the line through v',v. This path cannot use the failed u-incidence. Thus the **full-graph** alternate distance is exactly 1+2a, not the incidence-only distance 4a. In G−F_e, the direct e gives distance 1. Hence every f-EFT 2-spanner must contain every heavy edge in this weight range.

For **0<a≤1/2**, no such forcing claim is made. Among the p+1 edge-disjoint incidence paths above, at least one survives every f faults because p+1>f. Its cost is at most 4a≤2. Keeping K therefore supplies a replacement within twice the weight for every surviving heavy edge, while every other input edge is already retained. K is an f-EFT 2-spanner of the full G. Reduced common-neighbor overlap does not remove these four-edge alternatives.

For each fixed c,f, primes p≥q are unbounded. This is an actual unbounded-order input family, not a fixed-order diagram. Whether its forcing and denominator bounds reach the required uniform coefficient is deliberately assessed in REPORT.md, without declaring the general theorem repaired or false.
