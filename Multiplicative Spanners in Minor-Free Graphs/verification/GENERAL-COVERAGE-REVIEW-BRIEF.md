# Actual general-graph coverage alternative

Five sources, 382 lines, are frozen into the 162-module candidate.
checkpoint25-source-hashes.json has 163 module/root hashes, SHA256
35c5c2c595c06f58b5681d581ea5bd56432c47e6c57e040df463c5790cbbbf47.
The exact authoritative hash is also printed in general-coverage-freeze.json.
All 157 old library bodies are unchanged. The five staged strict builds pass;
production/root/audit/replay gates follow. Draft and production bytes agree.

Let U be the actual original-degree-small residual set, F the covered vertices,
H the covered vertices with at least 3 eps1 d original neighbors in U, B the
original-degree-large vertices, and Y=B union H. The 157 branch bound gives
k|H|<=N. The first module selects H literally and double-counts original
crossing edges. In particular, it proves the conservative bound
  e(U, F minus H)<=3 eps1 d |F|.
It counts every ordinary covered vertex. No stronger count in terms of |H|
or the number of stars is assumed.

Let W be residual vertices with fewer than
  d-(2+3k)eps1 d
neighbors in Y. Original minimum degree at least d and the 150 residual bound
force at least 3k eps1 d neighbors in F minus H for every vertex in W.
Exact crossing double counting then proves k|W|<=|F|. The cancellation uses
positive eps1*d; this follows from the final theorem's k>=8 and k<=eps1*d.

The actual global degree sum proves 2k^2|B|<=N under K>=4k^2, d>0 and
E(G)<=dN. Therefore 2k|Y|<=3N. If2|U|>N, choose X=U minus W.
For k>=8 and 4ell<=k, the integer cardinalities imply X nonempty and
ell|Y|<=|X|. The graph G.between X Y is explicitly constructed; it is a
spanning subgraph of the original G and genuinely bipartite with those parts.
Its exact left degree is the actual neighbor-filter cardinality, so every
left degree is at least d-(2+3k)eps1 d. Payload sets and graph are the same
objects used for all cardinality/degree conclusions.

The final export general_clean_coverage_alternative internally selects the
maximum family and invokes both 157 local consequences. It assumes only the
original finite simple graph and explicit parameters/degrees/density:
k>=8, 4ell<=k, K>=4k^2, d>=1, 0<=eps1<=1, eps2>=0, eps2*d>=1, k<=eps1*d,
original minimum degree>=d, and E(G)<=dN. It returns either the unchanged
small dense induced witness, the actual unbalanced bipartite subgraph above,
or a constructed clean family with 2|U|<=N. No family, coverage bound,
exceptional-set budget or bipartite output is supplied as a premise.

The explicit factor 2+3k is intentional. A useful positive bipartite degree
requires a subsequent small-eps1 specialization; this packet does not claim
the source paper's stronger 1-6eps1 expression for arbitrary eps1. It also
makes no new source-theorem refutation claim.

Remaining main proof steps: construct a densest induced core giving both
minimum degree and all induced density upper bounds; delete actual residual
singletons from the same canonical minor and prove its precise ratio; join
the 131 bipartite increment with natural rounding; then global iteration,
hierarchy/running time and the main upper theorem. The existing 144
minimum-density-floor core is not silently assumed to give a densest core.

Please verify the real crossing identity, positive cancellation, integer
cardinality arithmetic, actual bipartite degree/finite-instance normalization,
all frozen hashes and old-body equality. Source-only reciprocal review, no
child or compiler. Save review/general-coverage-review.json.
