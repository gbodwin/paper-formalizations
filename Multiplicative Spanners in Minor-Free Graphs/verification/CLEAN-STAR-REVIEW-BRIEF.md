# Actual single-clean-star construction: eight-source review

Baseline: full-CI131 commit95521c5fceee3db8067176db071efd094b66650d,
CI38156526515. All131 previous library bodies must remain byte-identical.
Candidate139 uses checkpoint21-source-hashes.json (140 entries including root).
The owner will provide strict production, root/index, exhaustive allowed-axiom
and all eight official new-module kernel replay logs before final receipt.

## Frozen new sources (production MinorFreeSpanners directory)
1. FullContractionModel: actual covering/full branch-model semantics, identities,
   literal edge contractions, and preservation under genuine model composition.
2. MinorBranchDegree: inject target neighbors into actual original neighborhoods;
   bound quotient degree by the original branch degree sum, then kD.
3. BoundedBranchMerge: merge exactly adjacent branches; other branches unchanged;
   size/width controlled by the actual two-branch sum rather than a loose product.
4. SingletonNonmateChoice: inject real available original neighbors into current
   singleton labels, select outside the actual current mate set, prove adjacency.
5. CleanStarState: retain original vertices, all crossing adjacencies, exact
   quotient vertex count, center branch size/subset, unused singletons and edge loss.
6. CleanStarGrowth: construct one real edge contraction; use exact simple-edge
   identity E_new+1+CN=E_old and CN<eps2*d to pay at most2eps2*d each step.
7. CleanStarConstruction: iterate real states to size k. Every current quotient
   receives its Unmated conclusion from the proved bounded-minor dense alternative.
   Starting with the actual identity model supplies the initial state internally.
8. FullCoverCardinality: exact partition cardinality proves every noncenter branch
   is a singleton when starting from the uncontracted host; original center-to-leaf
   adjacency and exact leaf count show that the branch really is one star.

## Precise endpoint and domain
exists_clean_star_or_dense takes an arbitrary actual finite simple host G,
center c, finite set T of actual neighbors, natural k>=1; real K,d>=1,
0<=eps1<=1, eps2>=0, eps2*d>=1, k<=eps1*d,
2eps1*d<=|T|, and original degree <=K*d for every vertex of {c} union T.
It constructs either an actual original-host induced S with
|S|<=3*k*(K*k)*d and E(G[S])>=eps1*eps2*d^2/2,
or a genuine full covering k-bounded minor Q with an actual k-vertex
center branch inside {c} union T, all other branches singleton,
|V(Q)|+k=|V(G)|+1, and E(G)<=E(Q)+2*(k-1)*eps2*d.
The leaf edges are actual host edges; extra host edges among leaves are allowed.
No initial minor/family, mate certificate, extension oracle, or edge-loss conclusion
is supplied to this endpoint. The generic grow theorem separately accepts an
actual initial state and preserves its explicit invariants.

## Scope boundary
This is a finite single-star construction component toward the general-graph
argument. It does not construct a maximal clean star forest, perform the needed
two-star replacement, prove the full general density-increment trichotomy/global
iteration, or close the main spanner upper theorem. The generic state does not yet
record every protected old branch required for a subsequent forest invariant.
There is no new source-theorem correction claim.

Please check exact hashes, actual simple quotient loop/parallel suppression,
branch/count semantics, nonmate selection, quantitative signs/budgets, the actual
bounded-minor alternative at each iteration, and the endpoint scope. Source-only
reciprocal review is sufficient; no additional compiler or worker is requested.
