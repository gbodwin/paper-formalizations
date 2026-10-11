# Eight-source actual bipartite density-increment review

Read-only reciprocal source review; no child, compiler, production edit or
publication is requested. The exact 131-module production tree is under
/workspace/shared/minor-free-spanners/repo/Multiplicative Spanners in Minor-Free Graphs.
Its eight new sources, 441 lines, are IntegerSelectedRegularization,
MinorHostTransport, BipartiteUnmatedAlternative, FiniteBoundedMinor,
SelectedRegularDegree, SelectedBipartiteMinor, InitialBipartiteSelection and
BipartiteDensityIncrement. The 132-entry manifest is
verification/checkpoint20-source-hashes.json, SHA256
7ea145a08f59942394d4c6dc4e01ee047d4ef5049019420886b0a58fb263fe97.
Check every hash and unchanged prior123 library bodies against checkpoint19.
The two strict production groups, root/index/exhaustive axiom gate and two
four-module official replay groups have logs in the owner's verification
folder named bipartite-increment-{build1,build2,aggregate,replay1,replay2}.log.
Wait for the owner's confirmation that all five terminal PASS markers exist.

The final theorem bipartite_density_increment takes ONLY a finite simple
bipartite graph G with finite parts A,B, A nonempty, natural ell,d and real k,
k>0, 1<=ell, 4ell<=k<=d, ell*|B|<=|A|, and every actual left degree >=d.
It constructs either an actual induced graph G[S] with |S|<=10k^3*d,
positive actual edge count and |E(G[S])| >= d*|S|/(400000k^5), or an actual
positive finite graph Q and MinorModel Q G, each original branch of size
at most ell+1, and |E(Q)| >= (ell-1)*d*|V(Q)|. This is the explicit proved
bipartite parameter variant; it is not yet the general-graph density
increment, global iteration, or paper's spanner upper theorem.

IntegerSelectedRegularization keeps the actual chosen star forest while
trimming the induced selected host to natural degree m. Its exact integer
identity is induced degree + exterior neighbor count = original degree.
Using m=d-floor(eps*d), rather than floor((1-eps)*d), avoids an unjustified
extra unit of degree loss. SelectedRegularDegree proves positivity, m<=d,
(1-eps)*d<=m and m+floor(eps*d)=d for d>0 and 0<=eps<1. It also proves
that the actual selected finite subtype's two literal parts cover it and
that its center part is nonempty when C is.

MinorHostTransport proves actual injective homomorphism transport of
bounded branch sets, injects unordered simple edges by Sym2.map, and maps
an actual finite induced witness to its literal image with equal vertex
count and nondecreasing edge count. FiniteBoundedMinor renames the same
positive graph to Fin n without changing its edges or original host branches.
Check the finite-enumeration equalities, including the explicit Nat.card
normalizations, as equalities of actual graph data rather than substitutions
of unrelated cardinalities.

BipartiteUnmatedAlternative reapplies the genuine small-dense/Unmated theorem
on the actual regular host. It does not claim unmatedness survives deletion.
Parameters are K=5k^2, eps1=1/(100k), eps2=1/(100k^2). A mate witness has
|S|<=15k^2*d and E>=d^2/(20000k^3); k>=4 gives the common positive dense
alternative above. The clean branch reuses the already reviewed actual
right-quotient/degree-budget/center-count theorem from checkpoint123.

SelectedBipartiteMinor applies integer regularization to the actual selected
subtype, obtains the regular-host alternative and lifts both alternatives
back to the original graph via the injective subtype projection. It never
supplies a target minor density as a premise. InitialBipartiteSelection
first applies the genuine graph dichotomy to the regular graph, constructs
a full mate-free family by the proved finite selection theorem, and proves
its original left-small hypothesis from exact left degree d. Its natural
boundary count is obtained by Nat.le_floor from the actual real bound.
The final theorem internally obtains its starting left-regular graph as an
actual spanning subgraph of G, then lifts the actual alternatives through
that edge inclusion. No initial family, cleaning estimate, regularization,
global Unmated hypothesis or minor certificate remains in the final input.

Please return a scoped exact-source PASS or precise fixes and save a receipt
at review/bipartite-increment-review.json. Confirm the explicit parameter
range and the still-open general-graph iteration/main upper result. Full CI
remains a separate gate; no full-paper verification claim is requested.
