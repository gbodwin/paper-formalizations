# Actual two-star replacement and maximum-family branch bound

Seven strict-compiled sources, 468 lines, frozen into the157-module candidate.
Manifest checkpoint24-source-hashes.json contains158 module/root hashes;
SHA256 97b383c010fd76d8cb0a6cace33d1aefe6c6acfdb248685a155f1798fd7d0e1f.
All150 prior library bodies are unchanged from published2bbec671 (full CI running).
The preceding144 baseline is fully certified. Exact new-source hashes are in
two-star-replacement-freeze.json, and draft/production bytes match.

## Actual replacement

BranchRefinementCount proves that splitting branches in an actual full
covering simple quotient cannot reduce the edge count. Each old crossing
edge has a new crossing-edge preimage, and a proved branch-ownership map
recovers its unordered old pair. This is a surjective edge-image argument,
not an assumed vertex graph homomorphism.

StarSubfamilyQuotient uncontracts selected stars using this theorem.
StarSubfamilyMembership supplies actual original-vertex membership after
uncontracting one old branch and inserting a new star. No host vertex or
edge is deleted here.

StarAdjoinExactLoss and StarExtensionExactLoss extract the precise new loss
2*(k-1)*eps2*d from protected growth without requiring an input clean-family
budget. This distinction matters: removing an old star need not produce a
family that is clean under its smaller center-count allowance.

TwoStarReplacement uncontracts an old star b containing distinct u,v. The
first star grows around u from original small residual neighbors T1; the
second grows around v from T2 minus that first actual k-vertex star. Original
branch disjointness proves v remains a residual singleton. Removing k
candidates leaves at least2*eps1*d when |T2|>=3*eps1*d and k<=eps1*d.
The old quotient has no more edges than its split refinement, and the two
actual growth losses total at most4*(k-1)*eps2*d. The extra clean allowance
is4*k*eps2*d. Every other old leaf assignment remains unchanged; the literal
new center count is |C|+1. No replacement/cleanliness oracle is assumed.

MaximumForestBranchBound uses this actual replacement to prove that each
star in a maximum family has at most one vertex with at least3*eps1*d
original-host small residual neighbors. Its final export chooses one finite
maximum internally and joins this branch bound with the150 residual bound.

## Domain / scope

Same finite simple graph and parameter domain as150:
k>=1, K,d>=1,0<=eps1<=1,eps2>=0,eps2*d>=1,k<=eps1*d.
Smallness always means original degree<=K*d. The exact induced dense
alternative remains |S|<=3*k*(K*k)*d and E(G[S])>=eps1*eps2*d^2/2.
The full canonical quotient has literal allowance4*eps2*d*k*|C|.
The selected maximum can still be empty without further density hypotheses.

This closes actual two-star replacement and both local maximality consequences.
Global quantitative coverage and the density-increment trichotomy/iteration,
construction runtime and the main upper theorem remain open. In particular,
no suspect source counting inequality is invoked in these seven files.

Please check the actual branch-refinement edge direction, temporary lack of
cleanliness after uncontracting, original residual membership of both centers,
exact cardinality and the final paid loss. Check all frozen hashes and old
body preservation. Source-only reciprocal review, no compiler or child.
Save review/two-star-replacement-review.json and report a blocker immediately.
