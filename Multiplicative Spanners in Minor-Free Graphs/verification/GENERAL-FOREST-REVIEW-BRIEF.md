# Actual density core and nonempty maximum clean star family

Candidate144 extends reviewed139 bd9d1d949e8df4c2d45e670721808450fd3fa7dc.
The frozen checkpoint22 manifest has145 entries including root,
SHA689fd4fb6eaed314ead1664f18a0bba23dcb58bd46d21527b8cf2da5c9c6d662.
All139 prior library bodies are unchanged. Five new sources total400 lines:
MinimumDensityCore, GeneralStarForest, MaximumCleanStarForest,
BranchPartitionComparison and CleanStarForestSelection.

The first theorem constructs an actual nonempty induced minimum-cardinality
core retaining an arbitrary positive real density floor d, and proves every
induced degree>d. It uses actual edge deletion, not a pruning oracle.

General stars require actual center/leaf edges, exact branch size k and
pairwise disjoint branches. They do not require leaves to be independent
in the host. The literal full quotient suppresses loops/parallel copies,
retains every host vertex and crossing adjacency, and has a genuine k-bounded
branch model for k>=1. Its count is |V(Q)|+(k-1)|C|=|V(G)|.

SmallCleanStarForest is the exact predicate combining this actual family,
original degree<=D for covered vertices, and the literal complete quotient
loss E(G)<=E(Q)+lossPerVertex*k|C|. A full embedding proves the empty family
is admissible, so finite maximization over all center/leaf assignments is
constructed internally. Alone this does not assert positive coverage.

The final two modules match the genuinely constructed139 star's branches
to the canonical one-star quotient and inject all its actual edges. Thus
under exactly139's c,T,k,K,eps1,eps2,d hypotheses, the original dense-witness
alternative remains, or an actual maximum SmallCleanStarForest at D=K*d,
lossPerVertex=4eps2*d is nonempty. The existing star construction has loss
at most2(k-1)eps2*d, so the4eps2*d budget is genuinely proved and retains
slack for later replacement arguments. No target cleanliness certificate
or maximality oracle is supplied to this endpoint.

Scope: this closes the finite nonempty-maximal-family setup only. Extending
that family while preserving old branches, replacing one old star by two,
deriving residual-neighborhood/coverage bounds, the general density trichotomy,
global iteration and main spanner upper theorem remain open. None follows
merely from finite maximization. No new source-theorem defect is claimed.

Three reciprocal narrow semantic reports cover this five-source batch.
All strict production/root/index/audit and five official replay gates must
pass before publication. Full exact remote CI remains a separate gate.
