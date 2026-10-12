# Actual small-component absorption: frozen fifteen-source packet

Parent: 75ddc8f4fe8bafa1004aece8bddf59e2a8910c5d (242 modules).
Manifest: checkpoint34-source-hashes.json, 258 source/root entries.
All fifteen new sources are exact copies of the named owner drafts in
small-absorption-phase-freeze.json. Every 242 inherited proof body is unchanged.
Strict production/root/index/exhaustive audit and fifteen replays are separate
owner gates. Review source only; do not claim full CI or complete lightness.

## Actual construction

1. ResidualBoundaryOwnership and ResidualOwnershipPartition select one actual
boundary edge and root for each genuine residual component. Whole components
stay intact; the internally chosen root fibers form a disjoint covering.
2. MaximumSupportedPath selects a maximum-mass actual simple supported path
from a finite set. RootedPathDiameter proves its radius lies between d(root)-1
and d(root)-1+2K by splitting at the root at most once. Root-avoiding paths
transfer back through RootedResidualGraph into a single original residual
component. RootedResidualConnectivity constructs the real connecting walks.
3. RootedAbsorptionReserve reserves at most N actual non-root vertices. For a
short critical path its own vertices and actual connector count pay its mass;
for a long path N chosen vertices' baseline credits pay the 2K increase.
AbsorptionCreditPayment releases all remaining vertex credits. The numerical
inputs are 2K<=Nb, a<=cb and Na+future<=spare. No paid-radius inequality is an
input. The old root's c*(d(root)-1)+spare is counted once.
4. OwnedResidualAbsorption constructs the root graph on actual ports and
selects its radius/reserve. WeightedRootedAbsorption lifts the same paths into
the original host and pays with actual original unit connectors. The common
full unit quotient can have more edges than the constructed connected root
graph; monotonicity justifies using its actual larger connector budget.
5. SmallComponentAbsorptionPhase constructs a covering next cluster family,
with retained roots, radius at most old root radius+2K, future reserves, and
pairwise disjoint original connector budgets.
6. SelectedResidualClusters combines actual previously selected core branches
with the untouched original residual branches. The family covers the original
host and preserves all intrinsic walks. CoveringClusterConnectivity proves
actual unit-host connectivity descends to the covering quotient.
7. MixedResidualHeavyEdges deliberately counts ORIGINAL small-cluster labels.
A large root can hide several original incidences in its new simple quotient;
we do not use that quotient degree. The right-index preimage is injective, its
cardinality is exact, and the original old family pays every incident heavy
edge using qM per absorbed old vertex.
8. MixedSmallAbsorptionPhase combines the actual construction, original heavy
edge charge, new covering family, unchanged root reserve and fresh original
unit connectors. Every new connector is outside every old mixed branch,
including all selected-core interiors, so old internal connector credit is
not reused.

## Explicit domain and remaining work

The input is an actual old covering cluster family, an actual nonempty selected
core family with its same branch unions and intrinsic radii, and a connected
coarse unit-edge graph H on that mixed family, with H contained in the actual
unit quotient. H need not be acyclic. It may be the already chosen forest.
Every actual simple path within each actual residual component of H must have
effective mass at most K. This is the SMALL-COMPONENT CASE input, not a claim
that the whole residual always satisfies it. Per-old-vertex diameter/baseline
credits, original heavy-edge degree/weight bounds, old-cluster looplessness
and uniqueness, and the numerical scale conditions remain explicit. The
loop/uniqueness inputs concern the original small family only and are the
already proved weighted-girth interfaces.

Large-path endpoint absorption/segmentation, the unconditional next-level
case split, deferred-edge accounting, choosing all scales simultaneously,
global multilevel lightness, runtime and whole-paper audit remain open.
No original paper defect is asserted by this packet.

Please read all fifteen frozen sources and bind exact hashes, old-body
preservation and the actual connector/label semantics. Save the scoped review
in review/small-absorption-phase-review.json. No compiler or child required.
