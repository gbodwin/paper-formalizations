# Independent semantic and source findings

Target: commit `40db5842cc89370c32e0b6ba64e231969f771ef0`, tree `450b98266065a7f8d6e3514144b9f863f4742ba1`. This is a new review, not an extension inferred from component reviews. The exact original arXiv:1605.01106v4 PDF and TeX in the frozen packet were read; the PDF was independently extracted to `source-pdf.txt`. No original-paper completion claim is justified.

## 1. Directed weighted upper bound

TheoremOne.theorem_one has no routing, selection, attainment, or uniqueness premise. Its input is an arbitrary finite type, directed relation, NNReal-valued weights, and indexed demands. The output is an actual finite subset of ordered edges, contained in the input relation, preserving the sInf of costs of all endpoint-correct list walks. Its edge bound is `3n+24p floor(cuberoot(n))²`.

PathUnion.IsWalk checks both endpoints and every consecutive step. Singleton walks give zero self-distance; an empty admissible cost set has infimum infinity. NativeWalkBridge converts arbitrary directed list walks to walks in the loopless complete ambient simple graph while separately retaining Allowed directed steps. Only self-loops are erased, without increased nonnegative cost. ConsistentTiebreaking minimizes actual real cost lexicographically with powers-of-two undirected-edge codes over the finite set of simple allowed paths, then extends optimality to all walks by bypass. Fixed endpoints and a simple path's edge set determine its traversal, so this code does not conflate distinct allowed directed simple paths. Subwalk consistency is proved by replacement and cancellation.

RoutingOfPaths derives ranks and predecessor consistency from these paths; Branching injects excess incoming edges into ordered triples; Batching chooses the integer cube root. The final theorem explicitly treats an empty vertex type and turns unreachable demands into self-demands solely during construction, restoring infinite-distance preservation by subgraph monotonicity. Repeats and zero weights impose no extra condition. Signed or infinite weights are not covered, as disclosed.

## 2. Undirected unweighted upper bound and RS correction

TheoremTwo.theorem_two constructs a SimpleGraph subgraph preserving native edist, including infinity, with `2|P|+12 matchingNumber V` edges. LazyTreeSelection selects a real predecessor tree by finite optimization. Its demanded reachable vertices have native shortest walks; unreachable demands are handled by infinity. Removing nondemanded leaves and rerouting a pair of single-child vertices prove the exact tree properties used later. A demanded vertex may be internal; equality of the leaf set with the demand set is not assumed.

The favorable-cut lemma retains at least one quarter of the oriented nonbranching set. Ownership assigns shared edges to one tree; three depth-residue classes give actual induced-matching partitions. matchingNumber is the maximum actual edge count of one-orientation loopless edge sets with a vertex-valued class label and endpoint-disjoint/cross-edge-free distinct edges in each class. This represents at most n induced matchings, including empty classes.

InducedMatchingRemoval builds the tripartite graph with one triangle for every original edge, proves both explicit disjointness and absence of accidental triangles, and applies mathlib's actual triangle-removal theorem. The epsilon/threshold result is genuinely subquadratic. The original TeX's RS prose has the opposite implication from this extremal definition and from the use in its proof. The correction is disclosed; the literal prose is not claimed proved. Quoted Fox/Behrend quantitative RS estimates are excluded.

## 3. Weighted construction and exact lower bound

The printed Euclidean assignment is false on its actual stated modular undirected graph. The frozen counterexample has n=30, ell=3, x=10, designated vertices (0,0),(1,9),(2,18), and simple competitor (0,0),(1,0),(0,24),(1,24),(0,18),(1,18),(2,18). It respects the paper's parameter constraints and costs `4+2sqrt(37)<2sqrt(82)`. This refutes the assignment, not the existential graph theorem.

QuadraticRepair uses `k*x²+1+a²`. Any extra step incurs a baseline exceeding the designated path's entire possible slope-square contribution. For a k-step competitor, height forces all steps forward; the no-wrap bound turns the endpoint congruence into an integer sum; a squared-deviation identity gives optimality and the equality case. ModularDistance encodes arbitrary native undirected walks, so backtracking is included. The actual obstacle-product weighting and metric forcing are joined before parameter selection and exact padding.

TheoremThree.bounded_range_lower_bound fixes natural C>0, then works for every 2<=T<=N with T³<=C³N². The witness is on Fin N, has S.card=T, and has finite positive symmetric weights on actual edges. Every subgraph preserving the inherited weighted distances satisfies `T³N² <= (32768C)³E³`. Floors, small-case path witnesses, terminal enlargement and isolated padding are internal. Any positive real fixed Big-O constant can be dominated by such a natural C. T>=2 is a necessary domain correction: singleton terminal self-distances alone force no edges.

WeightedSuperquadratic uses actual IsLittleO atTop on a terminal-count sequence; eventual admissibility hypotheses are explicit. B is fixed before the eventual graph-size quantifier and the witnesses. Its finite theorem uses max B 0+1, ensuring strict E>B*T² even for negative or zero B. The additional eventual T<=N hypothesis is disclosed and harmless in the intended little-o domain.

## 4. Sharp geometry and fixed-d unweighted spine

LatticeHull.ball is the actual finite set of integer vectors with sum of squares <= R², and its vertices are exactly extreme points of the real convex hull. The graph direction supply comes from translating these vertices; integer average rigidity is proved, rather than supplied as a graph uniqueness certificate.

The geometric chain uses attained discrete-lattice minima, a real minima basis, and a separately chosen genuine integral basis for the cofactor dual. It does not assume the minima basis is an integral basis. Minkowski yields the product estimate; the dual controls lattice-free ellipsoids and actual spherical caps. The actual missed integer hull is covered by shallow caps and finite normal/depth cells. Axial coordinates are proved measure-preserving; transverse annulus integration and the normal/depth sums bound actual Euclidean volume. Zero normals are excluded or yield empty cells. PolytopeApproximation's finite-hull lower bound and LatticeBody's identification of the hull turn missed volume into actual vertex counts. No geometric oracle remains in LatticeVertices.uniform_vertices or the final fixed-d graph theorem.

The graph-facing chain supplies Behrend outer ports, native unique unweighted paths, exact edge ownership and forcing. HigherParameters/HigherRate/HigherBehrend discharge numerical capacities and real-power conversion. The d=2 branch independently uses primitive planar directions; path and clique witnesses handle extreme scales. All final graph statements use Fin N, exact S.card=T and native edist preservation. The fixed-d coefficient is chosen before N,T, with domain 2<=T<=N.

## 5. Uniform displayed Theorem 4 range

uniform_dimension_lower_bound has only hA:0<=A, N>=8, T>=2, T<=N^(2/3), d>=2 and d<=A sqrt(log N). Its coefficient-one loss is exactly exp(-(1004+7A)sqrt(log N)). Thus A is fixed independently of N,T,d, and there is no hidden dimension-dependent constant or geometric premise.

The three branches are genuinely different constructions. For d=2, the planar constant 100663296 is absorbed using exp(27 sqrt(log N)); its loss 29 is weakened to the common coefficient. For d>=3 and d³<=sqrt(log N), BalancedVolume balances the actual shallow/deep estimates, BalancedRadius produces an actual radius <=d^(100d), and BalancedCoefficient bounds the positive graph-rate root by d^(1000d²). log d<=d gives the 1000sqrt(log N) budget and total 1004. For sqrt(log N)<=d³, the elementary sphere construction has coefficient <=exp(7d); exact floor-selected scales, small-scale path/clique branches and Behrend capacities are internal. The sharp and sphere polynomial rates differ by at most exp(4sqrt(log N)), giving loss 8+7A. The final theorem weakens every branch to 1004+7A. The terminal cap implies 2T<=N for N>=8, so the sphere domain is actually discharged.

This establishes the printed displayed dimension range after the stated domain corrections. It does not establish the original 'in particular' existential superquadratic assertion.

## 6. Corrected superquadratic corollaries and nonvacuity

The fixed-gap corollary fixes epsilon>0, chooses a dimension depending only on epsilon, then fixes the coefficient and finally a threshold depending on epsilon and B. Its genuinely nonempty asymptotic terminal range is 0<epsilon<2/3. The quantitative, growing, optimized-budget and sixth-root intermediates retain explicit assumptions and exact graph witnesses; their conditions are not silently discarded.

The quarter-root finite theorem uses log N>=8⁴, 2<=T<=N and the exact terminal cap `N^(2/3) exp(-32(log N)^(3/4))`. It chooses d=floor((log N)^(1/4)), proves all rounding/domain conditions, gains 16sqrt(log N) and invokes the sphere branch directly with loss 15sqrt(log N), leaving the advertised exp(sqrt(log N)) factor. It does not apply the much weaker common uniform coefficient and accidentally lose the gain. Its eventual theorem fixes every real B before one N0, uniformly in all subsequent N,T.

The finite range is empty near the nominal log N=8⁴ lower cutoff. The frozen quarter-root documentation already discloses possible emptiness for small N. This is not global vacuity: log N>=64⁴ suffices for the cap to exceed 2, since 32L^(3/4)<=L/2 and the cap is at least exp(L/6). An audit-only lemma independently checks eventual T=2 admissibility; it is supplementary and is not retroactively part of the frozen package. Every lower-bound theorem has an actual preserving subgraph H=G, so the conclusion is not vacuous through impossible preservation conditions.

## 7. Exact arbitrary-layer Theorem 6

The quantifiers are d>=2, then one natural K>0, then every N>0, k>0, x>=0 under `((k+1)K)^(d(d-1)) x^(d+1)<=N^(d-1)`. This is precisely the fixed-d exponent after taking the (d+1)-st root. For x>0 it also enforces a sufficiently large per-layer size. Nonzero examples exist for every fixed d,k,x by choosing N large; x=0 intentionally gives an empty path family.

Uniform_bounded_directions discharges sharp directions using the planar construction or actual lattice vertices. A rounded integer b controls both direction cardinality and volume. ExactLayerEncoding uses a scalar base B=(k+1)r; every sum of k digits is <B, so integer encoding equality implies coordinate equality. Scalar codes are only claimed rigid at the needed path length, not falsely convex in one dimension. The graph vertex type is Fin(k+1) x (Unit -> ZMod N), so each layer has exactly N vertices without isolated layer padding. Its own native adjacency enforces adjacent layers. Canonical walks have length k and are simple by layer injectivity. Exported conclusions give distinct supports, incidence exactly x, kNx edges, unique ownership and uniqueness against every walk of length <=k. k>0 is correctly needed for distinct indexed routes.

## 8. Generic positive-real weighted Lemma 7

ObstacleProduct.Data contains actual port maps, layer assignments and arc injectivity, not an output optimality or forcing axiom. The outer/inner optimality predicates concern actual native walks in the input graphs. Positive input simple-path uniqueness is converted to full-walk uniqueness internally. WeightedProjection deletes gadget steps and constructs an actual outer walk, retaining connector count and primary cost. Outer equality identifies a two-connector route; factorization confines the competitor to one gadget and identifies labels. Inner uniqueness then yields strict lexicographic comparison.

The finite perturbation is over the finite sigma-type of all simple paths and endpoint pairs, yielding a single epsilon before all endpoints, competitors and smaller positive delta. Strictly positive actual product edge costs make proper bypasses strictly cheaper, so cyclic walks are included. exists_real_weighted_forcing combines native distance attainment with edge coverage to prove equality with the whole graph and its exact edge count. Inner symmetry is a separate, correctly conditional theorem; the metric/forcing results are even valid for directional inner costs. To instantiate undirected symmetric weights, use the stated inner symmetry hypothesis; connector symmetry is by definition. Zero/signed/infinite input weights are not covered here.

## 9. Restricted obstructions

ConstructionEnvelope is a numerical theorem conditioned on exact construction count identities and capacity constraints. Its full-edge sqrt-deficit bound E<=2T²exp(27K²/8) is stronger than a bound on the displayed lower-bound expression, but applies only to that count family. In particular it is not a theorem about arbitrary graphs. TheoremFourRateAudit separately bounds only the displayed expression.

SubdivisionBarrier is an actual graph theorem: an independent old-vertex set and degree<=2 at every new vertex give a bounded-degree vertex cover, hence at most 2N total edges. Taking H=G is an actual preserver. It rules out only the specified full-private-subdivision shape, and only yields E<T² after 2N<T². No unrestricted upper bound or refutation of the original existential assertion is advertised in the inspected current inventory.

## 10. Documentation finding F1

The frozen README has two genuinely unmarked current-scope statements that conflict with its opening and the inventory: lines 132–136 say that the original growing-d range has no proved quantitative coefficient; lines 193–195 say that the printed growing-d range remains unproved. These are not inside the linked historical development record. They are stale under the later UniformDimension theorem, not mathematical defects or overclaims of original completion.

The owner's out-of-target live correction patch replaces both passages with explicitly intermediate/fixed-d scope and points to UniformDimension, while preserving the unresolved original near-threshold assertion. Patch SHA-256: `8062b9b6cc904ee84e002bac40da9deacdaa5598df278e9b5f06ba3bd6551da0`. It is an adequate remedy, but is not part of this frozen commit. Historical comments in intermediate Lean files are separately acknowledged by the inventory and do not change theorem premises or final coverage.
