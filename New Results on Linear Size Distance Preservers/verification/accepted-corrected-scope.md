# Accepted corrected-paper completion candidate

## Target and status

This candidate covers the mathematical results of Greg Bodwin's *New Results
on Linear Size Distance Preservers*, arXiv:1605.01106v4, with the explicitly
listed repairs, finite-domain conventions and alternative helper proofs.
The corrected Theorem 4 conclusion was accepted on 12 October 2026. The
original square-root-logarithmic-deficit conclusion is retained as an
unproved historical claim, but is no longer the completion target.

**Candidate only: fresh independent skeptical audit pending.** The 116
mathematical modules are byte-identical to commit
`0e63f86884fa72cbdb1228ca0ce55b6fcc132068`, tree
`4c0128c124e634f7c9d0b4c317d9cf8b661623c4`. Its exact full CI
[38182298230](https://github.com/gbodwin/paper-formalizations/actions/runs/38182298230)
passed on 11 October at 23:19:30 UTC: all build/index/audit/replay stages,
2,074 paper declarations, and 150 distinct project module replays, including
all 116 paper modules. A documentation successor requires its own exact CI.
The earlier independent audit at40db5842 remains evidence for its frozen
112-module target, not a substitute for the requested new audit.

This is not a claim that every sentence, proof method, background citation,
or open question in the original source has been formalized literally.
The precise statement map is [accepted-statement-map.json](accepted-statement-map.json);
the existing [coverage inventory](coverage-inventory.md) gives the proof spine.

## Main-result contract

1. **Theorem 1:** For every finite directed adjacency relation, finite
   nonnegative weights and p indexed demands, `theorem_one` constructs an
   actual subgraph preserving the infimum cost of all directed walks with
   at most `3n+24p floor(cuberoot(n))^2` edges. This is an explicit finite form
   of O(n+n^(2/3)p). Zero weights, loops, empty graphs, repeated demands and
   unreachable pairs are included. Signed or infinite weights are excluded.
   Consistent path selection, shortest-path attainment and batching are
   proved internally; no supplied routing or optimality certificate remains.
2. **Theorem 2:** `theorem_two` constructs an actual finite undirected
   unweighted subgraph preserving native extended distances with at most
   `2|P|+12 M(V)` edges. M(V) is the actual maximum edge count among graphs
   partitionable into at most |V| induced matchings. Its subquadratic
   epsilon/threshold consequence is proved using triangle removal. This is
   the standard extremal RS interpretation, correcting the reversed prose
   implication in the source. Quoted quantitative literature estimates are
   background, not silently assumed as newly proved results.
3. **Theorem 3:** For each natural C>0, then every exact N,T with
   `2<=T<=N` and `T^3<=C^3 N^2`, `bounded_range_lower_bound` constructs an
   undirected graph on Fin N with exactly T terminals and finite positive
   symmetric weights, forcing `T^3 N^2 <= (32768C)^3 E^3` in every actual
   terminal-distance preserver. The filter theorem
   `superquadratic_weighted_little_o` proves the original weighted
   superquadratic consequence with B fixed before the eventual threshold.
   At least two terminals are necessary; a singleton forces no edge.
4. **Theorem 4, displayed bound:** `uniform_dimension_lower_bound` fixes
   any real A>=0 before N,T,d. For N>=8, `2<=T<=N^(2/3)` and
   `2<=d<=A sqrt(log N)`, it constructs exact-size unweighted graphs forcing
   `N^(2/(d+1)) T^((2d+1)(d-1)/(d(d+1))) exp(-(1004+7A)sqrt(log N)) <= E`.
   The common coefficient is uniform in all graph parameters and dimension
   after A is fixed. No geometry, capacity or scale-selection premise remains.
5. **Accepted replacement for Theorem 4's final conclusion:** For
   `log N>=8^4`, `2<=T<=N`, and
   `T<=N^(2/3) exp(-32(log N)^(3/4))`, an actual N-vertex undirected
   unweighted graph with exactly T terminals forces
   `E>=T^2 exp(sqrt(log N))` for every terminal-distance preserver.
   `superquadratic_quarter_root_eventual` fixes each real B before a single
   N0, then works uniformly for every later N and admissible T, forcing
   `E>B*T^2`. The range is eventually nonempty; `log N>=64^4` is a
   sufficient explicit nonvacuity threshold. The old stronger square-root
   deficit is not claimed, and restricted-family obstructions do not refute
   its arbitrary-graph existential statement.

All asymptotic explanations above are supported by explicit finite or filter
statements; a separate named Big-O declaration is not claimed where none
exists. All lower-bound preservation predicates quantify actual subgraphs
with their inherited native distances, and H=G always provides a preserver.

## Auxiliary theorems and source repairs

- **Lemma 1:** the actual induced-matching extremal subquadratic bound is
  proved through a faithful triangle-removal reduction.
- **Lemma 2:** deterministic finite lexicographic optimization replaces the
  random perturbation proof. Consistent shortest subpaths are established
  for reachable endpoint pairs; unreachable demands are treated separately.
- **Lemma 3 and Lemma 4:** `Routing.branch_vertex_unique` proves that three
  fixed paths cannot branch at two vertices. The checked counting argument
  injects excess edges into ordered path triples and proves
  `E<=2n+p^3`, sufficient for the exact same asymptotic Theorem 1. The
  sharper literal `binomial(p,3)` total branching-triple count is not a
  separately formalized conclusion. This is an explicit alternative helper
  argument, not a claimed proof of that sharper numerical statement.
- **Lemma 5:** finite minimization constructs a genuine lazy shortest-path
  tree. Every nonroot leaf is a demand endpoint; demand endpoints may be
  internal. The source's statement that the leaves are *exactly* the demand
  endpoints is false, e.g. root--a--b with demands to both a and b. The
  corrected inclusion is precisely what the proof and Theorem 2 need.
  Unreachable demands retain infinite distance, without invented paths.
- **Lemma 6:** finite averaging keeps at least one quarter of the relevant
  nonbranching edges. Ownership and three depth residues yield actual
  induced matchings; no decomposition oracle is supplied.
- **Lemma 7:** native unweighted obstacle walks have actual uniqueness and
  edge forcing. The generic weighted version chooses one positive epsilon
  before all endpoints and all competing walks. Actual finite positive
  input weights and input uniqueness are explicit; inner symmetry gives
  symmetric output weights. Zero/signed/infinite weights are not claimed.
- **Theorem 5:** its printed Euclidean modular weighting has a concrete
  verified counterexample. The same finite graph with
  `k*x^2+1+a^2`, where k=ell-1, has the required shortest-path properties
  against arbitrary undirected walks, including backward steps. **The
  baseline k*x^2 is essential and must not be omitted from annotations.**
  The layer size n is positive, `(k+1)*x<=n`, and distinct indexed paths
  require k>0. One-layer arbitrary-label incidence is not asserted.
- **Theorem 6:** for each integer d>=2, then one natural K>0, every N>0,
  k>0 and x>=0 satisfying
  `((k+1)K)^(d(d-1))*x^(d+1)<=N^(d-1)` have the actual graph on
  `Fin(k+1) x (Unit -> ZMod N)` with exactly N vertices per layer, kNx
  edges, distinct uniquely shortest canonical paths, incidence x, and
  unique edge ownership. Sharp lattice geometry (d>=3), a separate planar
  proof, carry-free encoding and all integer rounding are proved. The
  proof uses actual average rigidity; it does not claim that ordinary
  convex extremality is equivalent to the source's stronger definition.

These substitutions preserve the main-result contracts above. A completion
label must name the *corrected mathematical results with documented helper
replacements*, not certify every literal original lemma or proof sentence.

## Algorithmic and computational boundary

A reread of the original TeX found no standalone algorithm or running-time
theorem. The only algorithmic bound in the proof is Lemma 5's prose that
there are O(n) edge-decreasing rounds and O(n) other rounds between them
(source lines330--345), giving O(n^2) modification rounds. The formal proof
instead minimizes two finite potentials. It proves existence and the needed
properties, not an executable rerouting implementation, its O(n^2) round
count, or a bit/RAM running-time bound. No such algorithm/runtime claim is
part of this candidate. The paper's references to graph algorithms are
background applications. No computational-cost assumption is used to obtain
any mathematical edge bound.

## Other verified modules and audit coverage

The four modules added after the previous112-module end-to-end audit are
UnlayeredEnvelope, NaturalBoundary, ConnectorPacking and SharedCopyLift.
The first three give explicitly restricted numerical/graph-shape/metric
obstructions. SharedCopyLift is a positive actual-graph transfer with
`r^2*n+2*r*s` vertices, `2*r*s` terminals and `r^2*m` forced edges from an
explicit input lower-bound hypothesis. None establishes normalized-gain
amplification or an arbitrary-graph counterexample. They remain in the
116-module inventory and must be included in the fresh source/axiom/closure
audit even though they are not needed for the accepted four main results.

Prior-work tables, cited background estimates, open questions, source
historical asides, signed/infinite-weight generalizations, executable
algorithms and the superseded sharper Theorem 4 conclusion are not claimed.
This does not remove an intended main result by relabeling it as background.

## Companion annotation gate

The private companion source remains frozen at
`a58a0b96ea154731dfa77ad29eed60f945b1ff1d`. Its ten existing boxed-L controls,
assets and original paper body must be preserved. The audited candidate
annotation plan corrects dp-1's missing weight baseline and adds notes at
Lemma 3 (alternative sufficient bound) and Lemma 5 (leaf inclusion and
nonalgorithmic existence proof). The original text is not rewritten.
The candidate annotation snapshot is separate from the deployed Site.
No live deployment, audience change or public research-site link is claimed.
A fresh skeptical audit and subsequent Site fidelity/interaction/access
checks remain publication gates.
