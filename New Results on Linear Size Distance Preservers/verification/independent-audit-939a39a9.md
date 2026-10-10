# Independent end-to-end audit: corrected distance preservers

## Verdict

**QUALIFIED PASS for the corrected finite mathematical package at commit `939a39a98953db3c23ac9ca55cb1fe58df8758b4`, with one minor documentation correction.** I found no mathematical blocker, hidden geometric oracle, circular final assumption, forbidden axiom, or incorrect final quantifier order in the claimed corrected results. The original paper is **not fully formalized**: its larger uniform growing-dimension range and its sharper near-threshold existential assertion remain unproved. The two formally diagnosed defects in literal source material do not refute the corresponding existential graph theorems.

The coverage inventory has one misleading sentence about positive inner-layer depth. It should be corrected as described in finding F1 below. This does not affect a Lean theorem or the corrected final graph results. The finding is corrected in this documentation-only successor; the audited mathematical sources are unchanged.

Audit date: 10 October 2026 UTC. The independent reviewer had no prior component-review involvement. Existing component verdicts were treated as claims, not as proof authority.

## 1. Exact object and evidence

- Commit: `939a39a98953db3c23ac9ca55cb1fe58df8758b4`.
- Git tree: `e28c7592105a8169b80a4b590621e75fa2f6d4d0`.
- Source: Greg Bodwin, *New Results on Linear Size Distance Preservers*, arXiv:1605.01106v4, 30 December 2020.
- Original PDF SHA-256: `0f579f4f454c145f435a1d51c6c5644da7f47303c7eddb42f720c331ee501f59`.
- Original TeX SHA-256: `aef731b5c31e9d2e1fc3bf426d2699fe82913608d3a9031fe1b141f538703e5b`.
- Lean `leanprover/lean4:v4.34.0`; mathlib `5ed2965256430c3649e86755f9576b54eca72435`; `autoImplicit=false`.

I recomputed all 179 packet-manifest hashes, all 91 entries in the internal paper-source hash record, and compared every archived repository file byte-for-byte with `git archive` of the specified commit. There were no mismatches or extra archived files. The populated checkout had the specified HEAD/tree and no tracked modifications. All nine installed dependency revisions matched `lake-manifest.json`, with no tracked modifications. No cache or frozen file was changed.

The paper consists of 91 source modules, 11,703 lines. The library index imports exactly those 91 modules, without duplicates. The machine-readable verification results preserve every source hash, dependency revision, and exact evidence hash. `independently-inspected-statements.json` records 37 exact source statements/definitions with file names, line ranges, module context and SHA-256. The local Lean diagnostic additionally prints elaborated final unweighted theorem types.

I read the actual PDF text and TeX, including main theorems and construction proofs, rather than relying only on the inventory. I visually checked the PDF's printed pages 3 and 8. Source anchors in the supplied TeX are Theorems 1–2 at lines 193–224, Theorems 3–4 at 236–246, lazy-tree Lemma 5 at 330–338, obstacle-product Lemma 7 at 479 onward, weighted Theorem 5 at 496–511, and unweighted Theorem 6 at 536 onward.

## 2. Certified mathematical scope

Write N for vertices, T for terminals, p for pair demands, and E for the number of edges in a preserving subgraph. Logarithms in the Lean statements are natural logarithms.

### Upper bound 1

`LinearDistancePreservers.theorem_one` constructs a finite set of directed edges contained in an arbitrary adjacency relation on a finite vertex type. For finite nonnegative weights it preserves all p indexed infimum walk distances and satisfies

    |H| <= 3N + 24p floor(cuberoot(N))^2.

Its only ambient type assumptions are finiteness and decidable equality. It does not assume reachable demands, a preselected consistent routing, shortest-path attainment, or any combinatorial certificate. Zero weights, directedness, loops, repeated demands, unreachable pairs and the empty vertex type are handled. Finite nonnegative weights are an explicit scope convention; arbitrary signed or infinite edge weights are not covered. This is a finite quantitative realization of the paper's upper rate; there is no separate named Big-O theorem.

### Upper bound 2

`theorem_two` constructs an actual undirected `H <= G`, preserving native extended graph distances for every pair in the given finite set, with

    |E(H)| <= 2|P| + 12 matchingNumber(V).

`matchingNumber` is a genuine finite supremum of edge counts for loopless graphs whose edges are partitionable into at most |V| induced matchings. It is not an assumed extremal estimate. `matchingNumber_subquadratic` has the correct order `for every epsilon>0, there exists N0, for every n>=N0`, and proves a strict epsilon n² bound through the actual imported triangle-removal theorem. This corrects the original RS prose convention. Quoted quantitative literature bounds are not established here.

### Weighted lower bound

`TheoremThree.bounded_range_lower_bound` states: for every positive natural C, and every N,T with `2 <= T <= N` and `T^3 <= C^3 N^2`, there exist an actual simple graph on `Fin N`, exactly T terminals, and finite positive symmetric weights on its edges, such that every subgraph preserving all terminal-pair weighted distances satisfies

    T^3 N^2 <= (32768 C)^3 E^3.

The smaller-range wrapper has constant 8192 when `T^3 <= N^2`. The factor depends only on the range constant C, not on N,T or the preserving subgraph. The construction uses a proved quadratic repair of the literal source weights. `T>=2` is necessary: one terminal imposes only a zero self-distance and cannot force a positive edge lower bound. Every fixed positive real asymptotic range factor can be covered by a larger positive natural C; this last translation is ordinary mathematics, not an extra named Lean asymptotic theorem.

### Unweighted fixed-dimension lower bound

`TheoremFourGeneral.displayed_lower_bound` has the important order

    for every integer d>=2, there exists K(d)>0,
    for every N,T with 2<=T<=N, there exists G,S,
    for every preserving H<=G, the rate is at most K(d)|E(H)|.

The rate is

    N^(2/(d+1)) T^((2d+1)(d-1)/(d(d+1)))
      exp(-4(d-1)/d sqrt(log N)).

Vertex and terminal counts are exact. There is no caller-supplied vertex-count, volume, flatness, shortest-path, or construction premise. The d=2 coefficient is explicitly 100663296; d>=3 uses the proved lattice-hull theorem. This is the fixed-d displayed rate, extending to all finite terminal sizes, not the source's full uniform growing-d claim.

### Explicit corrected extensions

For d>=3, the package proves the actual radius and coefficient bounds

    explicitRadius <= d^(20d^2),
    rateFactor <= d^(100d^5),
    rateFactor^(1/(d(d+1))) <= d^(100d^3).

The quantitative final graph theorem retains the full loss

    exp(-4 sqrt(log N) - 100d^3 log d).

Under `100d^3 log d <= sqrt(log N)`, it yields the coefficient-one loss `exp(-5 sqrt(log N))`. These are genuinely finite statements allowing d,N,T to vary under their explicit hypotheses. Their dimension range is much smaller than the printed `O(sqrt(log N))` range.

For each fixed epsilon>0 and real B, `superquadratic_fixed_gap` chooses N0 before all later N and T and forces `E > B T^2` whenever `2<=T<=N^(2/3-epsilon)`. The dimension is chosen using epsilon, before N,T; it is not an unrecorded growing-d assumption. The interesting nonempty asymptotic range is `0<epsilon<2/3`; for larger epsilon the admissible terminal range is eventually empty, as the statement openly permits.

The stronger parameterized sufficient condition `200d^5 log d <= log N` and `12d^2 <= sqrt(log N)`, together with `T<=N^(2/3-1/d)`, proves `E >= T^2 exp(sqrt(log N))`.

`superquadratic_sixth_root` removes the user-supplied dimension: `log N>=16^6`, `2<=T<=N`, and

    T <= N^(2/3) exp(-8(log N)^(5/6))

suffice for the same edge bound. Its eventual corollary is `for every real B, there exists N0, for every N>=N0 and every admissible T`, followed by existence of a graph and universality over all preserving subgraphs. No B or threshold is chosen after seeing T. The range is not globally vacuous: at and beyond the stated log threshold, its real cap is at least `exp((log N)/6)` and is eventually far above 2.

### Expression obstruction

`TheoremFourRateAudit.suppressed_expression_le` concerns only the displayed numerical lower-bound expression divided by T². For a deficit `t<=a sqrt(L)`, its upper bound is `exp(27a²/8-c sqrt(L))`, uniformly over d in the theorem. For fixed positive c it demonstrates why that expression cannot supply the claimed sharper implication. It is neither an upper bound on required preserver edges nor a graph counterexample. No separate formal filter-limit theorem is advertised.

## 3. Independent proof-spine inspection

### Directed weighted upper bound

I checked the definitions of list walks, costs and infimum distance, the native-walk bridge, lexicographic consistent tiebreaking, constructed routing, branching injection and batching. A list walk includes endpoint/nonempty conditions and requires every consecutive ordered pair to be an actual directed edge. The native complete-graph representation does not silently discard directedness: the `Allowed` predicate enforces the original orientation. Removing loops/cycles is justified by nonnegative weights, including zeros.

The lexicographic primary score is original real cost, with finite binary edge-code tiebreaking. Finite simple-path selection is proved to be optimal among all walks; additive cancellation supplies consistent subpaths. The branching proof uses the sufficient bound `2N+p^3`, rather than claiming the literal sharper binomial constant. Floor-cube-root batching correctly yields 3 and 24. Unreachable demands are handled separately by infinity and subgraph distance monotonicity.

### Undirected unweighted upper bound

I checked finite parent-function minimization, validity/depth constraints, rerouting, native tree walks and distance preservation, branch counting, finite cut averaging, owner assignment and the mod-3 induced-matching partition. Only demanded nonroot leaves are required; demands may be internal vertices. The retained cut fraction is one quarter, and three depth classes give the factor 12. The conversion of oriented edge sets to undirected edges uses an inequality in the safe direction.

For subquadraticity, each labelled edge becomes a triangle in a genuine three-part graph. Both explicit edge disjointness and absence of accidental triangles are proved. The normalization uses 3n vertices and epsilon/9. The final extremal consequence is deduced from mathlib triangle removal, with no assumed graph decomposition theorem supplied by the caller.

### Repaired weighted lower bound

I traced the actual modular graph and native canonical walks through unique shortestness, exact counts, obstacle-product connectors, weighted separation, subgraph forcing, integer parameter selection and exact padding. The repaired slope cost is `k*x^2 + 1 + a^2`. Layer displacement bounds path length below by k. A longer route is strictly more costly because of the baseline; a length-k route is all-forward, its modular displacement lifts to an ordinary equality under the explicit no-wrap hypothesis, and equality in the quadratic inequality forces the same slope at every step.

The outer obstacle metric also uses integer quadratic weights and a proved separation constant. A competitor with larger primary cost is expensive; a low-primary-cost competitor has exactly the required connector/gadget form. Its outer and inner uniqueness force the canonical vertex sequence. Edge forcing does not assume shortest walks exist in arbitrary subgraphs: finite nonnegative-weight attainment is proved and then used. Padding is an injective graph embedding with isolated extra vertices, proved metric transport, unchanged edge count, and terminal enlargement.

The parameter proof handles path fallback, floors and all finite sizes. The `4C` terminal reduction multiplied by 8192 explains 32768. The positivity/symmetry condition applies to edges, as a weighted graph requires; no unnecessary positivity of off-edge weights is silently claimed.

### Unweighted graph construction and actual geometry

I checked native direction walks, injectivity, edge ownership, counts, the average-rigidity uniqueness argument, actual Behrend port sets, product uniqueness, padding, and path/clique fallback cases. Distances are native `SimpleGraph.edist`, not a surrogate certificate. Ordinary convex extremality gives the equal-average rigidity needed by the construction; it is not silently identified with the source's stronger coefficient-sum-at-most-one convention. The planar branch uses actual coprime directions and an exposed convex chain. The higher-dimensional branch uses actual extreme points of the convex hull of the integer points in a Euclidean ball.

In particular, I followed the geometry that could otherwise conceal an oracle:

1. Actual discrete lattices supply successive shortest vectors outside spans. The real minima basis is not assumed to be an integral lattice basis. Gram–Schmidt/empty-box arguments and Minkowski's first theorem prove the product bound.
2. A separate genuine integral lattice basis is used for the integer cofactor/dual argument. Covering and transference produce a nonzero integral dual vector for an empty ball.
3. An explicit stretched ellipsoid inside a lattice-free cap turns that result into an integer-width bound `8d^(d+1)`. No flatness certificate is supplied as a theorem parameter.
4. A concrete support separator for the actual hull produces lattice-free caps in the missed region. Integer normals and depth floors group them into actual measurable shell/slab cells. The zero-normal case is empty.
5. Orthogonal slicing and Tonelli give the cell volume estimate; finite-volume and sphere-boundary side conditions are discharged. The d>=3 restriction provides the required transverse dimension.
6. Integer shell counting and the convergent depth sum give missed volume at most a dimension constant times `R^(d(d-1)/(d+1))`.
7. The polytope approximation lower bound uses actual angular shadows and uncovered shell volume. Krein–Milman identifies the actual hull with the convex hull of its complete extreme-vertex set. Comparing the volume bounds yields the sharp vertex count at `C b^(d+1)`, with C selected before b. No unproved monotonicity of vertex counts with radius is used.

The final general theorem calls this proved vertex theorem. The independent body-closure traversal reaches the geometry and graph proofs, so they are not merely unrelated theorems imported beside an assumed final construction.

## 4. Constants, domains and boundary cases

The independent review checked the dimension shifts `d=n+3`, the natural subtraction `d-1` under d>=2, positive root denominators, log/square-root domains supplied by N>=T>=2, and the polynomial exponent identity `(2d+1)(d-1)`. The explicit-radius formula includes both ceiling steps, a positive unit-ball volume divisor and the threshold maximum. The cube volume estimates and dimension coefficient losses were inspected through the final root, not only before taking it.

For the clean sixth-root result, with `R=(log N)^(1/6)>=16`, the actual choice is `d=floor(R/4)`. The proof establishes d>=3 and `R<=8d`, checks both numerical budgets and converts the terminal cap in the correct direction. The constants 200, 12, 8 and `16^6` are intentionally loose, but justified. The eventual theorem makes its size threshold dominate both the log threshold and the requested factor B.

The graph witnesses cannot rely on nonexistence of a preserving subgraph: G itself always preserves its own distances. Lower bounds impose exact terminal counts with T>=2, and every finite parameter regime is routed to a product, path, or clique proof. Small or zero inner depth is handled without asserting distinct singleton routes. See F1.

## 5. Literal-source corrections and unresolved scope

- **Printed Euclidean weights:** at n=30, ell=3, x=10, the designated slope-9 path has cost `2 sqrt(82)`, while the checked simple competitor has cost `4+2 sqrt(37)`, which is strictly smaller. Its consecutive edges and endpoints agree with the printed modular construction. The package proves this using exact arithmetic and radicals, then proves the quadratic replacement. This refutes the printed weighting argument, not the existential weighted lower bound.
- **RS prose:** the original sentence at TeX line 222 describes the reverse implication from the extremal one used by the proof. The formal maximum uses the standard intended direction and is fully defined.
- **Lazy-tree leaves:** the literal assertion that leaves are exactly all demanded endpoints is too strong when one demanded endpoint lies on the path to another. The formal construction proves the sufficient one-sided condition.
- **One layer and indexed paths:** multiple direction labels at k=0 can denote the same singleton walk. Distinctness theorems correctly require positive k; exact indexed incidence alone does not imply distinct paths.
- **Lemma 7:** the generic finite perturbation lemma is proved, but a completely generic arbitrary-real weighted metric join is not exported. The normalized integer-weight input family actually needed by Theorem 3 is proved end to end.
- **Theorem 6:** finite construction scales and final exact padding are proved; a separate every-per-layer-size asymptotic statement is not claimed.
- **Original Theorem 4:** neither the printed uniform `d=O(sqrt(log N))` range nor the square-root-log-deficit near-threshold existential assertion is certified. The fixed-d, explicit-budget, fixed-gap and fifth-sixths-deficit results above do not close those gaps. They do not refute those original existential assertions either.
- Prior-work tables, unused quoted bounds and open questions remain source context, not newly proved results.

These exclusions are substantially and prominently disclosed by the frozen README, inventory and dimension-boundary note. Historical introductory comments and pre-CI verification entries are explicitly dated/contextualized and should not override the final theorem types and exact-commit evidence.

## 6. Finding F1: minor documentation correction

**Severity: low; theorem validity unaffected.** In `verification/coverage-inventory.md`, correction 4 ends: “The actual constructions used in the main lower bounds have positive depth.” This is overbroad if it refers to inner gadgets, as the preceding sentence does.

`PlanarParameters` sets `k=t^2-1`; `HigherParameters` sets `k=t^d-1`. Their parameter proofs allow `t=1`. For example, the intermediate arithmetic choice `u=3,v=6` gives `b=v/u=2`, `t=u/b=1`, hence k=0; no positive-k condition is included in these product outputs. The product's full routes have length k+2 and its edge-forcing proof does not require distinct inner singleton routes. Therefore the theorem is sound, but the categorical documentation sentence should be narrowed.

Suggested replacement: “Distinct indexed inner canonical paths are asserted only under positive inner depth. Main obstacle-product parameter choices may allow zero inner depth; their full routes still have length k+2, and the edge-forcing proof does not require distinct inner singleton routes.”

This finding is corrected in the accompanying successor inventory. All 91 mathematical source modules remain byte-identical to the audited commit. The verdict applies to those frozen mathematical sources, not automatically to future proof changes.

## 7. Dependency, axiom and verification findings

### Exact-commit CI independently inspected

The complete raw log records checkout of the audited SHA, successful build with 3,668 jobs (including cached/replayed work), all module-index checks, an audit of 1,595 declarations defined in distance-preserver modules, and 125 sequential project kernel replays including every one of the 91 paper modules exactly once. The CI scripts were read, rather than trusting the receipt alone. Defining-module classification includes private/generated declarations and declarations outside the usual namespace. The allowed axiom set is only `propext`, `Classical.choice`, `Quot.sound`.

A fresh read-only GitHub connector query independently returned run 38076068106/job 114283149999 as completed/success, with build, index, axiom audit and kernel-replay steps all successful. The saved raw log's SHA-256 is `4e5a82ca1fe2c58af4655c68018aefdf412696838a5a9c9311e7272ae0bf5b06`. The live response is saved separately. This is verification evidence, not reliance on earlier semantic verdicts.

### Independent local diagnostic

I wrote and ran `IndependentClosureAudit.lean` single-threaded with `-j1 -DautoImplicit=false`. It completed with exit code 0.

The diagnostic checked 1,221 imported paper declarations by defining module for unsafe declarations and forbidden axioms. It then independently walked **types and bodies**, including opaque bodies, for six final-result closures. I checked Lean's `ConstantInfo.getUsedConstantsAsSet` implementation to confirm that this includes both type and value. The results were:

| Final root | All reached constants | Paper constants |
|---|---:|---:|
| displayed_lower_bound | 45,674 | 645 |
| displayed_lower_bound_explicit | 45,573 | 566 |
| displayed_lower_bound_quantitative | 45,629 | 621 |
| superquadratic_fixed_gap | 45,685 | 652 |
| superquadratic_growing | 45,640 | 627 |
| superquadratic_sixth_root_eventual | 45,646 | 635 |

Every closure contained exactly the allowed three foundational axioms and no unsafe constant. This body traversal supplements the standard `collectAxioms` check, whose imported results can use cached axiom metadata.

The final diagnostic succeeded after two scratch-only corrections: a Lean name-parenthesization/type-annotation mistake in the auditor's code, and adding the direct `GrowingSuperquadratic` import needed for a requested root. Both failed scratch logs are retained. Neither error was in a frozen source file.

A separate lexical scan, stripping nested comments and strings, found no executable `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `implemented_by`, `extern`, or `ofReduceBool` tokens in the 91 paper sources. This is supplementary to kernel checks, not a proof by grep.

### Trust boundary and checks not rerun

This audit did not independently rebuild all mathlib/dependencies, rerun all 3,668 build jobs, or locally kernel-replay all 125 modules. Nineteen older paper `.olean` files were absent locally, including final upper/weighted wrappers. Those spines were inspected in source and are covered by the complete exact-commit CI build/axiom/kernel evidence, not by an invented local full-build claim. The lower-bound closure probe uses available local artifacts and is supplemental; source/commit binding comes from the archived sources and full CI.

Lean's kernel, standard logical axioms, pinned toolchain, imported mathlib theorems and the CI execution environment remain the usual trusted base. Dependency revisions were verified; a full independent formal audit of every imported mathlib theorem was not performed. No experimental numerical check substitutes for a Lean inequality.

## 8. Reproduction and publication record

The full exact-commit verification can be reproduced from the repository root
with the pinned toolchain and dependencies:

```sh
lake build
bash scripts/CheckModuleIndex.sh
lake env lean -DautoImplicit=false scripts/AxiomAudit.lean
bash scripts/KernelCheck.sh
```

The supplementary body/type diagnostic is published as
[independent-closure-audit-939a39a9.txt](independent-closure-audit-939a39a9.txt).
Save its contents as a Lean file and run it with `lake env lean -j1 -DautoImplicit=false`
after building the pinned source. The report does not claim that this
supplementary diagnostic independently rebuilt every imported artifact.

The [machine-readable verdict](independent-audit-939a39a9.json) records source
identity, exact claims, exclusions, the corrected documentation finding, and
verification limits. The [statement extracts](independent-audit-statements-939a39a9.json)
preserve 37 independently inspected exact theorem/definition statements.

This publication retains the mathematical audit findings and removes local
execution-path and publication-coordination details. Original reviewer report
SHA-256: `2443142b8697c9b7cb2cf5740ef81e7e5113f69f1dcd891d69340f67d3fd7e1e`.
No mathematical source changed in the documentation successor.

**Recommended acceptance:** accept the corrected finite package and its explicit
extensions at the audited source commit, with F1 corrected in the inventory.
The original paper remains incomplete. Its larger growing-dimension and sharper
near-threshold existential assertions are neither proved nor refuted here.
