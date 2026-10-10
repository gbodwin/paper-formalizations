# Twelfth component semantic review

Date: 2026-10-10 UTC

## Verdict

**PASS for the seven frozen components and their stated conditional reduction.** I found no blocking semantic defect in the reviewed fault projection, connectivity amplification, degree statements, core-walk projection, forest trimming, copy-index congestion, preserver-weight positivity, or joined optimum-seeded output theorem.

This is a bounded component review, **not a fresh whole-paper audit**. In particular, it does not discharge the existence of the supplied edge-disjoint connectivity-preserving subdivision packing, prove Theorem 24 or Corollary 25, or complete the paper's main upper bounds.

## Identity, evidence, and limits

- Reviewed all seven actual production files under `repo/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/`: `SubdivisionFaultProjection`, `SubdivisionConnectivity`, `SubdivisionDegrees`, `PreserverWeightPositivity`, `SubdivisionCoreProjection`, `SubdivisionPackingProjection`, and `SeededSubdivisionPacking`.
- Independently recomputed their SHA-256 hashes. Every file agrees with both `review/twelfth-source-hashes.json` and `verification/TWELFTH_SOURCE_HASHES.json` in the paper directory, and its bytes agree with the corresponding Git blob at `ccdf1c651581c51bc116a37893aa564d72c5fb24`. Local HEAD is that commit on `light-eft-spanners-checkpoints`.
- Read the relevant upstream definitions and contracts, including `ParallelSubdivision`, `SubdivisionCleanColor`, `Basic`, `MissingEdgeConnectivity`, `ConnectivityOptimum`, `SeededGreedy`, `Blocking`, `SeededForestPacking`, `ForestComponents`, `ForestComponentPacking`, and `SubtreeAssignments`, together with the actual linked mathlib edge-connectivity and spanning-forest definitions/theorems.
- Inspected the existing aggregate and split replay scripts/logs. The root lists 56 modules; the aggregate log records the seven new builds, the 470-declaration allowed-axiom audit, index success, and its pass marker. Both replay logs contain their respective pass markers covering all seven modules. These are existing gate results, not tests rerun by this reviewer. The displayed twelfth build script explicitly rebuilds the seven new modules and root rather than independently recompiling every older module.
- Independently checked the pinned `paper.txt` and `arxiv2502.10890v2.pdf` hashes against `sources/SHA256.json`. Read the relevant local paper text and CS09 text, including the printed page boundaries.
- No compiler or kernel checker was run, no Lean source was edited, no child was spawned, and nothing was published or changed on the Site. The only written artifact is this report. `ConnectivityCuts` and `MinimalConnectivityCore` were not reviewed.

## Findings by obligation

### 1. Actual faults and native connectivity

`SubdivisionFaultProjection.lean:10–44` projects a fault only when it is an actual half-edge of the selected copy: the base-edge identifier is a member of `C.edgeSet`, and the core endpoint must belong to that edge. Thus failed nonedges, other copy colors, and unrelated vertices cannot create projected faults. Both failed halves of one original edge yield only one base identifier.

The cardinality proof selects one such failed half-edge per bad base edge and injects into the intersection of the fault set with the selected color's actual edge set. Equality of unordered half-edges either identifies their branch identifiers, hence their original edges, or demands equality between the disjoint core and branch sum constructors and is impossible. This is a real injection, not an assumed counting inequality.

`projected_faults_lift` then lifts each surviving original edge to its two surviving half-edges and concatenates these actual paths. The empty walk is handled by reflexivity.

`SubdivisionConnectivity.lean:11–49` counts disjoint actual color-edge intersections and obtains a color with fewer than `k` failures from a total budget strictly below `k * card I`. The connectivity theorem uses mathlib's native definition: reachability after deletion of every set of fewer than the stated number of unordered edges. The finite ambient vertex domain justifies conversion of arbitrary fault sets to finsets. The original graph's connectivity is applied to the projected fault set, then lifted.

The proved claim is the **lower bound/implication** from `k` core connectivity to `k * card I` core connectivity. It is not an exact numerical connectivity equality, a global connectivity claim about all subdivision vertices, or a path-packing assumption.

### 2. Genuine subdivision, parity, and branches

The upstream model has vertex type `V ⊕ (C.edgeSet × I)`, with adjacency only between an original endpoint and a branch belonging to its actual edge. For `I = Fin 2`, it is genuinely the simple graph obtained by subdividing two separate copies of each original edge.

`SubdivisionDegrees.lean:11–46` gives an actual neighbor equivalence at a core vertex and exactly the two distinct base endpoints at a branch. Distinctness comes from the original graph's looplessness. Consequently, every core degree is the incident-base-edge count times the copy count, and every existing branch has degree two.

`doubled_even_degrees` proves even degree at every vertex without a connectedness premise. It does **not** infer a connected Euler tour on disconnected input. `branch_not_highly_connected` correctly excludes a branch from connectivity of at least three to any *distinct* vertex using the native degree upper bound. Its inequality hypothesis is essential: reflexive connectivity is valid at every level, so singleton islands must remain possible.

### 3. Complete-branch projection and forest trimming

`SubdivisionCoreProjection.lean:10–23` requires both actual half-edges through one branch and distinct projected endpoints. A dangling half-edge contributes no projected edge. Under `T ≤ graph C`, the two endpoints force the branch's unordered base edge to be exactly their pair, proving that every projected edge belongs to `C`.

`walk_coreProjection` handles arbitrary walks, not just simple paths. The bipartite subdivision structure forces a core-to-core walk to proceed in two-edge segments. A segment returning to the same core vertex is discarded as a stationary projected step; a segment reaching a different endpoint becomes a genuine projected adjacency. Strong induction decreases the original walk length by two, so repetitions and reversals introduce no missing case.

The native mathlib theorem used by `exists_core_forest` supplies an acyclic subgraph with exactly the projection's reachability relation. It requires neither connectedness nor nonemptiness and only removes edges. Combining it with the walk projection gives the stated preservation of every actual core-to-core reachability. The family version uses the same construction independently for each index; unselected indices impose no obligations or congestion charges.

### 4. Unordered-edge identities and copy congestion

`SubdivisionPackingProjection.lean:11–55` first canonicalizes the branch witness for fixed endpoints to the exact base-edge subtype containing `s(a,b)`. `Subtype.ext` eliminates any distinction caused solely by membership proofs.

For each original unordered edge, the congestion proof fixes one representative pair `(a,b)` for all hosts and assigns every host a copy index witnessed at the common endpoint `a`. If distinct hosts chose the same index, both subgraphs would contain the same actual half-edge from `a` to that canonical branch, contradicting pairwise graph disjointness. Different proof witnesses for the same base edge do not produce different vertices; proof irrelevance handles that dependence. Reversing the representative orientation changes which common endpoint is used, not the validity of the injection.

Thus the number of projected hosts is at most the actual copy count. Trimming can only reduce the host set, so the same bound applies to the resulting forests. No acyclicity assumption on the supplied subdivision subgraphs is needed or silently used.

### 5. Same actual output and explicit remaining packing premise

`SeededSubdivisionPacking.lean:14–41` retains the real `IsMinimumFTPreserver G Q w q` hypothesis and concludes both properties for exactly `output G Q w ((1+eps)*(2*k-1)) f`. The upstream output is the recursive fault-aware greedy construction initialized by `Q.edgeFinset`, processing the actual nonseed input edges. The spanner and weight conclusions concern the same output, and the denominator is the same optimum seed `Q`.

The structural premises remain visible: an indexed family of actual subdivision subgraphs, inclusion in the doubled subdivision, pairwise edge disjointness, at least `q+1` indices, the budget `2*f+h ≤ q+1`, and preservation in every selected subgraph of every pair having subdivision edge-connectivity `2*(q+1)`. These are not replaced by a desired weight inequality.

The join obtains real projected forests, lifts each original `(q+1)`-connected pair to subdivision connectivity `2*(q+1)`, invokes the supplied family's connectivity, and projects back. Congestion specializes to two. It then applies the previously established forest-component pipeline: genuine connected-component vertex domains supply trees, distinct forest indices remain distinct, and a fixed original edge belongs to at most one component tree per forest.

The minimum-weight property is supplied as a genuine optimum premise; the reduction does not claim to compute an efficient optimum. Neither the parity theorem nor the branch-exclusion theorem constructs the needed packing. **Packing existence remains the substantive open obligation.**

### 6. Weight positivity and degenerate domains

`PreserverWeightPositivity.lean:10–46` is sound under positivity only on actual input edges. Applying the true preserver property to the empty fault set forces a path in `Q` between the distinct endpoints of any input edge. That path is nonempty. Every edge of `Q` belongs to `G`, hence has positive weight, and at least one contributes to the finite weight sum. Therefore every genuine preserver has strictly positive total weight whenever the input has any edge. Conversely, `G = ⊥` forces `Q = ⊥` by inclusion. This proves precisely the advertised zero-weight equivalence, without global nonnegativity or an optimum assumption.

The joined theorem still explicitly retains its upstream global nonnegativity premise; the standalone positivity result does not remove it. The upstream ratio proof splits on zero denominator. Under the joined positivity and preserver assumptions, that branch can only be an edgeless input; the actual output is then also edgeless by its spanner inclusion. Lean's `0/0 = 0` convention therefore does not mask a nontrivial positive-edge case.

Boundary checks:

- Empty or singleton original vertex domains have no original edges or branches. Degree, projection, forest, and positivity statements have their appropriate vacuous or zero interpretations; no hidden nonempty/tree assumption appears.
- Empty copy domains give no branches or projected edges. The connectivity target is zero, which is vacuous in native deletion semantics. The strict fault-budget hypothesis cannot demand a nonexistent color. The same applies when `k = 0`.
- A singleton copy domain realizes the ordinary simple subdivision and yields congestion at most one.
- Equal endpoint pairs use reflexive reachability; projected adjacency remains loopless. Diagonal unordered edges have no hosts.
- An empty selected family satisfies the standalone projection/congestion statements. It cannot satisfy the joined theorem's `q+1 ≤ indices.card` premise.
- The joined assumptions exclude `f = 0`, `k = 0`, `h = 0`, and nonpositive `eps`. Its budget with positive `f,h` forces `q+1 ≥ 3`, so the relevant doubled threshold is at least six. The general positivity theorem itself is valid for `q = 0` as well.

## Source alignment and retained scope

The pinned paper's Theorem 24 and Corollary 25 occur on printed page 11. Theorem 24 states an Eulerian forest-packing existence theorem; Corollary 25 uses edge doubling and obtains congestion two after projecting and splitting into component trees. Its footnote explicitly acknowledges the doubled multigraph issue.

CS09 Theorem 3.1 is stated on printed page 169, with its proof continuing on page 170. Its objects are maximal `2k`-islands: vertex sets whose pairs have sufficiently high connectivity **in the ambient graph**. It promises that each island is contained in a connected component of each forest, allowing Steiner vertices. The reviewed all-pairs reachability premise has this ambient-connectivity meaning; it does not silently substitute induced-subgraph connectivity or require an island to be a spanning tree by itself. Singleton islands only require reflexivity.

The genuine simple subdivision, parity result, and branch-degree exclusion provide appropriate ingredients for a later reduction avoiding unformalized parallel-edge identities. They do not supply CS09's packing theorem. Disconnected components must continue to be handled without upgrading even degrees to a single connected Euler tour.

No claim is made here about optimized sampling, Theorem 34 certificate replacement, runtime guarantees, the multigraph upper-bound extension, or completion of the main upper bounds. No correction to the seven frozen sources is requested by this review.
