# Frozen cut/contraction packet: independent semantic review

**Verdict: component PASS. No blocking source/semantic defect found in the eight frozen modules.**

This is a bounded read-only review of the new cut, contraction, counting, and fault-connectivity foundations. It is not a whole-paper audit, a full clean rebuild, or a proof of forest-packing existence. The review began on 2026-10-10 at 22:53 UTC. No compiler, kernel checker, browser, child worker, source edit, publication, or shared-cache modification was performed during this review. Only this report was written.

## Integrity and evidence

- Independently recomputed all eight production SHA-256 values, first on entry and again immediately before writing this report. Every value matches both frozen manifests, which are byte-identical.
- Independently compared every prior proof source with Git baseline `26f58f279857575e28088bc92605dd01bd70ea49`: exactly 56 prior files, all byte-for-byte unchanged. This assertion concerns those proof modules, not the root index or documentation.
- Independently counted 64 production `.lean` modules and 64 distinct corresponding root imports; the sets match exactly.
- Reviewed `gate-thirteenth-build.sh`, `replay-thirteenth-{a,b}.sh`, `run-lean.sh`, `run-checker.sh`, and the copied build/replay logs. The scripts and logs support strict builds of the eight new files, successful aggregate root/index checking, the 530-declaration audit with only `propext`, `Classical.choice`, and `Quot.sound`, and official kernel replay of all eight new modules. These are inspected existing execution records, not fresh executions by this reviewer. Earlier objects were reused; this is not evidence of a full clean 64-module rebuild or current 64-module exact CI.
- The all-declaration audit selects project declarations by defining-module prefix and recursively collects axioms. The eight reviewed sources contain no `sorry`, `admit`, new `axiom`, `unsafe`, or `partial` declaration.
- Independently verified both pinned CS09 artifacts against `review/forest-packing-dependency-plan.md`: PDF `e02ce99382d5b43cf403ba04b2eb54cab0843d2548136487869fea8ebb5881d5`; text `7d883da9406c70540c91eaa4cae970a895b7cf2cc70dab7555eb6dba50a6872c`. Read the relevant text and independently extracted PDF pages 7–8, printed pp.169–170.

Repository HEAD at final integrity check: `9752254f87cad1849129b264b8ee2cd08fcc9afc`.

### Exact reviewed production hashes

- `ConnectivityCuts.lean`: `d6017b60478c35165be9f21833a72a5bcb184e06fac75848049f6ec8f08028f3`
- `MinimalConnectivityCore.lean`: `a28e1f64756d495a0bbaec1a50ac73af5b63ea7344d98afa6c65da5273992c40`
- `MultigraphCutTransport.lean`: `ef5bf637f282ef4a89c15b4accec0c02ebb4bf660397e90e2c9f805d6cc9a64e`
- `ContractedCoreCuts.lean`: `e4c66a2c55724fb6a258a98f6bf845881def24ef6c0a03ae4fae0c0595bca665`
- `MultigraphPartitionCounts.lean`: `d37c36dbd4115c5eabeb921e2e3ed8309ac1aee9a678d50ed210cc9f914dd7e0`
- `CorePartitionBudget.lean`: `bb27d8d23d298a76353354cd3fd836912ba709be7154f2157b1f9764fa084a12`
- `MultigraphFaultConnectivity.lean`: `79410110bdea325060c0577d55e0ac165a5c6d6f30a1e376b5e3c194a4f83828`
- `ContractedCoreConnectivity.lean`: `77a73fdb51ff800e707aa71009b44446b1fb0b455721f1edac623861df97783f`

All production locations below are relative to `repo/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/`.

## 1. Genuine simple-graph cuts and finite minimal selection

- `ConnectivityCuts.lean:9–24` defines the actual cut by filtering `G.edgeFinset` on endpoint membership; nonedges and diagonal unordered pairs do not manufacture cut edges. `[Fintype V]` supplies the finite ambient `Sym2 V` domain used throughout the cardinal statements.
- `ConnectivityCuts.lean:27–50` proves that deleting the whole actual cut prevents a surviving walk from crossing sides, then obtains the native-connectivity cut lower bound. `:55–82` proves the converse using the actual component reachable from the first terminal after an arbitrary supplied fault set. Every cut edge must belong to that fault set; the proof compares actual finite cardinalities. This is not a numerical connectivity oracle or a path-packing assumption.
- `ConnectivityCuts.lean:86–99` proves unweighted cut posimodularity by the endpoint cases for each actual simple edge. It is an integral cardinal statement, not the general nonnegative weighted posimodularity theorem.
- `MinimalConnectivityCore.lean:9–22` derives class closure and a separating small cut directly from native edge connectivity. `:26–42` minimizes cardinality among nonempty deficient subsets of the given finite set and thereby obtains the required inclusion-minimality property for every proper nonempty inner subset.
- `MinimalConnectivityCore.lean:48–77` derives the witness from failed native connectivity and the genuine basic-instance assumption that every vertex has a distinct k-connected partner. The excluded terminal makes the core proper; a retained vertex and its retained distinct partner establish cardinality at least two. Closure under all k-connected partners is proved, not supplied. The selected minimal core need not contain the original first terminal; the theorem correctly makes no such claim.

## 2. Native contraction preserves original identities

- Inspected the pinned mathlib definitions: `Graph/Maps.lean:36–53` has vertex set equal to the image and leaves the edge set unchanged; endpoint identification creates loops. `Graph/Simple.lean:117–125` gives `ofSimpleGraph` all original vertices and edge identities in `Sym2 V`.
- `MultigraphCutTransport.lean:14–21` proves equality of edge sets for every cut and its vertex preimage, without a finiteness restriction on either ambient vertex type or edge type. `:25–38` proves exact agreement with the finite simple cut. `:42–62` keeps every retained vertex distinct, maps the outside to `none`, and proves inner-cut preservation. Distinct original crossing identities remain distinct even when their images have the same endpoints.
- `ContractedCoreCuts.lean:11–18` establishes complement invariance by symmetry. `:35–63` handles every cut separating two retained vertices: if the target side excludes `none`, its preimage is a nonempty proper subset of the core; if it includes `none`, the proof complements the side and reverses the terminals. This closes the important orientation case rather than silently assuming the outside vertex lies on the preferred side.
- These contracted-core lower bounds still start with a finite **simple** input graph and its minimal-core premise. The generic map/cut theorem is genuinely multigraph-valued; it does not by itself generalize the selection theorem to arbitrary multigraph input.

## 3. Exact multigraph partition counts

- `MultigraphPartitionCounts.lean:10–24` counts original identities with endpoints in two distinct `some` blocks. The proof uses uniqueness of the unordered endpoints of each native edge. Loops never cross; parallel identities count separately.
- `MultigraphPartitionCounts.lean:29–65` proves the exact identity: the sum of non-outside block cuts equals twice the internal crossing count plus the outside cut. The proof explicitly separates absent edge identities from actual links. It requires finite ambient edge type `E` and finite block type `I`, but does not require finite ambient vertex type `V`.
- `MultigraphPartitionCounts.lean:70–82` obtains the partition budget from actual block-cut bounds and an actual outside-cut bound. Empty `I` is explicitly covered by natural-number subtraction; for singleton `I`, the desired lower bound is zero. This generic theorem still has its stated block-cut premises even in the singleton case.
- `CorePartitionBudget.lean:11–19` identifies the outside boundary with the original cut of the core, excluding complement-created loops. `:25–50` discharges all block-cut premises for a **surjective, nontrivial** partition of the actual core, using an actual vertex in each block and an actual vertex in a different block. Empty blocks cannot be silently assumed nonempty. The final wrapper intentionally does not claim to discharge singleton-block premises; the singleton partition requirement itself is simply zero. A nonempty basic core cannot admit a surjective empty partition.
- These are the actual crossing edges internal to the retained core, not edges through the outside vertex. They prove the numerical partition criterion, not existence of any spanning trees.

## 4. Genuine post-fault walks, not premature simplification

- Inspected pinned mathlib `Graph/Delete.lean:36–45,96–104`: deletion retains the vertex set and removes the specified original edge identities. `Graph/Simple.lean:100–102` simplifies surviving adjacency and removes loops only afterward.
- `MultigraphFaultConnectivity.lean:11–13` uses exactly `(G.deleteEdges F).toSimpleGraph.Reachable`, with endpoints in `G.vertexSet`. Thus a second parallel edge can still witness adjacency after the first fails. The definition quantifies over finite fault sets; its cut-cardinality characterization uses finite ambient edge type `E`.
- `MultigraphFaultConnectivity.lean:17–47` proves the cut obstruction using actual native surviving walks. `:52–83` proves the converse by taking the reachable component in the actual post-deletion graph and showing its cut is contained in the supplied faults. The constructed adjacency at `:68–75` explicitly proves the crossing endpoints are distinct and supplies an undeleted original link.
- Raw fault identities that are not graph edges are permitted. They consume budget but cannot create a link or invalidate the cut-subset argument. No hypothesis silently counts only favorable failures.
- `MultigraphFaultConnectivity.lean:86–97` supplies actual preimages for mapped vertices and proves preservation under any vertex map. `:103–116` supplies a concrete parallel-edge sanity theorem; its comment correctly distinguishes the reflexive equal-endpoint case.
- The result is native `SimpleGraph.Walk` reachability on the correctly constructed surviving adjacency graph. It is not an edge-labelled path-packing or edge-disjoint-path theorem.

## 5. Endpoints, empty sets, and phantom outside vertices

- Equal terminals are safe: no set can separate a vertex from itself, and native reachability has the empty walk. For `k = 0`, the fault requirement is vacuous and cut lower bounds are zero; the final failed-connectivity premise cannot hold. No positivity assumption is being hidden.
- `ContractedCoreConnectivity.lean:11–13` embeds a retained core vertex with an explicit original preimage. Because `Graph.map` uses the image vertex set, the ambient value `none` is not an actual contracted vertex when the original complement is empty. Neither the connectivity theorem nor the helper constructor introduces a phantom endpoint.
- General cut theorems can quantify over ambient sets containing nonvertices without danger: actual links only use actual vertices. The final selected core is proper, so in that application the complement is nonempty and the outside vertex does have a real preimage.
- Empty/singleton cores cause no invalid stronger conclusion in the helper theorems: there are no two separable retained vertices. The actual basic-core existence theorem additionally proves `2 ≤ K.card` and properness.

## 6. Joined core construction and exact CS09 alignment

- `ContractedCoreConnectivity.lean:19–27` turns the real contracted-cut bounds into the real fault-connectivity conclusion. `:31–35` proves equivalence with mathlib's native set-based simple-graph edge reachability. `:41–52` joins failed connectivity, basicness, finite selection, closure, and actual contracted connectivity; neither a minimal-core certificate nor final-connectivity certificate is an extra premise.
- CS09 Lemma 2.4, printed p.169 (pinned text lines 376–381), is a weighted fractional assertion. This packet proves the finite simple-input **integral threshold / minimal strictly-small-cut specialization** needed for the reviewed construction, with genuine multigraph-valued contraction. It does not formalize that literal weighted lemma in full generality.
- CS09 Lemma 2.5, printed p.169 (text lines 383–390), contains both a crossing-count argument and the Nash-Williams/Tutte existence step. The exact double count and the core partition budget establish the former. The latter remains absent.
- CS09 Theorem 3.1 selection, printed pp.169–170 (text lines 401–418,430–437), is matched by the basicness, properness, class closure, and two-vertex lower bound. Substituting the connectivity threshold `2*k` gives the threshold used there. These foundations need no Eulerian hypothesis; they do not thereby establish the Eulerian induction.
- **Still open:** weighted/general-multigraph minimal-core selection at the source's full scope; Nash-Williams/Tutte packing existence; Mader splitting and its preservation properties; contraction/splitting forest expansion; the final packing-existence join; and the polynomial-time/compact-multiplicity claim. Existing conditional downstream application results do not discharge these dependencies.

## Review disposition

Accept the exact frozen eight-module packet as reviewed cut/contraction/count/connectivity components, with the domain distinctions above preserved in public summaries. No production-source correction is requested. Do not promote this PASS to a main Light EFT upper bound, CS09 Theorem 3.1, a whole-paper audit, or current full 64-module CI.
