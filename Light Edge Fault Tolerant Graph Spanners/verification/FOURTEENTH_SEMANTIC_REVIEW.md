# Native multigraph core extension: independent semantic review

**Verdict: component PASS. No blocking semantic or source-correspondence defect found in the four frozen production files.**

This is a bounded read-only review of the integral finite native-multigraph core, contraction, and partition-budget components. It is not a full-paper audit or proof of packing existence. Review performed on 2026-10-10, beginning at 23:18 UTC. No compiler, kernel checker, browser, child worker, production edit, publication, or shared-cache modification was used. Only this review report was written.

## Integrity and verification boundary

- Independently recomputed all four production SHA-256 values on entry and immediately before writing this report. They match the frozen manifest and the corresponding Git blobs at published checkpoint `c3a3aae006f140cfb1b007974320f0d3b3ea90d6`.
- The review manifest and repository `verification/FOURTEENTH_SOURCE_HASHES.json` are byte-identical.
- Independently enumerated the proof files at baseline `15f6e7cfae93c49cb836c6b91f543b9c1ea9c09f`: exactly 64 prior proof modules. Every one is byte-for-byte identical in the current working tree and at the published checkpoint. The only changes within the published checkpoint’s proof-module directory relative to that baseline are the four additions under review.
- Independently counted 68 production Lean modules and 68 distinct corresponding root imports in the published checkpoint; the sets match exactly. This was checked in the working tree at 23:19 UTC and again directly against published Git blobs before completing the report. At 23:20 UTC, a separate, unpublished four-file forest packet and a 72-module root were added to the working tree by the ongoing implementation task. Those later additions are outside this review; the four frozen core sources remain unchanged.
- Inspected the build/replay scripts, their runners, the copied logs, and the declaration-audit source. Existing records support four strict new-source builds, the 68-module aggregate/index check, an exhaustive 548-declaration audit allowing only `propext`, `Classical.choice`, and `Quot.sound`, and four official `leanchecker` replays. These are inspected execution records, not fresh executions by this reviewer. Earlier objects were reused; no fresh full 68-module rebuild or exact-commit CI result is certified here.
- The four reviewed files contain no `sorry`, `admit`, `axiom`, `unsafe`, or `partial` declaration.
- Independently checked the pinned CS09 PDF/text hashes against the dependency plan: PDF `e02ce99382d5b43cf403ba04b2eb54cab0843d2548136487869fea8ebb5881d5`; text `7d883da9406c70540c91eaa4cae970a895b7cf2cc70dab7555eb6dba50a6872c`. Read the relevant source text and independently extracted PDF pages 7–8, printed pp.169–170.

### Frozen source identities

- `MultigraphContractionSize.lean`: `a58eda67d4f8a1a80d3ba07abfa1fd752580baefb6dd8891f4855b3e7a16d4fe`
- `NativeMultigraphCore.lean`: `d896135be739caa2064175df1a24da0dde8424edf286a3a49474d6c60853d807`
- `NativeCoreContraction.lean`: `b7db3b0264b5e1a2b9a5a13db61bf0552cf30297286c12fe5c8f01ce64dac8a8`
- `NativeCorePartitionBudget.lean`: `688767548bb36eeeccbd37b64b02d1dd8831fc5f557a8074ed83bd2d332ee4d6`

Production line references below are relative to `LightEFTSpanners/`.

## 1. Native graph domains, edges, and post-deletion semantics

Inspected the pinned mathlib `Graph.Basic`, `Graph.Maps`, `Graph.Delete`, and `Graph.Simple` definitions, together with the previously reviewed `MultigraphCutTransport`, `MultigraphFaultConnectivity`, `ContractedCoreCuts`, and `MultigraphPartitionCounts` dependencies.

- `Graph V E` has explicit actual vertex and edge sets; neither ambient type is assumed fully occupied. Native links imply membership of both endpoints and the edge identity. Endpoints are unique up to reversal, while different identities can have identical endpoints.
- `Graph.map` maps the actual vertex set by image and retains the original edge set. Identifying endpoints creates loops without identifying parallel edges. Actual cut sets contain original identities, so parallel cut edges are counted separately and loops cannot cross a cut.
- `FaultConnected G k a b` quantifies over every finite set of original edge identities of cardinality less than `k`, deletes those identities, and only then tests native walk reachability in the surviving adjacency graph. Simplification is after deletion. It does not replace the multigraph by a simple graph before faults.
- The previously proved converse cut characterization takes the genuinely reachable post-deletion component and proves its original cut is contained in the supplied fault set. It is neither a connectivity oracle nor a path-packing premise. Absent edge identities can occur in a fault set and consume budget, but cannot create links or crossing edges.
- The new core results use finite ambient `V` and `E` as stated. Several helpers omit unnecessary finiteness assumptions explicitly. This packet is not a theorem about arbitrary infinite ambient edge types with merely finite actual edge sets.

## 2. Actual minimal-core selection

`NativeMultigraphCore.lean:11–18` proves that intersecting any cut side with the actual vertex set leaves its edge cut unchanged. This is the essential protection against selecting a phantom ambient vertex as a deficient singleton.

At `:32–49`, cardinal minimization among nonempty deficient subsets of the supplied finite set yields inclusion minimality: every proper nonempty inner set has cut cardinality at least the threshold. The helper does not itself assume the supplied set consists of actual vertices; the final construction supplies precisely that condition.

At `:54–99`, failure of genuine fault connectivity yields a separating small cut. Its side is intersected with the actual vertex set before minimizing. The proof independently establishes:

- inclusion in the actual vertex set;
- properness, because the excluded original terminal remains outside the chosen core;
- closure under every actual fault-connected partner;
- at least two actual vertices, by choosing a retained vertex and its distinct partner from the basicness hypothesis;
- smallness of the core cut and the required lower bounds on all proper nonempty inner subsets.

Basicness ranges over `G.vertexSet`, not ambient `V`. No minimal-core or closure certificate is an extra hypothesis of the final selection theorem. The selected minimal core need not contain the original first terminal, and the statement correctly makes no such claim. Closure is a direct relation-level assertion corresponding to a union of whole connectivity classes; no explicit maximal-island enumeration or packing is constructed.

## 3. Contraction and genuine endpoints

`NativeCoreContraction.lean:12–40` handles every target cut separating retained vertices. When the side excludes `none`, its preimage is a proper nonempty subset of the core. When it contains `none`, the proof complements the side and reverses the endpoints. Thus the outside-side orientation is genuinely covered.

The generic cut-lower-bound helper can talk about ambient core elements without asserting they are graph vertices. `nativeCoreVertex` at `:44–47` supplies the necessary distinction: an explicit `K ⊆ G.vertexSet` hypothesis constructs the actual mapped endpoint from its original preimage. The fault-connectivity theorem at `:51–59` uses these real endpoints and the genuine cut characterization.

The joined existence statement at `:64–77` derives core membership and contracted fault connectivity from the original failed-connectivity/basicness assumptions. It does not assume the desired contracted connectivity. Its conclusion does not retain the inner-minimality field, which remains separately exposed by `native_exists_basic_small_core`; future callers needing the partition budget must preserve or obtain that field rather than infer it from connectivity alone.

## 4. Partition premises and exact counting

`NativeCorePartitionBudget.lean:12–20` gives equality of the actual outside cut and the original core boundary, not just an inequality. Edges whose endpoints both collapse outside become loops and do not enter the boundary.

The budget theorem at `:26–51` assumes a finite nontrivial block type and a surjective assignment from the core. For each block, surjectivity supplies a vertex in it; nontriviality and surjectivity supply a vertex in a different block. These are exactly the witnesses needed for the separating-cut theorem. Empty blocks are not silently treated as nonempty.

The imported exact identity counts each internal crossing identity twice and each outside-boundary identity once. The conclusion counts only edges joining distinct retained-core blocks, not edges through the outside vertex. The stated outside bound is `≤ 2*k`; the selected core's strict `< 2*k` bound is sufficient when this helper is applied at threshold `2*k`.

This helper remains explicitly conditional on smallness and inner minimality. It is not itself a joined basic-instance existence theorem. It also does not assume `K ⊆ G.vertexSet`; the inequality is valid in that more general form, while interpreting it as a partition of actual core vertices requires the membership established by the selection theorem. For positive threshold and a nontrivial surjective partition, a phantom singleton would contradict the inner-cut premise anyway. At zero threshold the inequality is simply zero. These distinctions do not invalidate the theorem.

No spanning tree, tree-packing existence statement, or final forest conclusion appears as a premise or conclusion. Singleton partitions have a zero required crossing count and are outside this nontrivial wrapper; an empty/singleton core cannot surject onto a nontrivial block type.

## 5. Actual graph order versus ambient cardinality

`MultigraphContractionSize.lean:10–17` proves surjectivity of the vertex-type map from an outside preimage. This is a type-level fact. It must not be read as proving that an arbitrary outside ambient vertex is an actual graph vertex.

The needed actual-vertex premise is explicit at `:22–27`: `G.vertexSet = Set.univ`. Combined with the outside preimage, it makes the contracted graph's vertex set equal to the entire target type. The simple-graph embedding case has this invariant definitionally.

The cardinal theorem at `:38–46` states only `card (Option {v // v ∉ K}) < card V` when `2 ≤ K.card`. It concerns contraction of **K**, retaining its complement, rather than the complement contraction used for inner-core connectivity. To interpret this target as a full actual graph, apply the full-vertex lemma to the retained complement; a member of nonempty K supplies the contracted vertex's preimage. The finite complement identity then gives the strict decrease.

Accordingly, this is not yet a standalone actual-order theorem for an arbitrary native graph whose ambient type has nonvertices. The comments and public packet summary preserve this restriction. The existence of a proper actual core alone does not make all ambient vertices actual.

## 6. Degenerate cases and source correspondence

- For `k = 0`, `FaultConnected` is vacuous and every cut lower bound is zero. Failed connectivity cannot hold, so the selected-core existence theorem has no zero-threshold counterexample. No division by the threshold is used.
- Equal terminals have reflexive surviving reachability and cannot be separated by a cut. Empty cores supply no endpoints; singleton cores supply no distinct separable endpoints. The final selection independently proves at least two actual vertices.
- A proper actual core supplies an actual outside vertex even when `G.vertexSet` is a strict subset of V. If a generic retained set has no actual outside vertex, `none` need not be actual; the native endpoint construction and cut identities remain valid without inventing it.
- Empty actual graphs and singleton actual graphs cannot meet the final basic-instance/failed-connectivity hypotheses. Empty edge types or only loops cannot manufacture positive resilience between distinct vertices.

CS09 Lemma 2.4 on printed p.169 is a weighted fractional assertion. The source distinguishes weak deficiency from strict deficiency. These files prove the integral, strictly-small-cut/minimal-inner-cut version needed by the basic-instance construction, for finite native multigraph input. They do not implement the general weighted edge-vector statement or identify all weakly deficient sets with the strict Lean predicate.

CS09 Lemma 2.5 on p.169 includes a numerical crossing-count argument followed by Nash-Williams/Tutte tree-packing existence. The reviewed packet discharges the former under its explicit core premises. The existence step remains open.

The basic-instance selection on pp.169–170 of Theorem 3.1 is matched by actual-vertex basicness, properness, whole-class closure, the two-vertex lower bound, and genuine contracted connectivity. Substituting `2*k` for the connectivity threshold gives the intended source threshold. No Eulerian hypothesis is needed for these isolated components, but that does not establish the Eulerian induction.

## Disposition and remaining scope

Accept the four frozen modules as reviewed integral finite native-multigraph core/contraction/partition components. No production correction is requested. The earlier simple-input restriction is removed for this integral core step.

Still open: the literal weighted fractional lemma, Nash-Williams/Tutte tree-packing existence, Mader splitting and preservation, forest expansion, the complete Eulerian forest-packing join, polynomial runtime and compact multiplicities, and the unrestricted Light EFT upper theorem/full-paper formalization. This PASS does not certify those claims, a full clean rebuild, or exact 68-module CI.
