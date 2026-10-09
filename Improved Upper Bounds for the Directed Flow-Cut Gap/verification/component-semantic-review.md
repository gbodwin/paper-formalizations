# Directed flow-cut gap: component semantic review

Reviewed 9 October 2026 against the pinned TeX for Bodwin–Samborska, arXiv:2604.03412v3. Baseline commit: `f2c7ec9ab27cac3804f0cdd46680901b4808477c`.

**Result:** No mathematical mismatch, concealed conclusion, or unjustified positivity/monotonicity assumption was found in the reviewed component statements and proofs. They support a clearly labelled partial checkpoint. This review does not certify the headline flow-cut bound or the complete repairs of Lemmas 18/26 and Theorems 29/33.

This was an independent, read-only source review. No Lean commands were run and no proof files were changed. Compilation, axiom auditing, and kernel replay are separate checks owned by the verification worker. Their successful execution should be recorded against the same final source hashes before publication.

## Findings and scope

1. **Path extraction is genuine loop erasure.** `DirectedWalk` contains actual directed edges. Induction on a walk either prepends a fresh source or keeps the suffix beginning at an existing occurrence of that source. Thus `DirectedWalk.exists_simplePath` proves the same endpoints and support containment without assuming a simple replacement. Composition constructs and appends actual walks before extracting a path. Nonnegative weights justify cost comparison. `vertexDistance_triangle` correctly includes the common endpoint's weight; it uses proved finite attainment, and disconnected legs are handled in extended nonnegative reals. Repeated endpoints, zero-length paths, self-loops, zero weights, and an empty vertex type do not introduce an omitted hypothesis.

2. **The zero-weight oracle is derived.** `mw_oracle_avoids_zero` queries the original all-nonnegative-cost oracle after assigning each zero-weight item cost `α * mwPotential w c + 1`. The weighted budget is unchanged, so any selected zero-weight item would exceed it. Neither avoidance nor a family with the desired marginals is supplied as a premise. The positive auxiliary weights and strengthened admissibility predicate are then used only to invoke the already proved recurrence. Positive coordinates retain the original bound; zero coordinates have frequency zero. `α = 0` is treated separately by proving the empty set admissible. The empty item type and an all-zero weight vector are included. The oracle remains an explicit substantive hypothesis, and the auxiliary horizon is not a polynomial-time guarantee.

3. **Terminal ports preserve the endpoint convention exactly.** Source ports have no incoming edges; sink ports have no outgoing edges. Consequently only cores can be internal path vertices or useful cut vertices. Original paths lift with exactly their internal vertices tagged as cores. The direct source-to-sink self edge represents the original zero-length path. Projection first gives a walk, removes reflexive steps, and uses genuine loop erasure; it does not assume the projection is injective. Projection may remove charged endpoint cores, which explains the nonincreasing weight direction. The two directions yield exact distance and cut equivalences, including unreachable and self pairs. Pulling back an arbitrary cut discards zero-cost ports and preserves cost exactly. Vertex count is exactly `3n`; total weight and fractional objective are unchanged. These are static construction and transfer results. They do not yet prove that a later contraction procedure preserves the ports, restores fractional feasibility, or has the claimed size/cost bounds. Demand equivalences concern the explicitly mapped demand family, not an assertion that every possible transformed demand has an original counterpart.

4. **Greedy thinning charges the right indices.** The selected list is produced by `scan`, rather than postulated. Its indices increase, avoid deletion, and have the stated distance separation. `deletedWeight` contains only indices satisfying `deleted`; a skipped surviving index is controlled by its failed threshold test in `scan_potential`. Only upper one-step increments are assumed, so distances may decrease. The scan processes `0,...,n-1` and estimates the final value `d n`; this indexing is explicit. `source_scale_bounds` derives the bounds on the actual selected edge count, including the natural-number subtraction check, from `B ≥ 1`, `L ≥ 64B`, the terminal lower bound, the deleted-weight allowance, and the processed-prefix upper bound. It does not derive those graph-specific premises. In particular, the paper's “last vertex with distance at most one” does not by itself establish that every earlier distance is at most one when distances can decrease. An appropriate prefix argument remains necessary in the graph application.

5. **The existing foundations match the stated problem.** `Basic` excludes both endpoints from path weights and cutting, and proves deletion equivalence only with demand endpoints retained. `MultiplicativeWeights` constructs actual oracle outputs and counts their membership; its common scale makes the logarithm estimate valid. `PackingCovering` is attained finite sum-packing/covering duality, with explicit nonnegative capacities and nonempty resource sets. The latter condition is essential: an empty-resource path would make packing unbounded and covering infeasible. Empty path families and zero capacities are otherwise supported. Definition-level facts such as `isFractionalCut_thresholdDemands` are intentionally immediate and do not supply the missing rounding oracle or headline theorem.

6. **The graph duality bridge has the correct domain.** `VertexFlow` indexes actual simple paths by their actual demand pairs, counts only internal-vertex loads, and proves exact feasibility/objective identifications with `PackingCovering`. Its strong duality assumes only an available feasible fractional cut, not an optimum or the desired equality. Nonempty path resources are derived from that assumption. Self demands and direct-edge demands are explicitly shown outside this feasible-cut domain; empty/unreachable demand sets and zero capacities are treated separately. This is a path-based directed vertex sum-multiflow theorem. It does not assert an edge-flow theorem, concurrent-flow theorem, or a separate equivalence with an edge-conservation formulation.

## Checkpoint documentation

The reviewed baseline documentation still lists loop erasure/attainment, zero-weight extension, and the terminal-port construction as pending or under investigation. Update those descriptions to the precise component results above while retaining the unresolved graph application, contraction, preprocessing, and runtime obligations. `WitnessThinning` is a replacement numerical charging argument; it should not be described as a completed graph witness lemma. The final publication gate should also check the aggregate imports and verification results for all files included in the checkpoint.

The source passages compared were `body.tex` lines 30–40 (vertex endpoint convention) and 823–949 (witness construction and charging), `reductions.tex` lines 209–250 (unit-cost reduction/contraction) and 683–760 (sampling reduction), and `intro.tex` lines 56–59 (sum-multiflow objective).

## Reviewed declarations and source fingerprints

The following inventory records the exact public theorem/lemma names in the reviewed files. Supporting definitions and private helpers were also read. SHA-256 fingerprints identify the reviewed source snapshot; compilation status must be supplied separately.

### Basic.lean

SHA-256: `16ec9329854c93a175d9205a897b8f2e80c99d26aef4b3af4db7e11b48999521`

- `DirectedFlowCutGap.SimplePath.mem_vertices`
- `DirectedFlowCutGap.SimplePath.source_mem_vertices`
- `DirectedFlowCutGap.SimplePath.target_mem_vertices`
- `DirectedFlowCutGap.SimplePath.card_vertices`
- `DirectedFlowCutGap.SimplePath.edgeLength_lt_card`
- `DirectedFlowCutGap.SimplePath.mem_internalVertices`
- `DirectedFlowCutGap.SimplePath.source_not_internal`
- `DirectedFlowCutGap.SimplePath.target_not_internal`
- `DirectedFlowCutGap.SimplePath.refl_internalVertices`
- `DirectedFlowCutGap.SimplePath.edge_internalVertices`
- `DirectedFlowCutGap.SimplePath.weight_congr`
- `DirectedFlowCutGap.SimplePath.weight_mono`
- `DirectedFlowCutGap.SimplePath.weight_unit`
- `DirectedFlowCutGap.SimplePath.refl_weight`
- `DirectedFlowCutGap.SimplePath.edge_weight`
- `DirectedFlowCutGap.SimplePath.weight_zero`
- `DirectedFlowCutGap.le_vertexDistance_iff`
- `DirectedFlowCutGap.coe_le_vertexDistance_iff`
- `DirectedFlowCutGap.vertexDistance_le_weight`
- `DirectedFlowCutGap.vertexDistance_eq_top_iff`
- `DirectedFlowCutGap.vertexDistance_self`
- `DirectedFlowCutGap.vertexDistance_of_adj`
- `DirectedFlowCutGap.vertexDistance_congr_endpoints`
- `DirectedFlowCutGap.vertexDistance_mono`
- `DirectedFlowCutGap.not_cutsPair_iff`
- `DirectedFlowCutGap.cutsPair_erase_endpoints_iff`
- `DirectedFlowCutGap.not_cutsPair_subset_endpoints`
- `DirectedFlowCutGap.cutsPair_mono`
- `DirectedFlowCutGap.not_cutsPair_self`
- `DirectedFlowCutGap.not_cutsPair_of_adj`
- `DirectedFlowCutGap.isFractionalCut_iff`
- `DirectedFlowCutGap.isFractionalCut_thresholdDemands`
- `DirectedFlowCutGap.retained_iff_not_mem_erase`
- `DirectedFlowCutGap.SimplePath.avoids_iff_retained`
- `DirectedFlowCutGap.SimplePath.forgetDeletion_avoids`
- `DirectedFlowCutGap.endpointDeletedGraph_path_iff`
- `DirectedFlowCutGap.cutsPair_iff_endpointDeletedGraph`
- `DirectedFlowCutGap.weightedCost_unit`
- `DirectedFlowCutGap.cutCost_unit`

### MultiplicativeWeights.lean

SHA-256: `f5d00d7d54b6bd141550cfcb1fd40c3db79b6a25a84ad4951c460521f2cee3f4`

- `DirectedFlowCutGap.mwCount_zero`
- `DirectedFlowCutGap.mwCount_succ`
- `DirectedFlowCutGap.mwCost_pos`
- `DirectedFlowCutGap.mwCost_succ`
- `DirectedFlowCutGap.mwPotential_succ`
- `DirectedFlowCutGap.mwPotential_le`
- `DirectedFlowCutGap.mwCost_mul_weight_le`
- `DirectedFlowCutGap.mwCount_log_bound`
- `DirectedFlowCutGap.mw_half_le_log_one_add`
- `DirectedFlowCutGap.mwCount_le`
- `DirectedFlowCutGap.mwCount_le_four`
- `DirectedFlowCutGap.mwCount_eq_card`
- `DirectedFlowCutGap.mwCount_eq_fin_card`
- `DirectedFlowCutGap.mwOracleChoice_spec`
- `DirectedFlowCutGap.exists_mw_family`
- `DirectedFlowCutGap.exists_mw_family_marginals`
- `DirectedFlowCutGap.exists_mw_family_of_min_weight`
- `DirectedFlowCutGap.exists_finite_mw_family`

### PackingCovering.lean

SHA-256: `29a8f91ef1a8db39fa222f03fac3c51d00e68bbe070a89bfda42bc112ea1141a`

- `DirectedFlowCutGap.PackingCovering.incidence_nonneg`
- `DirectedFlowCutGap.PackingCovering.pathWeight_eq_sum`
- `DirectedFlowCutGap.PackingCovering.load_eq_sum_filter`
- `DirectedFlowCutGap.PackingCovering.load_nonneg`
- `DirectedFlowCutGap.PackingCovering.pairing_identity`
- `DirectedFlowCutGap.PackingCovering.weak_duality`
- `DirectedFlowCutGap.PackingCovering.zero_isPacking`
- `DirectedFlowCutGap.PackingCovering.one_isCovering`
- `DirectedFlowCutGap.PackingCovering.packing_coordinate_bound`
- `DirectedFlowCutGap.PackingCovering.isClosed_packings`
- `DirectedFlowCutGap.PackingCovering.exists_max_packing`
- `DirectedFlowCutGap.PackingCovering.clip_isCovering`
- `DirectedFlowCutGap.PackingCovering.clip_value_le`
- `DirectedFlowCutGap.PackingCovering.isClosed_coverings`
- `DirectedFlowCutGap.PackingCovering.exists_min_covering`
- `DirectedFlowCutGap.PackingCovering.convex_unitSimplex`
- `DirectedFlowCutGap.PackingCovering.isCompact_unitSimplex`
- `DirectedFlowCutGap.PackingCovering.single_mem_unitSimplex`
- `DirectedFlowCutGap.PackingCovering.nonneg_coefficients_of_bounded_orthant`
- `DirectedFlowCutGap.PackingCovering.functional_eq_sum`
- `DirectedFlowCutGap.PackingCovering.covering_certificate`
- `DirectedFlowCutGap.PackingCovering.strong_duality`

### PathExtraction.lean

SHA-256: `abc2c7bcda89b3b7ee2d37dd254f4357724585ebc9963697304917899473c63e`

- `DirectedFlowCutGap.SimplePath.finiteCode_injective`
- `DirectedFlowCutGap.SimplePath.suffix_vertices_subset`
- `DirectedFlowCutGap.SimplePath.prepend_vertices`
- `DirectedFlowCutGap.DirectedWalk.source_mem_vertices`
- `DirectedFlowCutGap.DirectedWalk.append_vertices`
- `DirectedFlowCutGap.DirectedWalk.exists_simplePath`
- `DirectedFlowCutGap.DirectedWalk.exists_of_sequence`
- `DirectedFlowCutGap.DirectedWalk.exists_simplePath_weight_le`
- `DirectedFlowCutGap.SimplePath.exists_directedWalk`
- `DirectedFlowCutGap.SimplePath.exists_composition`
- `DirectedFlowCutGap.SimplePath.internalVertices_subset_of_composition`
- `DirectedFlowCutGap.SimplePath.weight_le_of_composition`
- `DirectedFlowCutGap.SimplePath.exists_composition_weight_le`
- `DirectedFlowCutGap.nonempty_simplePath_iff_directedWalk`
- `DirectedFlowCutGap.vertexDistance_eq_top_iff_no_walk`
- `DirectedFlowCutGap.exists_minimumWeight_path`
- `DirectedFlowCutGap.vertexDistance_attained`
- `DirectedFlowCutGap.vertexDistance_triangle`

### ZeroWeights.lean

SHA-256: `5f22048c0583355d9400c4d314a5a4e2bc92a74acbd39ed65e68898be3fd06a4`

- `DirectedFlowCutGap.mwPositiveWeight_pos`
- `DirectedFlowCutGap.le_mwPositiveWeight`
- `DirectedFlowCutGap.mwPositiveMinimum_pos`
- `DirectedFlowCutGap.mwPositiveMinimum_le`
- `DirectedFlowCutGap.mw_empty_admissible_of_zero`
- `DirectedFlowCutGap.mw_oracle_avoids_zero`
- `DirectedFlowCutGap.mwNonnegativeHorizon_pos`
- `DirectedFlowCutGap.exists_nonnegative_mw_family`
- `DirectedFlowCutGap.exists_finite_nonnegative_mw_family`

### TerminalPorts.lean

SHA-256: `22bbef774144a67c6d8b631dd8ec5490846d46a7d5a530c18227df5d43bf5b88`

- `DirectedFlowCutGap.TerminalPorts.extend_core`
- `DirectedFlowCutGap.TerminalPorts.extend_source`
- `DirectedFlowCutGap.TerminalPorts.extend_sink`
- `DirectedFlowCutGap.TerminalPorts.no_incoming_source`
- `DirectedFlowCutGap.TerminalPorts.no_outgoing_sink`
- `DirectedFlowCutGap.TerminalPorts.source_not_internal`
- `DirectedFlowCutGap.TerminalPorts.sink_not_internal`
- `DirectedFlowCutGap.TerminalPorts.internal_is_core`
- `DirectedFlowCutGap.TerminalPorts.liftPositive_internalVertices`
- `DirectedFlowCutGap.TerminalPorts.exists_lift`
- `DirectedFlowCutGap.TerminalPorts.sum_extend_image`
- `DirectedFlowCutGap.TerminalPorts.exists_lift_weight`
- `DirectedFlowCutGap.TerminalPorts.exists_projection`
- `DirectedFlowCutGap.TerminalPorts.exists_projection_weight_le`
- `DirectedFlowCutGap.TerminalPorts.vertexDistance_eq`
- `DirectedFlowCutGap.TerminalPorts.mem_corePreimage`
- `DirectedFlowCutGap.TerminalPorts.corePreimage_image`
- `DirectedFlowCutGap.TerminalPorts.cutsPair_core_only_iff`
- `DirectedFlowCutGap.TerminalPorts.cutsPair_iff`
- `DirectedFlowCutGap.TerminalPorts.cutsPair_image_iff`
- `DirectedFlowCutGap.TerminalPorts.isFractionalCut_iff`
- `DirectedFlowCutGap.TerminalPorts.isIntegralCut_iff`
- `DirectedFlowCutGap.TerminalPorts.cutCost_corePreimage`
- `DirectedFlowCutGap.TerminalPorts.card_vertex`
- `DirectedFlowCutGap.TerminalPorts.totalWeight_extend`
- `DirectedFlowCutGap.TerminalPorts.weightedCost_extend`

### WitnessThinning.lean

SHA-256: `8a11a4e1f334361bca96474e8557e6d2faa6a786962a5e9f17dac48ba50cc33d`

- `DirectedFlowCutGap.WitnessThinning.scan_zero`
- `DirectedFlowCutGap.WitnessThinning.deletedWeight_zero`
- `DirectedFlowCutGap.WitnessThinning.deletedWeight_succ`
- `DirectedFlowCutGap.WitnessThinning.selected_mem`
- `DirectedFlowCutGap.WitnessThinning.selected_increasing`
- `DirectedFlowCutGap.WitnessThinning.selected_le_last`
- `DirectedFlowCutGap.WitnessThinning.selected_separated`
- `DirectedFlowCutGap.WitnessThinning.count_mul_step_le`
- `DirectedFlowCutGap.WitnessThinning.last_le`
- `DirectedFlowCutGap.WitnessThinning.scan_potential`
- `DirectedFlowCutGap.WitnessThinning.final_distance_le`
- `DirectedFlowCutGap.WitnessThinning.source_scale_arithmetic`
- `DirectedFlowCutGap.WitnessThinning.source_scale_bounds`

### VertexFlow.lean

SHA-256: `76d158ba94679184462a2d32e74f8f31721241608eac8140e279791cae20f509`

- `DirectedFlowCutGap.VertexFlow.incidence_load_eq`
- `DirectedFlowCutGap.VertexFlow.incidence_pathWeight_eq`
- `DirectedFlowCutGap.VertexFlow.packingValue_eq`
- `DirectedFlowCutGap.VertexFlow.coveringValue_eq`
- `DirectedFlowCutGap.VertexFlow.isPacking_iff`
- `DirectedFlowCutGap.VertexFlow.isCovering_iff`
- `DirectedFlowCutGap.VertexFlow.resources_nonempty_of_fractionalCut`
- `DirectedFlowCutGap.VertexFlow.exists_fractionalCut_iff`
- `DirectedFlowCutGap.VertexFlow.no_fractionalCut_of_empty_resources`
- `DirectedFlowCutGap.VertexFlow.no_fractionalCut_of_self`
- `DirectedFlowCutGap.VertexFlow.no_fractionalCut_of_adj`
- `DirectedFlowCutGap.VertexFlow.weak_duality`
- `DirectedFlowCutGap.VertexFlow.strong_duality`
- `DirectedFlowCutGap.VertexFlow.isEmpty_pathIndex_iff`
- `DirectedFlowCutGap.VertexFlow.value_eq_zero_of_unreachable`
- `DirectedFlowCutGap.VertexFlow.zero_isFractionalCut_of_unreachable`
- `DirectedFlowCutGap.VertexFlow.zero_isFractionalCut_empty`
- `DirectedFlowCutGap.VertexFlow.value_eq_zero_empty`
- `DirectedFlowCutGap.VertexFlow.value_eq_zero_of_zero_capacity`

### Pinned paper sources

- `main.tex`: `9f285c994283689c1a665ed74150281d6132d5507d6ee4c812d7778ffdb2b9ef`
- `body.tex`: `6261f6fe94e1ecd7084107a67f9da4550f4507b1e1e6cd0eea977f91e3667325`
- `reductions.tex`: `d848044d8d074305eefde28f5080dc0c5b2622224edde16952407e12ac46fe4a`
- `intro.tex`: `9619d3bab7a12edf3cc329880207681a3ad3084bef81e58ca3c7bb1c86bcc790`

The initial corrections record used for context had SHA-256 `6c8cc61382f5fe97c07c68f6c4247a4bd526bffaf9c0cd17c4c84edf2c898c4f`; documentation is being updated separately. The final reviewed `Basic.lean` fingerprint above includes the checked comment-only update that points to `PathExtraction.lean`.
