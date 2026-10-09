# Replication, witness-prefix, probability, and finite unit-cost reduction review

Reviewed 9 October 2026 against the pinned source of Bodwin–Samborska, arXiv:2604.03412v3, and `WITNESS_REPAIR_PLAN.md`. Repository baseline: `c2495aef21970bc125f20c785bd34a3db22d8ad7`. The four reviewed modules were untracked working-tree additions at review time; their SHA-256 hashes below identify the actual snapshots.

**Result: no semantic defect or hidden bridge assumption found in these four components.** Their concrete conclusions support the repaired partial formalization, including the finite unit-cost reduction conditional on its explicit bounded-instance oracle. This is not a review or certification of the complete witness system, adaptive algorithm, runtime, or final flow-cut bound.

This review inspected statements, definitions, proofs, relevant local dependencies, pinned TeX, and existing verification artifacts. It made no changes to Lean sources and ran no compiler, axiom checker, or kernel replay.

## 1. VertexReplication.lean

The graph is the required replication, not an abstract distance surrogate: `Vertex copies` is the sigma type `Σ v, Fin (copies v)`, adjacency is exactly original adjacency of first projections, every clone inherits its original weight, and every clone has cost one (lines 32–42). This matches the splitting operation in `tex/reductions.tex:244–246`.

- `liftPath` preserves actual adjacency, injectivity, internal support, and internal weight. `projectWalk` is a genuine directed walk; `project_path` invokes proved loop erasure and then proves that every surviving original internal vertex comes from a clone internal vertex. Distinct clones of one original vertex, including revisits of an original endpoint, do not invalidate the nonnegative-weight comparison.
- `vertexDistance_le` applies to arbitrary clone endpoints. Exact distance equality is deliberately stated for a consistent section of representatives, as needed for preserving each original demand. `isFractionalCut_all` additionally proves feasibility for all clone pairs above an original demand. Self pairs, direct edges, and unreachable pairs inherit the endpoint-excluding extended-distance semantics from `Basic.lean`.
- `fullFibers Y` contains an original vertex exactly when **all** its clones belong to `Y`. In `lift_avoiding` (line 216), the chosen source and target representatives remain fixed even if deleted, while every internal vertex uses a surviving clone. Therefore the contrapositive cut pullback does not mistake deletion of an endpoint for cutting a demand. Partial fibers produce no selected original vertex.
- The count is exactly `sum copies`; copied total weight is exactly `sum copies(v) * w(v)`. The full-fiber sum is bounded by `Y.card` through an actual sigma-finset inclusion. The cost inequality explicitly assumes `originalCost(v) ≤ copies(v)`, rather than assuming the required conclusion.
- Generic data and accounting permit zero copies. All demand/path-lift statements needing every vertex to exist require `index : ∀ v, Fin (copies v)`; this enforces positive fibers. `firstIndex` constructs it from positivity. Thus vacuous membership of a zero fiber in `fullFibers` cannot create a gap in those cut-transfer theorems.
- The final three port corollaries compose the proved replication, shortcut-contraction, and core-projection transfers. Only cores are contracted; permanent demand ports survive even when original endpoint cores are removed. Zero port weights/costs are accounted for explicitly. These corollaries do not apply an unproved unit-weight rounding theorem to the port graph.

**Scope boundary:** this module supplies static graph/count/cost transfer, not cost normalization, ceiling estimates, a polynomial blowup bound, or the complete unit-cost reduction. Its header states that boundary accurately.

## 2. WitnessPrefix.lean

This is the concrete graph adapter required by Sections 2–3 and interfaces 1–3 of `WITNESS_REPAIR_PLAN.md`. It repairs the printed carrier/prefix/thinning steps in `tex/body.tex:829–898` rather than claiming literal formalization of those flawed steps.

- Heights use frozen `vertexDistance G w s`, in the original graph. `distance_lt_top` proves finiteness along every carrier position before real-valued inequalities are used. Natural-index clamping is explicit; the scan and segment hypotheses keep every relevant index within the genuine carrier.
- `exists_firstCrossing` derives the crossing from the actual carrier and `1 ≤ vertexDistance G w s t`. The record is constructed using the least index at height at least one, not assumed as an oracle. With `N = j-1`, it proves `0 < N`, `N+1 ≤ edgeLength`, all earlier heights strictly below one, and a crossing at `N+1`. No monotonicity of carrier heights is assumed.
- The scan processes exactly indices `0,...,N-1`; the internal predecessor `N` supplies terminal potential and is not scanned. The source is forcibly omitted, and its artificial increment is zero. `height_one` proves that this is valid even if the actual source weight is large or the source belongs to the current cut.
- `p.Avoids X` refers only to internal vertices. It suffices for the outside cap at all charged indices and at `N`; no condition incorrectly forces the original endpoints to survive. `deletedWeight_le` proves equality with the used, nonzero-index prefix sub-sum inside its proof, then injects that sum into `internalVertices ∩ U`. Skipped nondeleted vertices are never charged as deleted.
- `scan_bounds` instantiates every numeric hypothesis of the proved `WitnessThinning.source_scale_bounds`, using `B ≥ 1`, `L ≥ 64B`, the outside cap, and used internal weight below `1/4`. Its lower and upper bounds concern `q-1` consecutive witness-list steps, not the number of graph edges in the carrier.
- The actual mapped list is nodup, lies in the carrier interior outside both `X` and `U`, has heights below one, and has the asserted height separation. Increasing scan indices come from `WitnessThinning.selected_increasing`. `residualSegment` constructs all intermediate vertices and adjacencies in the genuine induced graph on vertices outside `X`; `selected_reachable_in_residual` supplies these paths for increasing selected indices. This remains valid when either labelled carrier endpoint is deleted.

**Scope boundary:** existence of one certified witness list is established. Maximal-family construction, per-label family disjointness, candidate comparison, aggregate witness mass, and downstream charging are separate obligations. Carrier order is available through the increasing index list and its vertex map; there is no separately packaged vertex-list `Sublist` theorem in this module. That is an interface-packaging limit, not a missing semantic argument for the proved results.

## 3. LevelCutProbability.lean

The random experiment and all relevant events are concrete. `uniformLevel = volume.restrict (Icc 0 1)` has proved total mass one. `Real.toNNReal` equals the real sample on that support; its behavior on negative reals therefore changes no probability. Interval-event measurability is proved from measurable order comparisons.

- `uniformLevel_interval` derives the exact probability `min 1 b - a` for extended nonnegative endpoints; `uniformLevel_interval_clipped` rewrites it as `min 1 b - min 1 a`. Subtraction is truncated. Reversed intervals, lower endpoints above one, and infinite lower endpoints give zero; an infinite upper endpoint clips at one. Infinity is not silently converted to real zero.
- `levelHitEvent` is definitionally membership in the actual `levelCut`, with equality to its genuine distance interval. `uniformLevel_levelHitEvent` proves its exact clipped interval-length marginal, hence the bound by `w(v)`. Unreachable vertices are never selected, and zero-weight singleton intervals have probability zero. Boundary levels zero and one are explicitly null singletons.
- `newLevelCut_cost_indicator_sum` expands the cost of `levelCut \ X` pointwise. Measurability and the exact nonnegative integral then follow by finite indicator integration, yielding the weighted bound and its unit-cost cardinality specialization. Real-valued integrability is established before the ordinary expected-cost bound is exported. There is no assumed linearity-of-expectation bridge or assumed marginal law.
- The separation event uses the paper's closed interval from `tex/body.tex:444–449`; its exact probability is the clipped distance-difference value. `LevelResidualPath` requires every vertex, **including both endpoints**, of an actual simple path to survive full deletion. This is genuine residual connectivity, distinct from internally avoiding a labelled carrier. The finite-cut-fiber argument proves measurability even for the existential path event.
- `levelSeparationEvent_no_residualPath` proves pointwise destruction of that connectivity. Strict-upper levels use the actual adjacent-crossing cut theorem. At equality with the upper endpoint, the target itself is selected, which suffices for full residual deletion. It does not falsely assert that target deletion alone internally cuts the original pair. The complement-measure calculation then proves the one-round survival upper bound `1 - separationValue`.
- The imported deterministic `LevelCut` results separately prove internal cutting of a selected feasible demand at every level in `[0,1]`, including both boundaries. The first-edge distance-zero argument rules out charging the selected source as the internal cut vertex.

**Scope boundary:** these are single-level, fixed-weight, fixed-current-cut results. They do not prove uniform demand sampling, independence between rounds, a stopped permutation/epoch law, survival after adaptively many rounds, or an overall expected algorithmic cost. Those hypotheses cannot be obtained by conditioning on eventual epoch survival.

## 4. UnitCostReduction.lean

The final theorem, `round_of_bounded_unit_oracle` (line 339), takes an arbitrary feasible demand family and returns an actual original internal vertex cut with cost at most `6αC`, where `n = card(V)`, `W = sum w`, and `C = sum c(v)w(v)`. Its one substantive external mathematical input is explicitly `BoundedUnitRoundingOracle(4n², 3W, α)`. Every transformation connecting that oracle to the original graph is proved.

1. **Preparation.** The removed set consists of original cores with `w(v) ≤ 1/(2n)`. Its total weight is at most one half. Removal acts on the port graph through the concrete shortcut construction; all demand ports survive. Doubling and then clipping remaining weights at one preserves fractional feasibility. Clipping is proved by the two exhaustive path cases: an internal vertex of weight at least one supplies the whole threshold, or every internal weight is unchanged. Prepared integral cuts pull back at exactly the prepared cost.
2. **Prepared bounds.** Writing `W′, C′` for prepared total weight and fractional cost, the module proves `W′ ≤ 2W`, `W′ ≤ n`, `C′ ≤ 2C`, and at most `3n` prepared vertices. For `n>0`, each surviving core has prepared weight at least `1/n`; ports have zero prepared cost. Thus every prepared vertex obeys `c′(v) ≤ n c′(v)w′(v)`. No positive port-weight assumption is smuggled into the copy-count bound.
3. **Normalization and actual copies.** When `C′>0`, `scale = W′/(2C′)>0`, and normalized cost `ĉ = scale*c′` has fractional objective `W′/2`. The fiber size is `max(1, ceil(ĉ(v)))`, so even a zero-cost port retains a representative. The proved inequalities `ĉ(v) ≤ copies(v) ≤ ĉ(v)+1` suffice directly; there is no missing intermediate cost-floor estimate.
4. **Exact constants.** Summing the positive-core charging inequality gives `sum ĉ ≤ nW′/2`. Hence the actual cloned cardinality is at most `3n+nW′/2 ≤ 3n+n²/2 ≤ 4n²` for `n≥1`. The actual copied weight is at most `W′+W′/2 = 3W′/2 ≤ 3W`. Full-fiber pullback has normalized cost at most the deleted clone count; a cut of size at most `αW″` therefore has prepared original-cost pullback at most `3αC′`. The positive scale is explicitly canceled, and `C′≤2C` gives `6αC`.
5. **Demand and objective connection.** The oracle is called on the constructed sigma-type clone graph and copied weights, with the preceding cardinality/weight proofs. Prepared demands are lifted to fixed representatives and proved fractionally feasible, hence are among the oracle's threshold demands. Full-fiber pullback, shortcut pullback, and core pullback then give original integral feasibility. The normalized cost estimate is transported through the exact prepared-cost identity.
6. **Degenerate branches.** If prepared fractional cost is zero, `zero_cost_cut` uses the proved coarse threshold cut from `VertexRounding.lean`; its cost is zero and it hits every actual threshold path internally. If `n=0`, the theorem returns the empty cut directly. Thus neither branch divides by zero or requires the oracle. Original zero weights, zero costs, disconnected demands, and `α=0` are allowed by the statements.

`BoundedUnitRoundingOracle` quantifies over all finite graphs in the same universe with cardinality **at most** `4n²` and total weight **at most** `3W`, and guarantees a cut of size at most `α` times that instance's actual total weight. This is a transparent bounded-domain assumption, not an assumption of the desired original weighted cut, and not an unsupported monotonicity claim about an exact-parameter gap function. `hasVertexRoundingFactor_of_bounded_unit_oracle` correctly exposes it unchanged while quantifying the original rounding guarantee over every nonnegative cost function.

**Source relationship and scope:** this proves a repaired finite existence reduction corresponding to `tex/reductions.tex:213–246,335–392`. The simultaneous core removal plus permanent-port construction preserves the original demand endpoints; the exact constants account for the extra ports. It does not establish polynomial-time construction/optimization, prove the unit-cost oracle, derive a headline asymptotic bound, or complete the other edge/vertex/uniform-weight reductions.

## Verification evidence and limits

Existing artifacts record successful compilation and kernel replay for all four modules. The replication and prefix axiom scripts enumerate all declarations belonging to each module and report 55 and 113 declarations, respectively, permitting only `propext`, `Classical.choice`, and `Quot.sound`.

The probability axiom script instead explicitly prints the axioms of all 34 named source declarations. A read-only source/script comparison found 34 declarations, 34 matching print commands, and no omissions or extras; the log shows only the same standard axioms. This is complete named-source coverage, but its script does not independently enumerate compiler-generated declarations. Its separate kernel-replay log reports success. This documentation distinction is not a discovered mathematical defect.

The unit-cost audit log reports all 572 `DirectedFlowCutGap` declarations in its import closure passed the standard-axiom allowlist, and its kernel-replay log reports success. Its compile log contains non-fatal linter warnings.

The source review found no `sorry`, `admit` proof, custom axiom, or unsafe declaration in the four modules or the inspected supporting modules. Existing logs are evidence from earlier runs; this review does not claim a fresh build or independently establish source-to-object identity. Future edits require renewed verification against their new hashes.

## Exact reviewed snapshots

Module paths below are relative to `repo/Improved Upper Bounds for the Directed Flow-Cut Gap/DirectedFlowCutGap/`. Source paths are relative to `sources/2604.03412v3/`.

| File | SHA-256 |
|---|---|
| `VertexReplication.lean` | `91d123ecff052dcc24d3c96883fb95a06fd9047884639ebec9beb3018e3d0307` |
| `WitnessPrefix.lean` | `9bdfa74216cb531f6b2ef79a1466b9f562d233713655ca414b90c7c68b3cada7` |
| `LevelCutProbability.lean` | `8990974de210df6c799b9dbaa44fb276a16db2fcf9317dff83fb97bf40fc8e8d` |
| `Basic.lean` | `16ec9329854c93a175d9205a897b8f2e80c99d26aef4b3af4db7e11b48999521` |
| `PathExtraction.lean` | `abc2c7bcda89b3b7ee2d37dd254f4357724585ebc9963697304917899473c63e` |
| `ShortcutContraction.lean` | `414e3734bfeba918b89f1edf1673678b9bc7acada4cdfb4bdd246de42facc5db` |
| `TerminalPorts.lean` | `22bbef774144a67c6d8b631dd8ec5490846d46a7d5a530c18227df5d43bf5b88` |
| `LevelCut.lean` | `547a6b4ab2ef81294bb07ef4fe3965bd21131c353814494e20e443946561acd6` |
| `WitnessThinning.lean` | `8a11a4e1f334361bca96474e8557e6d2faa6a786962a5e9f17dac48ba50cc33d` |
| `UnitCostReduction.lean` | `ead649a30cb6423f56b5c4012bbf23385504c3c4c478a69f674ef8aeaa732843` |
| `VertexRounding.lean` | `94cc950f8e963599eb4e1c2ab443c643e976e4ba39dc0872da57cad58ae15662` |
| Source `tex/body.tex` | `6261f6fe94e1ecd7084107a67f9da4550f4507b1e1e6cd0eea977f91e3667325` |
| Source `tex/reductions.tex` | `d848044d8d074305eefde28f5080dc0c5b2622224edde16952407e12ac46fe4a` |
| Source `WITNESS_REPAIR_PLAN.md` | `8900d2fd3bc25595ee12e69d9bf59674a06947321dbd7c32e5dc7581f701dcee` |
| Source `paper.pdf` | `a0f6f3a73acbfbb1c82fe04d739283c87b3e34d7f6ff850543dcb42b702c3a46` |
| Source `paper.tar.gz` | `9d76894e97711df52b099d4f77061c7b5737a86958fc67d2f981b1be1680ce9e` |
| Repository `lean-toolchain` | `8733782dc070a99b312039cda424f601b80f3be6f6f512627da5ba25adc27632` |
| Repository `lake-manifest.json` | `615d78a994009475b0e34cd0cd67325b2d863ae37e9f42d8ded7f9d575bf4b2f` |
