# Adaptive epoch and probability model: semantic review

Reviewed 9 October 2026. Repository HEAD at review time: `19d2d0bcae17f88e040533ce9e34dbb0ac6856f8`. The exact reviewed source snapshots are identified by SHA-256 below; HEAD alone is not the identity of a working-tree file.

**Result: no semantic defect found in the frozen `AdaptiveEpoch.lean` and `AdaptiveRounding.lean` model.** They construct an actual stopped epoch, its exact finite sampling law, and a finite outer PMF recursion whose supported outputs are valid integral cuts at the stated fuel. The active-prefix coupling and unconditional truncated expected-cardinality bound are substantive proved results. They do **not** prove the complete approximation bound, the total expected size of the adaptive output, high-probability size guarantees, or an implementable running time.

This was a read-only review of Lean statements, definitions, proofs, dependencies, and existing verification artifacts. No proof source was edited and no compiler, axiom-audit, or kernel-replay process was run during this review. The report is a semantic assessment, not a new build certificate.

## 1. The state and the actual epoch scan

`CandidateSchedule.State` (lines 31–39) retains the original demand labels, a subset of labels still to process, the actual selected vertex set, per-label feasible fractional cuts, an outside-cut cap, and correctness for every processed original label. Feasibility and correctness use the original graph and internal-vertex cutting. They do not silently discard a demand when a terminal is selected.

The candidate is selected from the proved attained minimum, rather than supplied by an optimization oracle (`CandidateSchedule` 55–80). `Ready` means zero optimum or current mass at most `r` times the optimum. Stabilization finds the first ready state by actual repeated installations; an installation multiplies the cap scale by four and uses the candidate weights. The proofs of existence and termination use a geometric decrease and the unit lower bound for an unresolved fractional cut.

In `AdaptiveEpoch` 25–42, `Active r M S` requires all three of:

- readiness of the current candidate gate;
- nonzero current optimum;
- `M ≤ r * S.mass`, with `M` the recorded epoch-start mass.

The scan checks this condition **before every performed round**, together with membership of the next label. If the test fails, it returns the current state and performs none of the remaining samples. The scan contains no installation. Thus a failed gate stops before a weight change, and the next outer stabilization supplies any installation. A mass split occurs when current mass is strictly below `M/r`; equality remains active. No equality between current and starting mass is assumed.

For arbitrary caller-supplied lists, the scan can also stop because the next label is absent. That extra case is excluded in the actual sampled ordering: `sampleOrder_nodup` and `sampleOrder_toFinset` prove a duplicate-free enumeration of exactly the initial remaining labels, and every performed round erases precisely its own label. `run_stopped` therefore proves that a complete legal ordering ends at one of the specified activity boundaries, including exhaustion and zero optimum.

`run_execution` (48–60) embeds every round in `CandidateSchedule.Execution`, whose sampling constructor requires readiness, positive optimum, a remaining label, and a level in the closed unit interval. The deterministic round (CandidateSchedule 305–336) unions the actual original-graph level cut into the current cut, erases the label, preserves frozen weights and scale, preserves caps/feasibility, and proves the newly processed demand internally cut. Closed endpoints zero and one are permitted by the imported deterministic level-cut theorem.

The scan's invariants are proved, not required of a caller: unchanged weights and scale; nonincreasing mass; growing cut; shrinking remaining set; and the exact identity `remaining_after.card + rounds = remaining_before.card` (AdaptiveEpoch 73–121). Positive stabilized epochs with `r ≥ 1` necessarily perform a first real round, and hence strictly decrease remaining-label count (219–247). This is deterministic progress, independent of probability support.

## 2. Mass, cap, and subset-value bridges

`remaining_value_le` (AdaptiveEpoch 299–308) compares the separation-value sum over the actual remaining labels and current weights with the sum over the epoch-start labels and weights. It first rewrites by the proved frozen-weight identity, then uses subset monotonicity of a nonnegative finite sum. The direction is correct for transferring a lower bound on a current sum to the epoch-start sum. It supplies no such lower bound itself and does not instantiate a charging or witness theorem.

`next_start_mass` (284–297) proves `r * mass(next_stabilized_start) ≤ M` under explicit hypotheses: current mass is at most `M`, the epoch is inactive, and the next stabilized optimum is positive. If readiness failed, at least one true installation supplies the factor-`r` decrease. If readiness holds, positivity at the next start rules out the old zero optimum; inactivity then forces the mass-split inequality. Further stabilization cannot increase mass. The actual epoch supplies the first two premises through `run_mass_le` and `epoch_stopped`; this composition is used in `solve_support_zero_of_mass_fuel`.

Cap growth is charged to installations, never to analysis splits. `Execution.scale_eq` gives `scale_final = 4^k * scale_initial` for the installation count `k`. The global installation bound uses the last installation's unit mass lower bound, so later rounds reducing mass to zero do not invalidate it. `solve_support_scale_le` correctly invokes this trace bound with the explicit premise `S.mass < r^(J+1)` and `r > 1`; it concludes `T.scale ≤ 4^J * S.scale`. It does not choose `J`, bound initial mass by graph parameters at this call site, or assert a universal absolute cap independent of the input state. The separate `CandidateSchedule.initial_mass_le_cube` is available for the genuine initial state with `L ≥ 1`.

## 3. The finite law is the real product pushforward

`FiniteCutLaw.Outcome V` contains the actual finite vertex set and has the discrete sigma algebra. `draw G w s d` is exactly `levelCut G w s d.toNNReal`. `cutMeasure` is the measurable pushforward of `uniformLevel = volume.restrict (Icc 0 1)`, and `cutPMF` is its exact PMF. `cutPMF_apply` identifies each atom with the measure of its level-cut fiber. This is not a uniform distribution on possible cuts and not arbitrary assigned weights.

`AdaptiveRounding.Sample` (24–25) consists of a permutation and one finite cut outcome per current label. `sampleMeasure` (28–31) is the product of a genuinely uniform permutation measure and the product of the actual cut measures. `sampleMeasure_eq_map` (56–68) proves exact equality with the pushforward of `FrozenEpochProbability.experiment`: independent real uniform levels together with an independent uniform permutation. The proof uses the coordinatewise product-map theorem and the product-of-maps identity. The relevant Mathlib theorem actually asserts equality of the mapped product measures; no independence premise about representatives or adaptive histories is substituted for it.

`samplePMF_apply` displays the exact atom probability as the inverse permutation count times the product of the individual cut probabilities. `sample_expectation_eq_integral` and `sample_probability_eq` transfer arbitrary finite-sample real test functions and events to this real experiment. In particular, virtual cuts agree definitionally after `drawSample`, and both the frozen expected-new-cardinality and residual-path survival bounds transfer exactly (111–145).

The frozen survival theorem is itself grounded in the real product law: independent avoidance probabilities multiply; an actual surviving residual path avoids all sampled separation events; equal permutation-fiber cardinalities give the uniform fixed-size subset average; and the finite survival inequality bounds that average exponentially. `LevelResidualPath` requires every vertex of the path, including its endpoints, to survive. It is not interchangeable with the internal-cut predicate for the original labelled demand.

## 4. Representative levels are used only to reproduce cuts

`FiniteCutLaw.support_exists_level` proves that a positive-mass cut has a realizing level in `[0,1]`, by intersecting its positive-measure fiber with the real uniform measure's support. `realizeLevel` chooses one such level, and returns zero off support. No theorem claims these chosen levels are uniformly distributed.

`sample_support_coordinate` proves that every coordinate of a supported joint sample is supported in its cut PMF. `sampleLevels_cut` then proves exact reproduction of that coordinate's cut. The frozen weights used to realize levels are precisely the weights retained by each scan round.

The actual transition's data depend on a level only through this cut: the updated cut is a union, the selected label is erased, and the weights and scale remain fixed. Gate tests use the resulting state. The representative is not used to assert separation-interval probabilities. Those bounds are transferred from the real experiment through `virtualCut` and the exact pushforward, which is the correct distinction.

There is no separately packaged theorem equating the entire adaptive state-history law with an independently defined real-level state-history process. The exact input-law bridge, supported cut-reproduction theorem, and visible cut-only state update justify this finite model; they should not be described as a proved global continuous-history equivalence theorem. A future argument involving the real levels themselves, beyond their cut outcomes, would need its own valid bridge.

Off-support samples do not compromise legality: their representatives are still closed-unit levels, and all such levels yield legal deterministic rounds. Their finite cut outcomes need not equal those representatives' cuts. Probability and expectation arguments correctly use support when that equality is needed.

## 5. Stopped coupling and unconditional truncation

`epochPrefix` runs the same stopping scan on a deterministic number `t` of positions. `sampleOrder_take_toFinset` identifies the positions with the image of the literal deterministic prefix under the sampled permutation. Supported representatives give the virtual-union identity `prefix_virtual_eq`.

Two distinct conclusions are proved:

- `epochPrefix_cut_subset` (226–232): for every supported sample, the stopped prefix cut is contained in the virtual cut using all `t` positions. No activity or good-event premise appears.
- `epochPrefix_cut_eq_of_active` (234–247): if the prefix result remains active, then it performed every position and its cut equals the virtual cut. This is a pointwise coupling on a joint event, not a claim that a prefix remains uniform after conditioning on activity.

Remaining active is stronger than merely having performed the last prefix round: an epoch can become inactive exactly after that round. The more general deterministic `run_cut_eq_virtual_of_full` also handles that case when full execution of the prefix is supplied. This distinction does not weaken the stated active-event coupling.

`expected_epochPrefix_new_card_le` (256–277) genuinely proves the unconditional bound

`E[card(prefix_cut \ start_cut)] ≤ (t / card(start_remaining)) * start_mass`,

as a finite `ℝ≥0∞` expectation. Its assumptions are a fixed state and `t ≤ card(start_remaining)`; no good event, reaching event, or external expected-cost premise is required. The proof treats zero-probability atoms as zero, uses supported pointwise domination on the other atoms, and invokes the exact frozen expectation. `label_mass_sum` proves that the subtype sum equals the actual epoch-start outside mass. Duplicate cut vertices are counted once, and vertices already in the initial cut are excluded. Empty label sets and `t = 0` are covered without division-by-zero exclusions; the bound then has both sides zero.

**Precise unassembled probability interface:** `FrozenEpochProbability.experiment_stopped_joint_le_exp` is still a general wrapper requiring pointwise agreement with the real virtual process. `AdaptiveRounding` supplies an actual supported active-prefix equality and a finite virtual survival inequality, but does not state their combined finite actual-event probability inequality. To obtain it, one must discard the zero-mass unsupported atoms and use the supported joint-event inclusion. Plugging representative levels into the real wrapper as if they were uniform would be incorrect. No such misuse appears here.

Likewise, no named continuation/concatenation theorem relates the full epoch's overrun event to activity of `epochPrefix` at a specified horizon. The recursive definitions support that intended argument, but this review does not count an unproved interface as an exported tail bound.

## 6. The outer recursion and what its validity means

`solve` (AdaptiveRounding 298–306) is an actual PMF-valued recursion on natural fuel. Each iteration stabilizes the current state, returns it immediately if its optimum is zero, or binds the actual state-dependent finite sample PMF to the recursive law after its actual stopped epoch. Thus each next epoch uses the appropriate fresh sampling kernel for its new state. There is no favorable-outcome oracle and no assumption that real-valued optimizer states form a finite type. `Measure.toPMF` is applied only to the finite sample type; PMF `bind` itself permits arbitrary output types.

`solve_support_execution` proves every supported result is connected to the original input by a genuine finite trace of candidate installations and legal sampled rounds. `solve_support_zero` proves zero optimum when initial remaining-label count is at most fuel, using the strict progress of every positive stabilized epoch. The zero-fuel branch does stabilize, and need not be terminal without a sufficient-fuel hypothesis; the theorem correctly retains that hypothesis.

`solve_support_zero_of_mass_fuel` supplies a second sufficient condition: stabilized initial mass is strictly less than `r^fuel`. Its induction uses the actual next-start mass decrease and the unit lower bound on positive optimum at fuel zero. This is a genuine geometric termination theorem. It is not a separately stated logarithmic count of positive epochs along a sampled history, nor a theorem that output distributions at different sufficient fuels are equal.

`solve_support_integralCut` combines zero optimum with the state invariant, and `outputPMF` fixes fuel to the initial remaining-label count. `outputPMF_valid` consequently proves that **every supported returned cut** internally cuts all original demands, with no probability-of-success premise. Low-probability size failures, once defined, cannot invalidate that supported-cut correctness. The `≤ n²` coarse label budget follows from labels being a finset of vertex pairs, but these modules do not export a separate graph-size fuel theorem.

The model is mathematical and noncomputable: attained optimizer choices, first-ready indices, representative levels, and exact real probabilities do not supply an executable rational implementation or runtime bound.

## 7. Remaining assembly obligations and verification evidence

The inspected `ADAPTIVE_ASSEMBLY_PLAN.md` is explicitly a proposal. Its statements that finite-cut sampling, pushforward equivalence, and adaptive composition still require implementation are now outdated relative to these frozen modules. Its cost/failure assembly remains unproved here. Further work must establish the actual joint-event and overrun interfaces just described; supply the charging lower bounds and choose a deterministic horizon from each start state; bound overrun probabilities over relevant graph pairs; compose epoch expectations and failure probabilities through `solve`; account for the full output on failure events; and connect parameter selection, amplification, reductions, and constructive runtime as required. `remaining_value_le` and the per-prefix expectation do not discharge those obligations by themselves.

Existing artifacts inspected during this review:

- `adaptive-epoch-axiom-audit.lean` and `adaptive-rounding-axiom-audit.lean` enumerate declarations by owning imported module and recursively collect their axioms, allowing only `propext`, `Classical.choice`, and `Quot.sound`. Their logs report all **66** and **70** owned declarations passed, respectively, including compiler-generated auxiliaries.
- `adaptive-epoch-kernel-replay.lean` and `adaptive-rounding-kernel-replay.lean` independently invoke `replayFromImports` on the corresponding module. Their logs contain the corresponding `PASS kernel replay` messages.
- The compilation logs are empty, consistent with the reported successful strict compilations; an empty log alone does not certify the process exit status. This review does not claim an independently rerun compilation or freshly establish source-to-object identity.
- The reviewed adaptive source files contain no source-level `sorry`, `admit`, custom `axiom`, `unsafe`, `implemented_by`, or `native_decide`. Compiler-generated names such as `_unsafe_rec` in an ownership audit are not source-level unsafe proof declarations; they were included in the reported audit coverage.

## Exact source fingerprints

Paths in the first table are relative to `repo/Improved Upper Bounds for the Directed Flow-Cut Gap/DirectedFlowCutGap/`. The primary two files and their three required model dependencies were rehashed at the end of review to confirm this snapshot did not change while being reviewed.

| File | SHA-256 |
| --- | --- |
| `AdaptiveEpoch.lean` | `20eb67de0ac00bbf7b5cb241c141b4a20bfba3a917ab5f9671880171fd269d74` |
| `AdaptiveRounding.lean` | `34e166462f9b0c4cc57b7b75a8d447fc6ba94cb88a89a373f4bc559b9fa8c745` |
| `CandidateSchedule.lean` | `8fbe75e614b924f6adb8ee1ce90906ca8a9d6c99132dd1821dcfad1d30f73f38` |
| `FrozenEpochProbability.lean` | `e21737b01cc16039289dbf5f1a21cb305269b0cb943480e3cb6796d8513305a8` |
| `FiniteCutLaw.lean` | `3c5fb9499067764d83a9850e071a74cb798aed89be5d3435a9892ee93030f5a2` |
| Supporting `LevelCutProbability.lean` | `8990974de210df6c799b9dbaa44fb276a16db2fcf9317dff83fb97bf40fc8e8d` |
| Supporting `LevelCut.lean` | `547a6b4ab2ef81294bb07ef4fe3965bd21131c353814494e20e443946561acd6` |
| Supporting `EpochAccounting.lean` | `b4bcc1008bb36051c7f7d98ec2f06ec2394c5afbb699b46c59e01cf42d34b971` |
| Supporting `Basic.lean` | `16ec9329854c93a175d9205a897b8f2e80c99d26aef4b3af4db7e11b48999521` |
| Source plan `sources/2604.03412v3/ADAPTIVE_ASSEMBLY_PLAN.md` | `d1d692d38591a4ae69732ae91cea7004ae9c67651a4af28fa2a73e50cf8e6ca1` |
| Repository `lean-toolchain` | `8733782dc070a99b312039cda424f601b80f3be6f6f512627da5ba25adc27632` |
| Repository `lake-manifest.json` | `615d78a994009475b0e34cd0cd67325b2d863ae37e9f42d8ded7f9d575bf4b2f` |

The toolchain is `leanprover/lean4:v4.34.0`; the manifest pins Mathlib to `5ed2965256430c3649e86755f9576b54eca72435`. Selected directly inspected Mathlib interfaces, relative to `Mathlib/`:

| File | SHA-256 |
| --- | --- |
| `Probability/ProbabilityMassFunction/Monad.lean` | `843a7cd1b736c8efe1eb8405a6ee28176e76166db08d7393171c44c9cf5960bb` |
| `Probability/ProbabilityMassFunction/Basic.lean` | `c8bb4397cc2ba0a606029a2d251e8f625532da9fb577d8036ba1c0728fa90f84` |
| `MeasureTheory/Constructions/Pi.lean` | `c42e64e87e9ca61e4e8a17e412ee339759f6ee453471618bcbfe098dc45da041` |

These fingerprints delimit this review. A later `AdaptiveCost.lean` or changes to any dependency need their own verification and semantic assessment; their conclusions are not included here.
