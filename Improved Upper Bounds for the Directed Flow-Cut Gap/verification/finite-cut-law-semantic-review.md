# Semantic review: the finite law of an actual level cut

Date: 2026-10-09. Reviewed repository HEAD: `ad6c6e531335bc7554421e01c41c8100d9fe3f2c`; the new module and two comment updates are working-tree changes relative to that commit.

**Verdict:** no blocking semantic mismatch, assumed cut-distribution oracle, or concealed adaptive-law hypothesis was found in `FiniteCutLaw.lean`. It constructs the exact finite probability law of one actual uniform-level cut, proves that every positive-mass outcome has a valid unit-level realization, and transfers the actual single-round new-cost bound to a finite expectation. The two recorded documentation updates are verified comment-only changes. Full adaptive assembly remains separate.

This is an independent source-level review. The reviewer inspected all of the new module, the relevant level-cut geometry/probability proofs, the exact Mathlib measure/PMF interfaces, both changed comments, and the earlier documentation notes. No Lean source was edited and no compiler or kernel command was run. The existing `finite-cut-law-compile.log` contains no diagnostics; this report does not substitute for the separately conducted strict compilation, all-owned-declaration axiom audit, kernel replay, or source-to-object identity checks.

## Actual pushforward and exact mass

`Outcome V` is a wrapper around `Finset V`, with its finite type derived from the finite vertex type and with the discrete sigma algebra. Its finite support is therefore a consequence of the actual finite output space, not a new hypothesis about a supplied distribution. The sample space remains the real line, with `uniformLevel = volume.restrict [0,1]`; its normalization was proved in `LevelCutProbability`.

`draw` applies the actual `levelCut` to `d.toNNReal`. The conversion agrees with `d` on the sampling interval. `measurable_draw` is proved from `measurableSet_levelCut_property`, whose proof reduces arbitrary cut properties to a finite union of measurable cut fibers. Thus arbitrary real values outside the sampling interval do not affect the experiment.

`cutMeasure` is literally the pushforward of `uniformLevel` along this measurable function. This measurability matters: the pinned Mathlib version defines the map of a non-a.e.-measurable function using a fallback Dirac mass and supplies an unconditional probability-measure instance. The new module does not rely on that fallback. Its separately proved measurability is used explicitly in `cutPMF_apply` and the integral transformation, establishing the intended pushforward semantics.

`cutPMF` is obtained from this probability measure by `Measure.toPMF`. The finite/countable measurable-singleton assumptions needed by that construction are supplied by `Outcome`. `cutPMF_toMeasure` proves that converting it back gives the same pushforward, and `cutPMF_apply` proves exactly

`cutPMF G w s Y = uniformLevel {d | draw G w s d = Y}`.

The weights are normalized genuine probabilities, not arbitrary nonnegative coefficients. No claim of a uniform distribution over distinct cuts is made; different cut fibers can have different masses.

## Supported outcomes and the off-support fallback

`support_exists_level` starts from nonzero PMF mass, rewrites it as the restricted Lebesgue measure of the cut fiber, and derives that the fiber intersects `[0,1]`. It then returns the corresponding nonnegative finite level, proves it is at most one, and preserves the actual cut exactly. The argument uses the valid implication “nonzero measure implies nonempty”; it does not use the false converse. In particular, a cut attained only at isolated boundary levels need not have positive probability, and the theorem does not claim that it does.

`realizeLevel` chooses this witness on PMF support and returns zero otherwise. `realizeLevel_le_one` holds in both branches. `realizeLevel_cut` requires the support premise, correctly avoiding a claim that an impossible cut equals the level-zero cut. Off support, the PMF coefficient is zero, so the arbitrary fallback does not alter any finite expectation. No additional existence or optimization oracle is assumed; the supported choice is justified by the preceding theorem.

`support_cutsPair` retains the substantive fractional-distance condition `1 ≤ vertexDistance G w s t`. It applies the imported deterministic theorem for every level in the closed unit interval, including zero and one. Its conclusion is the actual internal-vertex `CutsPair` predicate, not a weaker claim that merely selecting a terminal counts as separating the demand. Unreachable targets are handled by the existing extended-distance geometry.

## Exact expectation and actual new cost

`expectation_eq_integral` holds for every real-valued function on the finite outcome type. The finite PMF integration identity supplies the exact sum over all outcomes, with real weights `(cutPMF ... Y).toReal`; converting the PMF to its measure and applying the measurable-map integral identity gives the original uniform-level integral. Since the outcome type is finite and its measure is a probability measure, every such function has finite range and is integrable. There is no missing summability hypothesis or infinite-mass `toReal` truncation.

`expected_new_cost_le` instantiates that exact equality with `cutCost cost (Y.cut \\ X)`. The imported integral theorem bounds the cost of the actual newly selected vertices by `∑ v ∉ X, cost v * w v`. Its proof expands the actual cut cost into vertex indicators, integrates their exact clipped-interval probabilities, bounds each by `w v`, and proves finiteness before passing to the real integral. Thus already selected vertices are not charged, multiple occurrences are not counted, and the theorem does not postulate an expected-cost guarantee. The arbitrary prior cut `X` and arbitrary nonnegative finite weights/costs are explicit. `expected_new_card_le` is the correct unit-cost specialization.

## Verified comment-only changes

The record `comment-only-source-updates.json` was checked against both the current source bytes and `git show HEAD:<path>`. In each file, the recorded removed comment occurs exactly once in HEAD; replacing that occurrence with the recorded replacement produces the entire current file byte-for-byte. Both old and new SHA-256 values match the record. Consequently no definition, theorem statement, proof, import, option, or other source text changed.

| File | Git HEAD SHA-256 | Current SHA-256 |
| --- | --- | --- |
| `EpochAccounting.lean` | `d698916d0cf6495589c73ddcf5a507957d240dcbe85b11cedbaf8afa086cd4a2` | `b4bcc1008bb36051c7f7d98ec2f06ec2394c5afbb699b46c59e01cf42d34b971` |
| `MedianShortcuts.lean` | `d357f86b271698c9e03a7a91ad84235e65c1f0e48f09ae01836af597dcb5e2f4` | `d20ab16cd47fcc298272510ff83d928d2fcc6fd149dd7b8731b8188a6fd3e1a9` |

The `restart_power_le` comment now accurately describes a unit terminal-mass lower bound and distinguishes the additional `r > 1` needed by the logarithmic theorem. This resolves the interpretive concern in `reduction-semantic-review.md`.

The `mediators` comment now describes a single search branch containing the required ancestors instead of claiming equality with the root-to-node chain. This resolves the concrete `[1,2,3,4,5,6,7]`, `x = 4` issue in `path-system-semantic-review.md`: the mediator set may include `4,6,7`. The sentence about continuing right at the queried pivot is understood for the no-duplicate trees used by the shortcut theorem. For an unrestricted `Tree` containing a duplicate of that pivot in its left subtree, the definition's literal rule is to go left whenever `x ∈ l.vertices`; this does not affect the no-duplicate application or any theorem.

These checks close the earlier substantive comment notes while retaining the original reports as historical reviews of their old exact snapshots. They do not reclassify an earlier pending build or replay as completed.

## Remaining scope

This module proves a law for one cut at fixed graph, weights, and source. It does not construct the full adaptive execution, derive its conditional transition law at each reached history, assemble analysis epochs or restarts, prove conditional independence, or establish the complete algorithm's cost/survival/high-probability bounds, running time, or headline flow-cut theorem.

The representative `realizeLevel` reproduces a supported cut; its real-valued distribution is generally not uniform. Its selection is appropriate for preserving a deterministic transition that depends on the sampled level only through the cut. Future assembly must prove that this dependence condition holds where used, or retain the original real-level experiment for any additional level-dependent events. In particular, a separation-interval probability or an independence claim cannot be transferred merely by declaring the chosen representative level uniform.

A finite outcome type for this one round does not itself provide the global adaptive law. The complete construction must connect legal state updates and their history-dependent frozen data to the exact PMF proved here, then supply the stopped-epoch and charging premises. These are explicit remaining obligations, not premises hidden in the new single-round theorems.

## Exact reviewed source fingerprints

All values below are SHA-256. Project Lean filenames are relative to `repo/Improved Upper Bounds for the Directed Flow-Cut Gap/DirectedFlowCutGap/`; repository and verification filenames are identified separately. The new module contains no source-level `sorry`, `admit`, custom `axiom`, `unsafe`, `implemented_by`, or `native_decide` occurrence.

| Source | SHA-256 |
| --- | --- |
| `FiniteCutLaw.lean` | `3c5fb9499067764d83a9850e071a74cb798aed89be5d3435a9892ee93030f5a2` |
| `LevelCutProbability.lean` | `8990974de210df6c799b9dbaa44fb276a16db2fcf9317dff83fb97bf40fc8e8d` |
| `LevelCut.lean` | `547a6b4ab2ef81294bb07ef4fe3965bd21131c353814494e20e443946561acd6` |
| `Basic.lean` | `16ec9329854c93a175d9205a897b8f2e80c99d26aef4b3af4db7e11b48999521` |
| Repository `lean-toolchain` | `8733782dc070a99b312039cda424f601b80f3be6f6f512627da5ba25adc27632` |
| Repository `lake-manifest.json` | `615d78a994009475b0e34cd0cd67325b2d863ae37e9f42d8ded7f9d575bf4b2f` |
| Verification `comment-only-source-updates.json` | `1f632d9c88754c01fc265a74ceb43118bb66e322a5d523318f85986a5a7344d5` |

The inspected Mathlib dependency is pinned by the repository manifest to `5ed2965256430c3649e86755f9576b54eca72435`. Its directly inspected interfaces have the following exact source hashes, relative to `Mathlib/`:

| Mathlib source | SHA-256 |
| --- | --- |
| `Probability/ProbabilityMassFunction/Basic.lean` | `c8bb4397cc2ba0a606029a2d251e8f625532da9fb577d8036ba1c0728fa90f84` |
| `Probability/ProbabilityMassFunction/Integrals.lean` | `174951d99036d6995b4ac6d486de807bedb58f340aa902f02502a7216515bf63` |
| `MeasureTheory/Measure/Map.lean` | `775c69d7084f194fedd5c0f67888432ae151bf68481f86e1b6e64b23da5ee7c1` |
| `MeasureTheory/Measure/Typeclasses/Probability.lean` | `054a34de6303b06fb714c4f8e583a92a3513a1ae95354e672404830c33ba3632` |
