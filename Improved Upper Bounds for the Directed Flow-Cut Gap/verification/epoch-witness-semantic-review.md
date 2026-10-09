# Directed flow-cut gap: witness, frozen-epoch, schedule, and uniform-reduction review

Reviewed 9 October 2026 against the pinned Bodwin–Samborska arXiv:2604.03412v3 source. This is an independent source-level mathematical review of the exact snapshots below. No Lean source was edited and no compiler or kernel command was run by this reviewer.

**Result:** No blocking semantic mismatch, concealed desired conclusion, or omitted positivity condition was found in the four reviewed components. They establish a finite endpoint-safe witness construction, a genuine frozen probability experiment, deterministic candidate/restart control, and a finite uniform-weight reduction. They do not establish the full adaptive probability law, analysis-epoch assembly, running time, or the headline flow-cut bound.

## 1. Finite witnesses and the comparison candidate

`WitnessSystem.lean` correctly implements the repaired Lemma 18/26/27 interface in `WITNESS_REPAIR_PLAN.md`, rather than the invalid original-endpoint residual-carrier requirement in `tex/body.tex:508–521,829–948`.

- `NodeList` is the actual finite type of vertex lists without repetition. `exists_maximal_family` maximizes cardinality over all valid finite families, starting from the proved valid empty family. A deficient internally avoiding path produces a nonempty fresh certified list using `WitnessPrefix`; insertion strictly increases cardinality. Thus the all-path `Covers` stopping condition is derived, not assumed.
- Certificates retain an ordered, strictly internal subsequence of an actual simple carrier. Only internal carrier vertices must avoid the cut; the original demand endpoints may belong to it. Frozen heights are original-graph distances, finite on the carrier. The imported first-crossing construction and zero source-increment budget avoid both nonmonotone-prefix and deleted-endpoint errors. The certificate data, with `WitnessPrefix.residualSegment`, give actual common-residual paths between forward list vertices.
- With `B ≥ 1` and `L ≥ 64B`, each list has `L/(4B) ≤ q−1 ≤ L`, and its heights are below one and separated by at least `1/L`. Same-label lists have disjoint supports. The sigma index preserves identical lists under different labels; `index_eq_of_same_label_of_shared` proves the needed congestion-one property.
- The explicit comparison is one on the current cut, four times the frozen weight on used witness vertices, and zero elsewhere. Its fractional feasibility is proved by the correct internal-path case split, including paths whose endpoints were selected. Its outside cap is `4B/L`. The exact disjoint-support sum and the **upper** list-length bound give outside mass at most `8B` per witness.
- `exists_system_of_stable` exposes the fractional-feasibility/cap hypotheses, candidate-minimality inequality, and stable gate `M ≤ r·OPT`, with `r > 1`; these yield `|Π| ≥ M/(8Br)`. It does not assume candidate feasibility or witness existence. Its `opt` argument needs only the stated minimality comparison, not an additional hidden feasibility hypothesis; attained candidates are available from `CandidateOptimization` and instantiated by `CandidateSchedule`.

## 2. Actual frozen sampling, graph survival, and cost

`FrozenEpochProbability.lean` supplies the probability model missing from a purely arithmetic subset-average bound (`tex/body.tex:399–415,448–477`).

- The sample space is a uniform permutation of the finite label type, independent of a finite product of uniform real levels on `[0,1]`. The permutation type remains nonempty when the label type is empty. Normalization, equal-size permutation fibers, the exact fixed-size subset law, and the literal prefix cardinality are proved. No sampling law is supplied as an extra hypothesis.
- `frozenCut` is the initial cut union the actual `levelCut` sets for the selected labels. Its measurability is proved. Survival means a real directed simple path avoiding the entire cut, including both endpoints. The imported closed-interval geometric theorem makes survival imply avoidance of every sampled separation interval. Product-measure independence then gives the avoidance product, and the proved permutation law and Maclaurin bound give `exp(−i·val/|E|)`.
- `lintegral_experiment_new_card_le` integrates the cardinality of the actual new-vertex union, counting each vertex once. A pointwise union bound, proved one-round marginals, and exact permutation averaging yield expected cost at most `i/|E|` times the epoch-start outside mass. Zero/full prefixes and an empty label type are covered.
- The stopped-survival event is explicitly **joint**: reaching the round and retaining a path. It is bounded by virtual survival through pointwise agreement on the reached event. There is no division by reach probability and no claim that conditioning on reaching preserves a uniform prefix. Stopped cost similarly requires pointwise inclusion in the virtual prefix.

The stopped wrappers permit arbitrary `reaches`, `actualCut`, and `stoppedCut`; their inequalities remain valid as outer-measure/nonnegative-integral domination. To interpret a future concrete adaptive process as ordinary measurable events and random variables, its measurable construction and the agreement/inclusion premises still must be proved. The deterministic horizon and frozen data must likewise be linked to the epoch-start history. These are explicit assembly boundaries, not an error in the inequalities.

## 3. Attained candidates and deterministic restart control

`CandidateSchedule.lean` implements the repaired repeated-test gate, preserving Algorithm 2's original graph and demands (`tex/body.tex:268–314`).

- Each candidate is chosen from the proved attained compact minimum at cap `4·scale/L`. Feasibility, objective decrease, and individual and aggregate minimality are derived. No optimizer oracle is assumed.
- `optimum_eq_zero_iff` is exactly the all-remaining-demands-cut test. Its converse uses an explicit candidate with zero outside weights; its forward direction uses an actual internally avoiding path to prove optimum at least one. Together with the processed-demand invariant, zero optimum certifies an integral cut for every original demand, even with deleted endpoints or unreachable labels.
- A failed ready test installs the candidates, multiplies scale by four, and immediately retests. `exists_ready_le` derives termination from any fuel satisfying `M_initial < r^N`; `exists_ready`, `restartCount`, and `stabilize` construct the first ready state for `r > 1`. Every earlier installation has strict factor-`r` mass decrease and installed mass at least one.
- `round` uses the actual closed-unit level cut, removes exactly its sampled label, freezes the weights, and preserves feasibility, cap, and the internal-cut invariant. `Execution` permits sampling only at a ready state with nonzero optimum. Across arbitrary interleavings of legal samples and installations, it proves `r^k M_current ≤ M_initial`, `scale = 4^k scale_initial`, and `|remaining| + rounds = |remaining_initial|`.
- Crucially, the global bound `r^k ≤ M_initial` for positive installation count uses the last installation's mass lower bound and survives all later samples, including a later zero mass. Installation and logarithmic bounds therefore do not silently assume the final mass is positive.
- `initial` has the genuine unweighted-distance-at-least-`L` demands, zero cut, weights `1/L`, and scale one. Fractional feasibility, exact mass `|P|n/L`, and the bound `n³` are proved for `L ≥ 1`, including empty cases and infinite distances.

This constructs first-ready stabilization and specifies legal finite execution traces. It does not yet assemble a complete random execution or analysis-epoch splits. Applying the witness theorem still requires the separate parameter invariant `L ≥ 64·current scale`; initial scale one and the proved execution scale bound support, but do not by themselves assert, that inequality. No equality of current mass and epoch-start mass is assumed.

## 4. Genuine directed uniform-weight reduction

`UniformWeightReduction.lean` proves a repaired finite existence version of Theorem 28 (`tex/reductions.tex:71–207`).

- The graph has consecutive directed edges inside each fiber and original arcs from the last source clone to the first target clone. `predecessor_mem`, `successor_mem`, and `full_fiber_mem` derive full traversal of every visited nonendpoint fiber from actual adjacency. Projection forms an original walk, erases reflexive steps and loops, and proves that all copies of every remaining internal original occur internally in the expanded path. The resulting path-weight domination is proved, not a correspondence assumption.
- Expansion inserts whole chains. The integral pullback theorem explicitly requires singleton endpoint fibers; the final construction satisfies this with permanent zero-weight source/sink ports. The port graph's direct self edge preserves original length-zero paths. Selected clones pull back through their originals and then through cores, without increasing cardinality or counting selected demand endpoints as path cuts.
- Clipping at one preserves demanded fractional cuts. For positive prepared mass, every prepared vertex receives `max(1, ceil(weight/average))` clones, so zero-weight vertices and ports survive. The prepared graph has `3n` vertices; proved ceiling and sum bounds give at most `6n` expanded vertices and total uniform mass at most `2W`, with uniform weight at most one.
- The explicit bounded oracle ranges over actual finite uniform instances with cardinality at most `6n` and mass at most `2W`. Its conclusion is used to obtain an original integral cut of size at most `2αW`; no monotonicity of a gap function at exact parameter values is assumed. The zero-prepared-mass branch returns an empty original cut via the proved zero-cost theorem, without positive-mass division or an oracle call. Empty graphs, zero weights, disconnected demands, and `α = 0` are retained.

This is an existence reduction with an explicit uniform-rounding oracle assumption. It does not prove that oracle, implement a polynomial-time construction, or establish the headline asymptotic bound.

## Verification boundary

The existing module-owned axiom-audit scripts enumerate declarations by defining-module identity, including generated declarations, and permit only `propext`, `Classical.choice`, and `Quot.sound`. Their logs report 56, 71, 117, and 119 declarations for WitnessSystem, FrozenEpochProbability, CandidateSchedule, and UniformWeightReduction, respectively. All four standalone LeanChecker replay logs report success. WitnessSystem and CandidateSchedule compile logs are empty; FrozenEpochProbability and UniformWeightReduction contain nonfatal linter warnings. No source proof placeholder, custom axiom, explicit unsafe declaration, native decision shortcut, or replacement implementation was found in these modules and the inspected supporting sources.

These are existing verification artifacts, not a fresh reviewer build or an independent source-to-object identity check. The semantic conclusions are pinned to the following source bytes; changed files require renewed review and verification.

## Exact reviewed snapshots

All hashes are SHA-256. Lean filenames are relative to `repo/Improved Upper Bounds for the Directed Flow-Cut Gap/DirectedFlowCutGap/`; paper filenames are relative to `sources/2604.03412v3/`.

| File | SHA-256 |
| --- | --- |
| `WitnessSystem.lean` | `b60a8e2dd02b56c561f3cebefb53c1930198e3acfd31745c923aa69ea0128d14` |
| `FrozenEpochProbability.lean` | `e21737b01cc16039289dbf5f1a21cb305269b0cb943480e3cb6796d8513305a8` |
| `CandidateSchedule.lean` | `8fbe75e614b924f6adb8ee1ce90906ca8a9d6c99132dd1821dcfad1d30f73f38` |
| `UniformWeightReduction.lean` | `4f801c5c73da8587ccffefd12a05ee9a13696e89619042ff32d2708dd863de8a` |
| `WitnessPrefix.lean` | `9bdfa74216cb531f6b2ef79a1466b9f562d233713655ca414b90c7c68b3cada7` |
| `WitnessThinning.lean` | `8a11a4e1f334361bca96474e8557e6d2faa6a786962a5e9f17dac48ba50cc33d` |
| `CandidateOptimization.lean` | `0a39d1eecb5e2b875466e66ca408f41889debe67e167b704c9d4d249f82bc31a` |
| `EpochAccounting.lean` | `d698916d0cf6495589c73ddcf5a507957d240dcbe85b11cedbaf8afa086cd4a2` |
| `FiniteSurvival.lean` | `3570b1e17b46537badd766bbf777bc38d87065f8eb9e545a33046170bc80e5d3` |
| `LevelCutProbability.lean` | `8990974de210df6c799b9dbaa44fb276a16db2fcf9317dff83fb97bf40fc8e8d` |
| `LevelCut.lean` | `547a6b4ab2ef81294bb07ef4fe3965bd21131c353814494e20e443946561acd6` |
| `TerminalPorts.lean` | `22bbef774144a67c6d8b631dd8ec5490846d46a7d5a530c18227df5d43bf5b88` |
| `UnitCostReduction.lean` | `ead649a30cb6423f56b5c4012bbf23385504c3c4c478a69f674ef8aeaa732843` |
| `PathExtraction.lean` | `abc2c7bcda89b3b7ee2d37dd254f4357724585ebc9963697304917899473c63e` |
| `Basic.lean` | `16ec9329854c93a175d9205a897b8f2e80c99d26aef4b3af4db7e11b48999521` |
| `Paper tex/body.tex` | `6261f6fe94e1ecd7084107a67f9da4550f4507b1e1e6cd0eea977f91e3667325` |
| `Paper tex/reductions.tex` | `d848044d8d074305eefde28f5080dc0c5b2622224edde16952407e12ac46fe4a` |
| `Paper WITNESS_REPAIR_PLAN.md` | `5ec5797e9086314347c520dae1e96f5ffcdf54dcd138e84ddfd594d47aef9c92` |
| `Paper paper.pdf` | `a0f6f3a73acbfbb1c82fe04d739283c87b3e34d7f6ff850543dcb42b702c3a46` |
| `Paper paper.tar.gz` | `9d76894e97711df52b099d4f77061c7b5737a86958fc67d2f981b1be1680ce9e` |
| `Repository lean-toolchain` | `8733782dc070a99b312039cda424f601b80f3be6f6f512627da5ba25adc27632` |
| `Repository lake-manifest.json` | `615d78a994009475b0e34cd0cd67325b2d863ae37e9f42d8ded7f9d575bf4b2f` |
