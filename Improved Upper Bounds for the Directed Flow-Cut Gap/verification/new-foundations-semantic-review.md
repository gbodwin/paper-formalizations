# Semantic review: edge model, epoch parameters, amplification, and adaptive cost

Reviewed 9 October 2026 against arXiv:2604.03412v3. Repository HEAD was `19d2d0bcae17f88e040533ce9e34dbb0ac6856f8`; the four reviewed modules were untracked working-tree files, so their hashes below, rather than HEAD, identify this review. The review was extended to the newly frozen `AdaptiveCost.lean` at 04:50–04:53 UTC.

**Verdict: no blocking mathematical or specification defect found in these four components.** They provide an actual directed-edge model, a correctly scoped bridge from attained candidates to the charging theorem and uniform numerical envelopes, genuine independent finite amplification, and an unconditional expected-cost theorem for the actual bounded adaptive solver under explicit hard-regime parameter conditions. They do not yet supply the all-regime headline flow-cut theorem or an implementable polynomial-time algorithm.

This was an independent source-level review. It inspected the complete four modules, relevant imported path/state/charging/asymptotic/adaptive interfaces, Mathlib's PMF constructors and event identities, the existing verification drivers/logs, and the paper's actual TeX. No Lean source was edited and no compiler, axiom auditor, or kernel replay was run by this reviewer.

## 1. Actual edge/path/cut semantics

`EdgeModel.lean` uses a directed adjacency relation on vertices, with an edge represented by an ordered pair. `SimplePath` is the existing injective consecutive vertex sequence with explicit adjacency proofs. Its new `edgeAt` reads consecutive vertices, and injectivity of this edge map is proved. Consequently the finite edge set has exactly `edgeLength` members. Edge weights include the first and last edge; no vertex-endpoint exclusion leaks into edge length.

`DirectedWalk.edgeWeight` adds a cost on every traversal, including repeated edges and self-loops. Its `edges` forgets repetition only in the support. The proof that support weight is at most walk weight explicitly uses nonnegativity. Crucially, loop erasure is performed after restricting adjacency to the original walk's edge support. The extracted path therefore uses only traversed edges; the argument does not mistake vertex containment for edge containment. Composition uses the same restriction to the union of the two input edge sets and bounds the resulting weight by the sum of the input weights.

`edgeDistance` is the extended nonnegative infimum over actual simple paths, with proved equality to the infimum over conventional walks. Disconnected pairs have distance infinity, self-distance is zero, and the positive-length self-loop cannot displace the empty self path. Finite vertex sets supply attained minima and the ordinary edge triangle inequality. Zero weights and zero costs are supported; negative or infinite individual weights/costs are outside the type.

`EdgeCutsPair` requires an actual edge hit on every path. The deletion graph removes edges and retains every vertex, including both terminals. The equivalence to absence of any deleted-graph walk is proved, as is the equivalence to distance at least one under the cut indicator. Self-demands are correctly impossible to cut and cannot be fractionally feasible. Unreachable demands are already cut vacuously.

The objectives sum only over actual adjacent ordered pairs. A syntactic cut may contain nonedges, but these affect neither feasibility nor its defined cost: explicit filtering theorems normalize it to a subset of actual edges without changing either. The weighted fractional objective of an indicator equals integral cut cost. Graph self-loops are included in total edge weight and the objective even though simple paths cannot use them; this is coherent and can only add nonnegative objective terms.

This matches the edge-distance, path-hitting, and objective definitions in `tex/body.tex:17–27`, used by the reductions at `tex/reductions.tex:398–434,597–620`. It is a relation-graph model, not a separately identified parallel-edge/multigraph model. The source itself distinguishes the edge multigraph setting in `tex/intro.tex:265`; no multigraph normalization theorem should be inferred from this file. Neither edge/vertex reduction is proved here, as the module header explicitly states.

## 2. Actual candidate cap and exact uniform parameters

`EpochParameterBridge.lean` closes a concrete interface gap in the earlier charging/asymptotics review: it bounds the exact `Nat.log2 n + 2` factor by the padded `H(n)` and proves subpolynomiality of

`K(n) = 2048 B(n) r(n) (256 B(n))^4 (Nat.log2 n + 2)`.

The imported parameters are `r(n)=max(2,log(n+2))`, `J(n)=ceil(3 log(n+2)/log(r(n)))`, `B(n)=4^J(n)`, and `H(n)=2+ceil(log(n+2)/log 2)`. Positivity avoids zero logarithmic denominators. The bounds have the correct order `∀ ε>0, ∃ C>0, ∀ n≥1`; constants are chosen before the size. For the expected-cost expression, the confidence exponent `q : ℕ` is fixed before those quantifiers. There is no assertion uniform in unbounded `q`, and no claim that merely naming this expression proves an actual expectation bound.

The state bridge is substantive. Its label type is exactly the subtype of `S.remaining`; the subtype-to-finset identities count each remaining label once and exclude processed labels. It uses `S.mass`, the current outside-cut mass, rather than substituting an epoch-start mass. Feasibility and the cap come from the actual state. Candidate minimizers are constructed in `CandidateSchedule` from attained compact minima, not passed in as an oracle. `Ready` together with nonzero optimum yields the stable gate, while the proved unit lower bound on nonzero optimum supplies positive current mass.

The optimization domain is handled correctly: `exists_state_graph_value` applies `PathSystemCharging.exists_stable_graph_value` at `S.scale`, with candidate cap exactly `4*S.scale/L`. The NNReal/real conversion preserves that cap. Only after obtaining the favorable residual pair does `exists_state_graph_value_global` increase the positive numerical denominator from the actual scale to `B(n)`. It does not transfer optimizer minimality to a larger feasible domain, which would generally be invalid.

The hard-regime conditions remain explicit: scale at least one, `64*scale≤L`, `L≤|V|≤L^3`, readiness, and positive optimum. They imply positive `L` and a nonempty vertex type. The cube-root adapter and a single eventual size threshold prove the advertised domain implications; the module does not silently dispose of small sizes or other parameter regimes. The conclusion constructs a pair connected in the fully deleted residual graph and lower-bounds its exact frozen separation-value sum. Neither that pair nor a witness family is a premise.

Source correspondence is to the mass and cap bookkeeping in `tex/body.tex:324–327,376–399`, the expected-cost assembly at `401–435`, and the repaired graph-value theorem previously reviewed in `charging-asymptotics-semantic-review.md`. The explicit denominator is a conservative formal constant from that repaired argument, not a claim that this exact constant is printed in the paper. The adapter alone supplies no adaptive survival, total cost, or runtime theorem.

## 3. Genuine finite independent amplification

`FiniteAmplification.lean` uses a normalized `PMF A` on an actual finite type. Event probability equals the finite sum of its atom masses; all those masses and event masses are finite. Thus conversion from extended nonnegative values to real numbers does not discard an infinite mass. The expected cost is the literal finite weighted sum. The bind and map identities establish ordinary finite expectation transfer.

`sampleLaw p T` assigns each sample vector the product of its coordinate masses, and proves normalization by expanding the power of the total mass. Its rectangle identity proves independence directly. The probability that all coordinates satisfy an event is exactly the single-draw event probability raised to `T`; it is not an independence hypothesis. The empty experiment is handled at the product-law level, while minimum selection requires `T>0`.

The output is one of the actual samples, selected at a proved minimum-cost index, including ties. Its support is contained in the original PMF support, so a validity predicate holding on that support is preserved. The strict upper-tail event for the selected cost is exactly the event that every sample exceeds the threshold. The validity hypothesis is explicit and is not established for a graph algorithm by this generic module.

For nonnegative costs and an **unconditional** expected-cost bound `E[cost]≤B` with `B>0`, the finite Markov proof gives single-draw failure at threshold `2B` at most one half. Independence then gives failure at most `2^(-T)`. The explicit positive count `max(1,ceil(κ log n/log 2))` gives failure at most `n^(-κ)` for `n≥1`, `κ≥0`. Strict failure correctly complements success at cost at most `2B`. The zero-budget case is separately proved: nonnegative expected cost at most zero forces zero cost at every supported output, without dividing by zero. No outcome type with no PMF is assumed to be sampleable.

This implements the repetition/minimum idea in `tex/body.tex:366–367`. An application requires a valid finite law of complete runs and an unconditional expectation estimate; the next section reviews the new conditional-parameter theorem supplying those ingredients. Amplification itself does not justify replacing an unconditional expectation by the source's calculation under a high-probability runtime event (`430–435`). The noncomputable choice of a minimum and the real-valued PMF also do not establish a sampling implementation or bit/runtime bound.

## 4. Stopped joint events and unconditional adaptive cost

`AdaptiveCost.lean` closes the joint-event, continuation, horizon, and outer-expectation gaps identified in `adaptive-model-semantic-review.md`. It analyzes the repaired stopped adaptive construction already defined by `AdaptiveEpoch` and `AdaptiveRounding`; it is not a proof that every detail of that repaired schedule is identical to the printed algorithm.

The deterministic append theorem uses a duplicate-free legal label order. If a prefix is inactive, continuation remains at the same state. Consequently full-epoch new cost is pointwise at most prefix new cost plus `n` times the indicator that the prefix remains active. This is true even on samples outside PMF support; no conditional expectation or good-event cost assumption is introduced. At the full remaining-label horizon the epoch is deterministically inactive.

For every supported active prefix, `active_prefix_value_witness` applies charging at the current state's actual scale. The scale and weights are frozen inside the epoch. The activity condition supplies `start_mass ≤ r*current_mass`; monotonicity of the remaining-label value sum then transfers the current favorable pair to the fixed start-family threshold

`a = start_mass*(L/n)^(3/2) / (r*graphDenominator(n,B,r))`.

The extra factor `r` is retained. The actual prefix cut equals the virtual frozen cut only on the supported active event, exactly as required by the imported coupling. Unsupported atoms are removed by PMF support monotonicity. No distributional claim about the chosen representative levels is used.

`valuable_pair_event_le` takes the union over all actual ordered vertex pairs. For each fixed pair, its frozen separation-value sum and the threshold comparison are deterministic at the epoch start. Its event probability is bounded by the proved virtual residual-path survival theorem. Thus an adaptively selected favorable pair incurs the explicit factor `n²`; it is never treated as a predetermined pair. This proves the unconditional joint-event bound `P(active prefix at t) ≤ n² exp(-t*a/|P|)`, without asserting a permutation stays uniform after conditioning on activity.

The horizon is the start-state quantity `min(|P|, ceil(|P|*H/a))`. It is chosen before that epoch's sample. Positive optimum proves `|P|>0`, positive start mass, and positive `a` under the domain hypotheses. If the horizon equals `|P|`, failure probability is zero. Otherwise the ceiling gives exponent at least `H`. The ceiling's additive cost is kept explicitly as `start_mass/|P|`, then bounded by `nB/L` using the actual outside-weight cap. Combining the unconditional prefix expectation and the `n`-cost failure term proves

`E[new epoch vertices] ≤ r*graphDenominator(n,B,r)*H*(n/L)^(3/2) + nB/L + n³ exp(-H)`.

This explicitly accounts for failure outcomes and repairs the expectation assembly issue at `tex/body.tex:430–435`. The corollary absorbs the last two terms into `(B+1)*(n/L)^(3/2)` using `L≤n`, `H≥0`, and the explicit hypothesis `n³ exp(-H)≤1`. That failure hypothesis is not derived merely from calling something a confidence logarithm. In particular, the earlier envelope is subpolynomial for every fixed natural `q`, but an application with `H=log((J+1)(n+2)^q)` must separately check this condition; `q≥3` suffices for `n≥1`, while arbitrary `q` does not.

`boundedOutput` is the actual `solve` law pushed forward to its finite vertex-cut output. The optimizer-state type is not assumed finite. The recursion is rewritten as a bind over each finite sample space, after deterministic stabilization, so the finite tower identity applies legitimately. Its induction bounds every legal continuation; off-support continuations are also legal because their fallback levels stay in the closed unit interval. Exact cut-cardinality decomposition counts only newly added vertices and retains the previous cut once. Stabilization does not change the cut.

The intermediate tower theorem states a scale invariant explicitly. The final `boundedOutput_expected` discharges it from the real execution trace and geometric installation budget, rather than retaining an optimizer or desired-cost oracle. For a starting state `S`, it assumes:

- `r>1`, `1≤S.scale`, and `S.mass<r^(J+1)`;
- `4^J*S.scale≤B`, `64B≤L≤n`, and `n≤L³`;
- `H≥0` and `n³ exp(-H)≤1`, on a finite nonempty vertex type.

It then proves the unconditional final expectation is at most

`|S.cut| + (J+1)*(r*graphDenominator(n,B,r)*H+B+1)*(n/L)^(3/2)`.

`boundedOutput_valid`, with the same geometric sufficient-fuel condition, proves every supported final cut cuts every original demand internally, including on size-failure outcomes. Fuel zero still performs stabilization at the state level; its output cut equals the original cut, and no unconditional validity claim for insufficient fuel is made. The final theorem retains only concrete numerical/state hypotheses, not a favorable witness, success event, expected-cost premise, or rounding conclusion.

Remaining work is to instantiate the genuine initial state and choose the global parameters, discharge the hard-regime/failure/fuel conditions, handle small sizes and other regimes, apply amplification, and connect downstream reductions and any claimed runtime. Those are genuine remaining theorem-level obligations even though the adaptive expected-cost bridge is now proved.

## 5. Existing build evidence and its limits

The dedicated `edge-model-*`, `epoch-parameter-*`, `amplification-*`, and `adaptive-cost-*` drivers and logs were inspected. Compile logs are empty; the corresponding object files exist. Their audit drivers enumerate every declaration owned by the target module using module indices and recursively collect its axiom dependencies, permitting only `propext`, `Classical.choice`, and `Quot.sound`. The recorded success counts are 148, 31, 42, and 73 declarations, respectively. All four dedicated replay logs report PASS.

Those replay drivers call the official Lean 4.34.0 `LeanChecker.replayFromImports` on the individual module. Its source shows that it kernel-replays that module's declarations into the imported environment; this is not a fresh independent replay of every dependency or an external verifier. At initial inspection, the older aggregate `DirectedFlowCutGap.lean`, `verification/flow-cut/AxiomAudit.lean`, and `KernelReplay.lean` omitted the additions; the later source-bound aggregate described below supersedes that coverage limitation.

The initial dedicated logs do not themselves bind source hashes. At 04:54 UTC, this reviewer independently inspected the subsequent `verify-sixth.sh`, `sixth-prebuild-source-manifest.json`, six `sixth-*-compile.log` files, aggregate drivers, and final aggregate audit/replay logs. The script uses `set -euo pipefail`, recompiles all six additions and the aggregate with `-j1 -DautoImplicit=false`, then runs the aggregate axiom audit, official replay driver, and post-build source-hash assertion. All six compile logs and the aggregate compile log are empty. The final audit reports **2199** allowed-axiom declarations. An independent read-only comparison confirmed **35 current source hashes match the pre-build manifest** and **35 distinct kernel PASS entries exactly cover its 34 component modules plus the aggregate**, with no omitted or unexpected module. This is inspected evidence of the coordinator's fresh local run; the reviewer did not rerun Lean and does not claim remote publication or remote CI. The earlier naive addition of historical declaration counts differed by one from the actual aggregate count; the six additions' dedicated lists contain 430 distinct names with no overlap. The measured aggregate count is the evidence used here.

The source manifest SHA-256 is `037ac8df60e690a2e8de20e7ed87c6050245a3f9113605633087a43607de7921`; verification script hash is `b547c15682350e64393615ac7f0b270a476debd02b6113b5c1ea2a46e05b607d`; aggregate axiom log hash is `0c8641a1e6bba1df0a9fd871d6f3547e871ed6661bb53dde18f954f079cae341`; aggregate replay log hash is `b64102b11833fbdba6b7591a847057b21d5869493698851c99eb5bbf68f40b4c`. The four reviewed source files contain no `sorry`, `admit`, custom `axiom`, `unsafe`, `implemented_by`, or `native_decide` occurrence.

## 6. Exact reviewed snapshots

Lean filenames below are relative to `repo/Improved Upper Bounds for the Directed Flow-Cut Gap/DirectedFlowCutGap/`. Values are SHA-256.

| File | SHA-256 |
| --- | --- |
| `EdgeModel.lean` | `76d24c359a46238e3f822e42d615f7e7f43dfbc48443212ad70e203666512e9b` |
| `EpochParameterBridge.lean` | `f93dd998682dddcb95018137a8ee0d6537a6a60456148c11a5684bd22186c946` |
| `FiniteAmplification.lean` | `0371f41d05e63025151823fec0c681dbfc951870e5b425439b9e0d7713d5f678` |
| `AdaptiveCost.lean` | `c2bc3d9bda104148d976f207d8ab7b1fa714ceea5a4c63b0a04f53c11b11710d` |
| `AdaptiveEpoch.lean` | `20eb67de0ac00bbf7b5cb241c141b4a20bfba3a917ab5f9671880171fd269d74` |
| `AdaptiveRounding.lean` | `34e166462f9b0c4cc57b7b75a8d447fc6ba94cb88a89a373f4bc559b9fa8c745` |
| `Basic.lean` | `16ec9329854c93a175d9205a897b8f2e80c99d26aef4b3af4db7e11b48999521` |
| `PathExtraction.lean` | `abc2c7bcda89b3b7ee2d37dd254f4357724585ebc9963697304917899473c63e` |
| `CandidateSchedule.lean` | `8fbe75e614b924f6adb8ee1ce90906ca8a9d6c99132dd1821dcfad1d30f73f38` |
| `PathSystemCharging.lean` | `bc56f96afb836847e71b4caeab9ac3ff6f694c9adacbdc6537afe27e47025569` |
| `SubpolynomialBounds.lean` | `f699434e96940db5e00f10e101bd806696f5d6f698c8f82c69727c8ce7bab086` |

The inspected actual paper source files under `sources/2604.03412v3/tex/` have hashes: `body.tex` = `6261f6fe94e1ecd7084107a67f9da4550f4507b1e1e6cd0eea977f91e3667325`; `reductions.tex` = `d848044d8d074305eefde28f5080dc0c5b2622224edde16952407e12ac46fe4a`; `intro.tex` = `9619d3bab7a12edf3cc329880207681a3ad3084bef81e58ca3c7bb1c86bcc790`. The repository pins Lean `v4.34.0` and Mathlib revision `5ed2965256430c3649e86755f9576b54eca72435`.
