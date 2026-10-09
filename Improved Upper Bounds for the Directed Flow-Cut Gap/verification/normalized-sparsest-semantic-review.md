# Semantic review: normalized vertex and edge sparsest-cut rounding

Vertex drafts reviewed 9 October 2026, 05:19–05:21 UTC; final five-module sources, including the full edge bridge/corollary, reviewed 05:27–05:28 UTC. **No mathematical or quantifier defect found. All five strict compile logs are empty, 115 owned declarations pass the recursive axiom audit, and five isolated official kernel replays pass.** No Lean source was edited and no compiler was run by the reviewer.

## Exact reviewed sources

Paths are relative to `repo/Improved Upper Bounds for the Directed Flow-Cut Gap/DirectedFlowCutGap/`.

| File | SHA-256 |
| --- | --- |
| `FiniteHarmonicThreshold.lean` | `76e6664436a28fe3278a23286d70bce79e05eecd0df9b36fa63cd283f991174b` |
| `SparsestVertexBridge.lean` | `ba3b50c4164d28b4d8d4fc158b44158ff772e467e1ef913474b3700cc84d0e94` |
| `SparsestVertexCorollary.lean` | `a53dee404c71d9b8980d406ee3c85536130f6f9a60a2d028016197f3507beddd` |
| `SparsestEdgeBridge.lean` | `e2afd6756979b25b64f66a6b4e71c4f513ab62dc454ecb7c64c05e1d3cb18a1d` |
| `SparsestEdgeCorollary.lean` | `e322c42c51e2e9eac009259260ac81881392dd408a624790a01044b8990acb4a` |

All current source hashes were independently checked against the final manifest. The original three-source draft was compared in full: changes are elaboration/coercion repairs, omitted unused assumptions, and separately reviewed additions proving positive scaling of the fractional ratio, normalized mass equal to `mW` when `S=1`, and the explicit average-distance-one corollary. No former substantive claim was weakened or given a new mathematical premise. Both added edge modules were read in full, and final snapshots retained. This audit uses the previously reviewed actual vertex path/cut semantics and frozen all-cost vertex rounding estimates. It also checks correspondence with the normalized contract in `sources/2604.03412v3/COROLLARY7_PARAMETER_AUDIT.md`, whose source-normalization caveat remains applicable.

## Finite harmonic selection and numerical transfer

The harmonic number is the actual sum of reciprocals `1/(i+1)` over `Fin m`. A maximizing rank-weighted value bounds every distance by that maximum divided by its positive rank; summing gives the harmonic inequality. Sorting through a permutation into descending order then injects the rank prefix into the actual threshold index set. Equal distance values remain separate demand indices. Positive sum forces both the selected threshold and its threshold count to be positive. Neither a sorted-input assumption nor the desired good threshold is supplied as a premise.

For positive finite total distance `S`, the resulting inequality is `S≤H_m τ k`. Increasing `k` only to the actual number of separated demands gives the intended cost/count bound. Increasing it to at most `m` proves the crucial mass inequality `W/τ≤H_m(mW/S)`. This keeps the scale-sensitive factor that cannot be discarded in a raw sparsest-LP formulation. All division operations used in inequality transport have explicitly positive denominators. The objective may be zero throughout.

The harmonic envelope follows from Mathlib's genuine `harmonic_le_one_add_log` and `m≤n²`, giving `H_m≤1+2log(n+2)`. Its square absorbs both `H_m` and `H_m^(3/2)` since the envelope is at least one. The existing fixed-power subpolynomial theorem chooses a single constant before both `n` and `m`, including all small positive sizes. No asymptotic constant depends on the current demand family.

## Actual distances, cuts, and normalization

The bridge uses the existing endpoint-excluding directed vertex distance, and its separated-demand set contains precisely those pairs whose every actual simple path meets the selected internal vertices. The denominator is the cardinality of this actual separated subset, not merely the chosen rank count or a supplied abstract success counter.

The finite-distance hypotheses explicitly exclude infinity before an ENNReal distance is converted through `toNNReal` in the main bridge. Positive scaling of the extended distance is proved, with a positive scaling factor to avoid the zero-times-infinity case. More directly, scaled threshold membership is proved equivalent to the original extended distance being at least the positive threshold by the all-path characterization. Consequently a cut returned for `w/τ` separates every counted demand of original distance at least `τ`.

The mass is explicitly `W_avg=|P| W/S`, invariant under positive scaling. Rescaling lengths by `|P|/S` makes the distance sum exactly `|P|`; when this average-distance normalization is imposed, `W_avg` equals raw total weight. The graph/cost objective scaling is exact. Neither the generic mass identity nor the theorem's name silently identifies `W_avg` with the raw mass of a sum-distance-one LP.

Zero-distance demand pairs are retained in `P`, its cardinality, and the normalization; the positive-sum hypothesis merely ensures some positive distance. Infinity is treated separately: an unreachable demand gives the empty cut with zero cost and a positive actual separation count. Empty demands have zero separation count. Under finite distances, zero sum is proved equivalent to all actual distances being zero. The main ratio theorem does not claim a positive-denominator result in either empty or all-zero cases.

## Uniform final bounds and honest source scope

The size theorem takes the proved vertex rounding estimate at exponent slack `ε/2` and spends the other half absorbing the harmonic factor. The mass theorem does the same with the full `H_m^(3/2)` loss. The final minimum theorem chooses the maximum of the two global constants, before all finite instances, and selects the cut from the smaller displayed size/mass regime. This gives one actual cut with positive denominator and factor

`K n^ε min(n^(1/3), sqrt(|P|W/S))`

times the individual assignment's fractional ratio `C/S`. The constant is independent of vertex type, graph, demands, weights, and costs. The final proof instantiates every intermediate all-lengths rounding oracle with the proved AdaptiveVertexBound theorem; no final sparsity estimate or favorable optimizer remains an assumption.

This is a concrete normalized sparsest-cut rounding theorem for each length assignment. The same result is proved in both vertex and edge models; it does not select or identify a sparsest LP optimum, formalize maximum-concurrent-flow duality, or provide polynomial runtime. It also does not remove the source's normalization ambiguity recorded in the parameter audit. Those scope limits are visible in the inspected source comments and final hypotheses rather than being hidden in a theorem premise.

## Edge model and explicit normalized formulations

The full edge bridge uses actual edge distances, actual edge-weight/cost sums, and `EdgeCutsPair`. Every final edge output is explicitly a subset of `graphEdges G`. Its threshold rescaling, finite-distance guard before `toNNReal`, actual separated-demand count, harmonic mass loss, and positive-denominator proof mirror the individually checked vertex route. Nonedge values cannot add budget or appear in the returned cut.

Both models now separately prove positive-scale invariance of the fractional ratio as well as of normalized mass. The sum-distance-one lemma explicitly yields `W_avg=mW`. The average-distance-one final corollaries assume `S=m` with `m>0` and replace `W_avg` by raw total weight exactly, while replacing the fractional ratio denominator by `m`. These additions make the normalization contract reviewable in the theorem statement; they do not conceal or erase the ambiguity in the source's unqualified Corollary 7 wording.

## Independently inspected local verification

The five-module local evidence is preserved under `repo/Improved Upper Bounds for the Directed Flow-Cut Gap/verification/sparsest-normalized/`. Its manifest independently matches all five current source hashes and records strict options `-j1 -DautoImplicit=false -DwarningAsError=true`; all five compile logs are empty. Manifest SHA-256: `20336f3d902567fc40b6560669ac6251e06162c2610cf561db2b3523eda4e210`.

The combined audit driver enumerates the complete owned declarations separately for each of the five target modules, rejects an empty target enumeration, recursively collects axioms, and allows only `propext`, `Classical.choice`, and `Quot.sound`. The actual audit log has 115 distinct declaration names and passing counts 37/31/8/31/8. Its SHA-256 is `3e8860e9839ba5ff9d39b4523e00d89e919c2021d05b9a0e78f8f3da8da3649a`.

Each isolated replay driver invokes official `LeanChecker.replayFromImports` on its exact target before printing PASS; all five logs contain that corresponding PASS:

| Module | Kernel replay log SHA-256 |
| --- | --- |
| FiniteHarmonicThreshold | `868c81ab78a8d0955a413b2dc293721e279d666a81632d6801de9405494c00fe` |
| SparsestVertexBridge | `4037b9481eaf7c827c4d577e92e6fed9ad8ab0672740bf912cbbe52d6344d7a3` |
| SparsestVertexCorollary | `39a718ba3a6e0a210c4ec7303d294e416eedcdb23801e4d148bdd9c0597cd0bc` |
| SparsestEdgeBridge | `7e9e8832ba4c0ad430a4237328b023e3c9ec266397f8edabebba0da80c0d496a` |
| SparsestEdgeCorollary | `bbd7a95ad4c08acc4f21ae98f5616bf31b856f9fbb5607480142e95358b105d4` |

Official replay checks each target with its imported dependency environment. It is not an independent verifier or a fresh whole-project source rebuild in that isolated invocation. These modules are absent from the seventh aggregate manifest; enlarged root integration remains a separate gate. No remote Git publication or external CI result is asserted here.

## Eighth-checkpoint cross-check

At 05:34 UTC the full enlarged checkpoint completed. The reviewer independently matched all 53 source hashes, all 52 component imports plus root, all 53 unique official kernel-replay PASS targets, and the actual 2,854-declaration recursive allowed-axiom audit. The sources reviewed here are included and unchanged. See `eighth-independent-verification-review.md` for exact evidence hashes, fresh-build scope, count reconciliation, and local-versus-remote limitations.
