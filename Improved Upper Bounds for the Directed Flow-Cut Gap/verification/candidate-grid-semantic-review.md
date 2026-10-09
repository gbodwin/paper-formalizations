# Semantic review: exact finite-grid candidate optimization

Reviewed 9 October 2026, 05:19–05:22 UTC; final local receipts inspected 05:22 UTC. **No mathematical defect found in the three complete final sources. Strict build logs are empty, exhaustive owned-declaration axiom audits pass for 38/12/47 declarations, and all three isolated official kernel replays pass.** No Lean source was edited and no compiler was run by the reviewer.

## Exact inspected bytes

Paths are relative to `repo/Improved Upper Bounds for the Directed Flow-Cut Gap/DirectedFlowCutGap/`.

| File | SHA-256 |
| --- | --- |
| `CandidateGridRounding.lean` | `840aeb7036a4d9c9720358596e6cca66966b9f63c3ec18d219560dabc4ec3be8` |
| `CandidatePotentialSoundness.lean` | `fca3bb578ea27ffceb385a263778e5f0f402872c80e08ca2aaf939a9d8831165` |
| `CandidateGridOptimizer.lean` | `e7dcc6a4aa9455cf99df2780f39aeae8c01b7def85f3b27b1411a30a67746a0b` |

Exact snapshots were saved and final hashes rechecked: all three final sources are byte-identical to the fully reviewed snapshots, so no later proof or statement change needed reconciliation. The review also relies on the separately reviewed original candidate and permanent-terminal-port definitions. These modules are not included in the seventh checkpoint.

## Common-shift rounding and finite optimality

For a bounded system of integer difference inequalities, flooring every coordinate after the same shift preserves all differences, integer bounds, and equality pins. The common shift is essential; the proof does not use independent coordinate rounding. Shifted floors belong to the explicit finite box `I → Fin (L+1)`, with exactly `(L+1)^|I|` assignments.

The finite averaging identity sums equally spaced common shifts via Hermite's identity. The signed linear objective is handled correctly: its discrepancy from `N` times the original objective is bounded by the fixed sum of absolute coefficient values. Thus a finite grid minimizer is no larger than every feasible real objective by taking arbitrarily large positive averaging counts. The proof does not assume a real minimizer or a grid-integrality conclusion. The temporary finite-minimum premise in `grid_minimum_le_real` is discharged by `exists_min_image` on the actual nonempty finite feasible grid in the existence theorems.

The reusable shift-closed version assumes only boundedness and closure under all common shifts in `[0,1)`. In the candidate application both properties are proved explicitly from local constraints. They are not disguised assumptions of a desired optimal objective.

## Actual endpoint-safe path soundness

The potential inequality telescopes on the injective vertex sequence of an actual simple path, so converting sequence sums to finite vertex sums loses no multiplicities. Zero gaps at both endpoints permit deletion of precisely their contributions, including the zero-length path case. Permanent source/sink ports have zero extended weight, and nonnegative potential gaps therefore vanish there.

The source potential is pinned to zero and the selected target potential to `L>0`. A local gap bound by `L` times the actual extended vertex weight, together with the graph-edge inequalities, forces every lifted source-to-target path to have weight at least one. The preexisting exact port lift then yields the original endpoint-excluding fractional-cut condition. No endpoint weight is counted as an internal resource, and self or directly adjacent demands cannot be made spuriously feasible by port vertices.

Candidate reconstruction installs the original convention: weight exactly one on the existing selected set `X`, and gap divided by `L` outside it. Bounded potential gaps on `X` are at most `L`, so installing one still dominates them. The cap `B/L` is imposed only outside `X`, and can be below one. The outside-mass objective equals the signed potential objective divided by `L` exactly; neither ports nor selected vertices add hidden cost.

## Reverse potentials and exact candidate minimum

From any actual feasible candidate, before/after potentials are constructed from actual endpoint-excluding distances on the port graph. They use `clip(a)=(min(1,a)).toReal`, clipping before conversion, so unreachable distances become one instead of being incorrectly converted to zero. The after potential adds the current vertex's extended weight before clipping. The actual triangle inequality then gives each local edge constraint, and the clipping increment bounds every gap by `Lw(v)`.

All potentials lie in `[0,L]`; source and sink pins follow from reflexive zero distance and actual fractional-cut feasibility. Every port gap is zero. Outside candidate bounds yield the integer gap cap `B`. The signed objective sums exactly the original core gaps outside `X`, and is at most `L` times the original candidate's outside mass.

The final single-pair theorem therefore starts with an arbitrary feasible candidate, obtains a finite-grid potential minimum, reconstructs a feasible original candidate, and compares it against the distance potentials of every other real feasible candidate. This proves attained optimal outside mass and weights of the form `k/L` outside `X`; no real optimizer or optimum-value oracle is an input. The family theorem minimizes each independent label and sums these valid comparisons, without assuming an aggregate-family optimizer.

## Conditions and remaining algorithmic scope

The exact candidate theorem has natural parameters `L,B` and assumes `L>0`. It does not itself replace every real-threshold candidate state in the previously constructed adaptive law or provide a reduction from arbitrary real caps to those integer parameters. A graph with `n` vertices has `3n` port/core vertices and `6n` before/after coordinates, so direct grid enumeration can have `(L+1)^(6n)` assignments. The source explicitly acknowledges exponential search.

Consequently these modules establish finite-grid integrality and exact mathematical optimization for the stated candidate domain. They do not yet implement efficient minimum-closure optimization or max flow, establish bit complexity, or construct an executable polynomial-time adaptive algorithm. They are progress toward the source's candidate LP step, rather than a runtime certificate for the paper's randomized polynomial-time claims. The current source comments consistently preserve this distinction.

## Independently inspected local verification

All three `candidate-{grid-rounding,potential-soundness,grid-optimizer}-build.log` files are empty (SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`). Each inspected audit driver enumerates all declarations whose owner is its exact module, rejects a zero count, recursively collects all axiom dependencies, and allows only `propext`, `Classical.choice`, and `Quot.sound`. The success logs report 38, 12, and 47 audited declarations. These drivers cover the complete owned declaration set, although their logs print only totals rather than individual names.

| Module | Axiom audit log SHA-256 | Official kernel replay log SHA-256 |
| --- | --- | --- |
| CandidateGridRounding | `e5af43d2e6e74724dc9a5734d2681bae623fe1b5d2005cfefa71f1d8d12e41fd` | `7f9521f292bc10c77d2c0271a54d04b5f7d4f6207ac3c878d3275aa553b049d2` |
| CandidatePotentialSoundness | `02f51555db93111c5b4e4f2f400d2e5369f511fb87421a4e07765ac2c756b37d` | `3bd1b6d488fccdf9e115c6087576ed54ab8604ab3ccd1ed3271b2cd030458b09` |
| CandidateGridOptimizer | `611d9fdbfa4fe0c021aec733ab51b8dcdd6fe06d3ae8f569694e75bd426cccfa` | `e5da0b07e20d0bee822918ebcfab50eb8e754b6d38fb3662018b14cb6d4b02bb` |

Each replay driver invokes official `LeanChecker.replayFromImports` on its own module and prints the target-specific PASS afterward; each log contains that PASS. This is kernel replay of the target declarations with imported dependencies, not a separate proof checker or an assertion of polynomial-time evaluation.

These modules are not in the seventh source manifest. Their status rests on the exact final bytes and their own subsequent local receipts; an enlarged aggregate source-bound checkpoint is separate. No Git publication or external CI result is claimed here.

## Eighth-checkpoint cross-check

At 05:34 UTC the full enlarged checkpoint completed. The reviewer independently matched all 53 source hashes, all 52 component imports plus root, all 53 unique official kernel-replay PASS targets, and the actual 2,854-declaration recursive allowed-axiom audit. The sources reviewed here are included and unchanged. See `eighth-independent-verification-review.md` for exact evidence hashes, fresh-build scope, count reconciliation, and local-versus-remote limitations.

The fresh aggregate owns 11 CandidatePotentialSoundness declarations versus the earlier standalone audit count of 12. All seven explicitly named source definitions/theorems are present in the fresh ownership enumeration, source bytes are unchanged, and full replay passes. The old count-only standalone log does not identify the differing generated name; no exact duplicate-name attribution is made. See the eighth receipt for the ownership diagnostic and authoritative aggregate count.
