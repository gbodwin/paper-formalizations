# Current LightEFT main-result coverage

Reconciled against accepted native source `753ae06c2921597cb39cd72bde25bc99e13a71e5` and evidence `88fa6ea4990488c2d3af870283ba47d6b35fec85`. The parent reports independent acceptance of all 122 manifest entries, 59 chunks, nine sequential receipts and the native residual/square-root proof chain. This records that review; it is not new reviewer execution or CI.

This document supersedes stale open-native-upper notes in historical README/checkpoint entries. Earlier source, diagnostics, corrections and historical statement-map text remain preserved. The new `current_native_coverage` fields in `verification/statement-map.json` point here. No whole-paper completion is claimed.

Let n be the finite ambient vertex-type cardinality, f>0, k>0, epsilon>0, t=(1+epsilon)(2k-1), L=extremalLightness(n,t+1), and B=9+2048/epsilon*n^(1/k). Native outputs are subsets of actual original undirected edge IDs. Parallel identities and loops are not merged, weights are finite nonnegative reals, and faults are sets of those original IDs. The optimum opt_q is attained by an actual q-fault connectivity preserver. Weight inequalities do not divide by the optimum.

| Paper claim | Current proved scope | Explicit exclusions/qualifications |
|---|---|---|
| Theorem 9 | Preserved `RealStretchLowerFamily` finite lower construction for real stretch >=1, q<=2f-1, n=(m+3)(f+1), m+2>=2 ceil(t), ratio >=n/(16 f² t), unbounded order for each fixed parameter tuple | Not an every-n family or an epsilon-uniform coefficient/onset claim |
| Theorem 10 upper half | `NativeSquareRootOutput.exists_native_paper_sqrt` constructs the genuine native f-EFT output with weight <=(1+16 sqrt(f) B) opt_(2f); rounded higher competition is also proved | Corrected finite numerical upper result, not all literal lower/uniform/runtime clauses |
| Theorem 10 lower half | Preserved fixed-parameter lower family above, with actual denominator/nonvacuity | Literal jointly uniform every-n/epsilon wording remains qualified |
| Theorem 11 upper half | `exists_native_sqrt_output` gives the canonical optimum-seeded native output with Nat.sqrt f; `exists_native_sqrt_bound` gives weight <=(1+16 sqrt(f)(L+1)) opt_(2f) | Uses **t+1**, not the documented false printed argument (1+epsilon)2k; retains baseline 1 and pruning loss +1; no lower/Theorem34 or runtime conclusion |
| Theorem 12 upper half | `NativeMinimumOutput.exists_native_minimum_output_bound`: weight <=(1+8f(L+1)/h) opt_q under h>0 and 2f+h<=q+1. `NativePaperParameters.exists_native_paper_rounded`: weight <=(1+8B/eta) opt_floor((2+eta)f), eta>0 | Floor competition and h=floor(eta*f)+1 are explicit; baseline remains for unrestricted eta; no printed-threshold or lower/runtime claim |
| Theorem 13 | Preserved corrected simple-graph mathematical randomized correctness/lightness and represented atom-model execution statements under their explicit hypotheses | Native deterministic existence is not a native randomized algorithm. Efficient seed/packing/random generation, physical bit runtime and full printed algorithmic guarantee remain excluded |
| Theorem 34 | Written denominator certificate is refuted by preserved actual counterexamples; exact cloud-connectivity threshold and weaker repaired certificates are proved | General lower theorem remains a **substantive open obligation**; it is not declared false or repaired |
| Question 35 and cited background not needed by the above chains | Historical inventory remains explicit | Not silently promoted to completed claims |

## Actual native proof chain

`NativeSeedBudget.exists_minimum_seed_budget` constructs the attained seed and original-ID forest budget. `NativeGreedySoundness` proves arbitrary-fault normalization, persistent surviving-edge coverage and edgewise replacement. `NativeCompleteInput` proves complete duplicate-free sorted input and soundness of the actual canonical output.

`NativeCycleBlocking` derives one actual traced full blocker family and its original-ID cycle exclusion. `NativeHeavyLightCounts` separates seed blocker count from residual count. `NativeResidualSampling` samples residual blockers while proving disjointness from the original **full** blockers on the sampled host. `NativeResidualExtremal` uses actual component subtypes, minimum-tree pruning, full native girth and exact weight transport, obtaining h*weight(U)<=8r(L+1)*weight(seed) with distinct seed cap b, multiplicity h and residual cap r. `NativeSquareRootOutput` proves both heavy/light charges, the integer Nat.sqrt f conditions and the joined endpoint. No packing, blocker, sample-weight or extremal oracle remains in the final existence statements.

## Boundaries and documented corrections

- Positive f includes f=1; the repaired sampler avoids the invalid 1/f boundary argument.
- Zero weights, empty inputs and zero optimum are admitted. `exists_native_sqrt_zero` proves actual zero weight of the constructed positive-f output at zero optimum.
- For f=0, preserved canonical soundness and the direct zero-optimum result apply. A positive-optimum opt_0 square-root specialization is not inferred by substituting zero into the positive sampler.
- h=0 only permits the undivided charge. No ratio bound is derived from it.
- The corrected numerical extremal theorem has baseline 8; retaining the pruning loss gives 9. Neither the additive seed baseline nor L+1 is silently removed.
- Infinite distances/unreachable demands are handled by actual walk witnesses and the existing extended-distance corollary at positive stretch.
- Signed edge weights, infinite graphs, runtime conclusions, lower claims beyond the preserved fixed-parameter scope, and whole-paper completion are excluded.

The substantive threshold/certificate corrections in `CORRECTIONS.md` remain unchanged. This reconciliation does not introduce a new counterexample or relabel a proof repair as a false theorem.

## Aggregate/CI status

The source-derived aggregate closure contains 429 LightEFT leaf modules, 56 required support modules and the aggregate: 486 modules total. All LightEFT leaves occur in that import closure.

The authorized linter-only continuation now strictly compiles all 486 modules with `-j1 -DautoImplicit=false -DwarningAsError=true`, and all 485 leaf/support modules pass official singleton kernel replay. Seventeen source files have mechanical repairs with mathematical assumptions retained; the other 469 module sources are unchanged. The original blocker and all failed attempts remain preserved.

The complete actual-owner diagnostic export contains 9,327 roots, 60,746 recursively visited constants and 48 opaque bodies. It identifies 57 partial `._unsafe_rec` implementation companions and no unsafe project roots. None of those companions is reachable through the types/bodies of the 9,270 safe roots; that closure uses only `propext`, `Classical.choice`, and `Quot.sound`. Nevertheless, the strict all-owner no-partial gate fails. No companion was silently excluded or allowlisted and no clean CI was triggered. This audit-policy boundary requires independent review; it is not a mathematical counterexample.

An extra aggregate-prefix checker invocation expanded into internal parallel tasks under the official checker's prefix semantics and was OOM-killed at the 16 GiB limit. Its source-bound receipt and diagnostics are preserved and it is not counted as a singleton pass. The aggregate owns zero declarations; it is strictly compiled and covered by the complete owner audit. Future prepared CI replays only the 485 actual leaf/support modules, individually.

See `checkpoints/light-eft-strict-aggregate-20261016/REPORT.md` for the exact diff, hashes, all 988 external invocation receipts, complete diagnostic inventory and 208 reconstructible chunks. Earlier bounded acceptance remains within its recorded scope. Theorem 34 remains open; runtime and whole-paper completion are excluded.
