# LightEFT native parameters and heavy/light counting bridge

Tested source: `9cba496646e7a7c73513325b708cbfd0545a3133`.
Branch: `light-eft-spanners-checkpoints`; additive source and evidence commits use `[skip ci]`.
Paper directory: `Light Edge Fault Tolerant Graph Spanners`; worktree: `/workspace/light-eft-verification`.
Parent accepted source: `326a50b3b9e66d9c1bc8840575a7edc8e2f5effd`.
Parent accepted evidence: `743b63b81c0c5572d27664028f873a4014483289`.

This bounded checkpoint proves the corrected stretch/numerical specialization of the native multigraph existence theorem, including rounded higher competition, and a first native heavy/light counting bridge. It does not prove square-root-f dependence, Theorem 11, the full aggregate or Theorem 34. Independent review is pending.

The parent's acceptance of the prior soundness checkpoint is recorded as prior source/log/hash review, not fresh independent execution or CI. All 424 prior LightEFT proof modules and the entire prior evidence manifest remain byte-identical. Only two new proof modules and two aggregate imports were added. The aggregate itself was not compiled. Work stayed in the correct LightEFT directory and branch; no other project/workspace or website was inspected or changed during this task.

## Correct stretch and numerical specialization

`NativePaperParameters.nativePaperStretch eps k` is the nonnegative stretch `(1+eps)*(2*k-1)`. For eps>0 and integer k>0, its real coercion equals the paper expression and its value is strictly greater than one. The actual extremal threshold is **stretch+1**, not the larger printed `(1+eps)*2*k`.

The unchanged established theorem `extremalLightness_corrected_coarse_bound` gives

`L <= 8 + 2048/eps * n^(1/k)`

at this corrected threshold. The native pruning estimate contains L+1, so the new numerical envelope is

`B = 9 + 2048/eps * n^(1/k)`.

No additive loss or seed baseline is dropped. Epsilon has no upper cap. These statements also include n=0 and zero optimum; there is no division by n or optimum.

`exists_native_paper_bound` constructs an actual original-ID f-EFT spanner S for every finite native graph, arbitrary nonnegative finite weights, eps>0, k>0, f>0, h>0 and `2*f+h <= q+1`, with

`weight(S) <= (1 + 8*f*B/h) * opt_q`.

The seed is the attained genuine native q-connectivity minimum from the accepted construction. No forest, packing, blocking, simplicity or positive-edge-weight premise is externally supplied. The actual output is a subset of input IDs and satisfies the native walkwise fault-stretch contract.

`exists_native_paper_baseline` sets q=2f and h=1, giving

`weight(S) <= (1 + 8*f*B) * opt_(2f)`.

This bound is **linear in f**. It is not the square-root-f improvement and is not presented as Theorem 11.

## Integer competition and rounded result

`native_rounded_budget` proves exactly

`floor((2+eta)*f) = 2*f + floor(eta*f)` for eta>=0.

Consequently `h=floor(eta*f)+1` is positive and satisfies the host count with equality at q=floor((2+eta)*f). This uses floor, not ceil, and does not demand an extra vote at noninteger eta*f. `native_rounded_coefficient` then proves the denominator estimate for any nonnegative B.

`exists_native_paper_rounded` combines these facts with the constructed native output. For eta>0, f>0, eps>0 and k>0 it establishes

`weight(S) <= (1 + 8*B/eta) * opt_floor((2+eta)*f)`.

This closes that bounded higher-competition **native numerical existence specialization**. It retains baseline one for unrestricted eta, the actual corrected extremal threshold and pruning loss. It is not a runtime theorem, a full-paper acceptance claim, or the stronger exact-2f square-root bound.

The new positive-budget specializations do not instantiate the sampler at f=0. The accepted zero-fault canonical soundness, safe working-budget max(1,f) comparison, direct zero-optimum result for f<=q, and h=0 undivided-charge qualification remain unchanged. No zero-fault opt_0 ratio or h=0 division is inferred.

## Heavy/light reconciliation and new native counts

[HEAVY-LIGHT-RECONCILIATION.md](HEAVY-LIGHT-RECONCILIATION.md) follows the actual preserved simple-graph proof, records its positivity/domain restrictions, and identifies the native interface still needed. Source hashes are in `evidence/heavy-light-source-reconciliation.json`; this is static reconciliation, not a fresh replay of that preserved closure.

`NativeHeavyLightCounts` proves native host-assignment equality under seed intersection, cardinal and weighted multiplicity from a separate seed-blocker cap, the residual/seed cardinality budget, and the exact heavy/light weight partition on original IDs. Its endpoint derives from one actual traced blocker family at q=2f: every selected nonseed candidate has one unblocked host; a candidate with more than r residual blockers has seed cap at most f-r and at least 2r+1 unblocked hosts, for r<=f. Heavy candidates have the complementary residual cap r. No endpoints or parallel IDs are merged.

The remaining substantive obligation is weighted residual-cap sampling and component aggregation for candidate subfamilies, preserving the same full blocker family for cycle exclusion and L+1 through native pruning. Current native sampling is capped by full blockers, so it cannot simply be called with sqrt(f). The new counting bridge supplies the separate seed-count interface; it does not supply that missing weighted estimate. The native square-root-f theorem, further stronger native synthesis, full aggregate and Theorem 34 remain open. No new false paper statement was found.

## Validation

Official Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Release. All nine dependency pins are unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Toolchain executable, config, source and object hashes are recorded in the evidence.

This is incremental local validation. All 173 reused objects were hash-reconciled. One unchanged required module, `ExactExtremalDefinition`, was compiled and individually replayed; its source snapshot is checked against the frozen Git source. Both new modules passed `-j1 -DautoImplicit=false -DwarningAsError=true` and individual official kernel replay. No default Lake build, cache retrieval, dependency update, clean full build, aggregate build or CI was performed.

Entry points:

```
python checkpoints/light-eft-native-parameters-20261016/run.py dependencies
python checkpoints/light-eft-native-parameters-20261016/run.py compile NativePaperParameters
python checkpoints/light-eft-native-parameters-20261016/run.py compile NativeHeavyLightCounts
python checkpoints/light-eft-native-parameters-20261016/run.py replay ExactExtremalDefinition
python checkpoints/light-eft-native-parameters-20261016/run.py replay NativePaperParameters
python checkpoints/light-eft-native-parameters-20261016/run.py replay NativeHeavyLightCounts
python checkpoints/light-eft-native-parameters-20261016/run.py audit
python checkpoints/light-eft-native-parameters-20261016/run.py version
```

All three replay outputs contain exactly their corresponding singleton `replaying LightEFTSpanners.MODULE` line. The recursive audit passed: **1880 actual-owner project roots, 29 declarations owned by the two new modules, 24432 recursively visited constants and 14 opaque bodies**. Types and bodies are traversed; unsafe/partial declarations and axioms outside `propext`, `Classical.choice`, `Quot.sound` are rejected. This is the imported native/extremal closure, not full-paper coverage.

Eleven source-bound locked receipts cover one unchanged dependency compilation, five new-module compilation attempts, three singleton replays, one audit and one official version check. Three failed compilation attempts are preserved: coercion/implicit epsilon/addition-order elaboration, a local membership abbreviation, then explicit versus classical DecidableEq mismatch. Strict unused-simp diagnostics accompany the first two failures. These were proof elaboration repairs; no mathematical hypothesis or warning policy was weakened. All final compilations, the unchanged dependency and audit emitted zero warning headers. Raw failed diagnostics are classified as errors, and hints are not counted as warnings.

Each invocation had a process/resource preflight and used the common exclusive lock, unique UUID, submitted-source SHA256/snapshot, child PID, UTC/monotonic timings and reaping. `evidence/commands.jsonl` preserves exact executable paths/options/environment. `evidence/execution-reconciliation.json` checks UUID uniqueness, one lock inode, non-overlap and all snapshots/reaped children. The frozen source hashes, 176 local object hashes and preservation of 424 parent proof modules are in `evidence/source-object-hashes.json`.

The original recursive TSV is retained together with 58 ordered row-aligned chunks and [reconstruction manifest](audit-export/manifest.json). Concatenate chunk bytes in listed order with no separators. `evidence-sha256.json` covers reports, scripts, raw logs, UUID receipts, failed snapshots, hashes, inventories and chunks. `reconcile.py` performs source/log/hash checks without compiler execution.

Initial public CI checks found zero in-progress, queued, waiting, pending and requested runs. The remote branch is checked before an ordinary fast-forward push; both commits use `[skip ci]`. Terminal state records no compiler/checker, a free universal lock, about 23 GiB free disk and a 16 GiB memory limit. The worker pauses for independent review after publication.
