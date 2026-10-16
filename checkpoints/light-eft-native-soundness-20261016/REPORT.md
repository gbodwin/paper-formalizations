# LightEFT native greedy soundness and complete minimum-seed output

Tested source: `326a50b3b9e66d9c1bc8840575a7edc8e2f5effd`.
Branch: `light-eft-spanners-checkpoints`; additive source/evidence commits use `[skip ci]`.
Working directory: `/workspace/light-eft-verification`; paper directory: `Light Edge Fault Tolerant Graph Spanners`.
Accepted parent source: `06d44ae091e689695ec0eadf17ff4b9ec9e9cd0b`.
Accepted parent evidence: `2c7ec73cda703371dfae30873e2f15c43f1c4692`.

This is a NEW LightEFT checkpoint. It proves native greedy EFT soundness, constructs the complete duplicate-free sorted actual-input list, and supplies an attained-minimum-seed weight bound with explicit parameters. Independent review is pending. The full aggregate, further parameter synthesis and Theorem 34 are not claimed complete.

The parent's acceptance of the native extremal checkpoint is recorded as prior independent source/log/hash review, not fresh CI. All 421 existing LightEFT proof modules and the prior evidence manifest remain byte-identical. The aggregate gains only three imports and was not compiled. Before the parent's corrective message, an obsolete SCC checkpoint was mistakenly inspected read-only; that work is unrelated and is not counted as progress or validation here. After correction, development and verification stayed in this LightEFT worktree. No other project source, website or security setting was changed.

## Fault normalization and soundness

`NativeGreedySoundness.lean` proves `Walk.transfer_faults`: changing a fault set preserves an actual native walk and its weight when each usable retained edge remains available. `NativeCovered.all_faults` normalizes arbitrary original-ID faults F to F intersect A, applies the insertion test, then transfers the resulting walk back to F. The normalized set has no larger cardinality. Faults outside the current selected set are not silently dropped from the final statement.

`NativeSurvivingCovered` states precisely the condition needed for edgewise replacement: the original edge itself must survive. A retained surviving edge supplies its one-edge walk when t >= 1. Coverage persists under adding selected edges, by actual walk transport with unchanged weight. Induction on the tail-first native greedy list handles both skipped edges and insertions; already selected seed edges remain covered. `nativeGreedy_sound` applies the existing native edgewise replacement theorem to seed union listed IDs. It needs no sorting, uniqueness, completeness, connectivity, positive edge weights or positive fault count.

Faults continue to delete actual original edge identities, including parallel IDs. Loops, zero weights and unreachable demands retain their native semantics. The result is the walkwise `IsEFTSpanner` contract; its existing `distance_le` corollary handles extended distances for nonzero t. Here t >= 1 ensures that condition. No path-restricted/global-distance equality is introduced.

`IsEFTSpanner.fault_mono` permits lowering the fault budget. `zero_weight_preserver_isEFT` proves that every retained edge of a zero-total-weight connectivity preserver has weight zero, hence every returned walk has weight zero. Such a preserver is an EFT spanner for any nonnegative stretch and any f <= q, without dividing by the seed weight.

## Complete canonical input

`NativeCompleteInput.lean` sorts the finite set of actual original input IDs with the relation w(d) <= w(e). Since the fold is tail-first, it processes lighter edges first. The proof establishes permutation of the actual input list, membership equivalence, no duplicates, pairwise ordering, and exact equality of its toFinset with `inputEdges G`.

`nativeOutput` runs the existing native greedy algorithm on that complete list. Seed IDs may occur in the list; the algorithm's existing membership test skips them. No unproved seed/list disjointness premise is needed. `nativeOutput_sound` proves the result is an EFT spanner of all actual input IDs for any input-contained seed, every natural f including zero, and t >= 1. The seed remains a subset of the output.

## Minimum seed, budgets and boundaries

Let L = extremalLightness(card V, t+1), opt_q be the attained native q-connectivity minimum, and S be the canonical output seeded by an attained minimum H.

`NativeMinimumOutput.lean` combines the accepted candidate estimate with the exact disjoint weight identity

`weight(S minus H) + weight(H) = weight(S)`.

For t > 1, f > 0 and 2*f+h <= q+1 it proves

`h * weight(S) <= (h + 8*f*(L+1)) * opt_q`,

along with actual f-EFT soundness of S. `exists_minimum_seed_budget` constructs the optimum seed and its forest budget; neither is an external oracle in this endpoint. The additive pruning loss L+1 is retained throughout.

When h > 0, `exists_native_minimum_output_bound` proves

`weight(S) <= (1 + 8*f*(L+1)/h) * opt_q`.

No positive optimum or positive individual edge weight is assumed. The concrete justified choice q=2*f, h=1 gives `exists_native_baseline` with coefficient `1+8*f*(L+1)` for f>0.

Boundary qualifications are explicit:

- h=0: the undivided charge remains true, but does not imply a finite ratio. The ratio theorem requires h>0.
- f=0: canonical greedy soundness holds directly. The positive sampling estimate is not instantiated at zero. `exists_native_baseline_all_budgets` uses working budget max(1,f), then lowers the fault budget. At f=0 it compares against opt_2 with coefficient 1+8*(L+1), **not** opt_0 with coefficient 1. A sharper nonzero-optimum opt_0 bound is not supplied here.
- Zero optimum: `exists_native_zero_optimum` selects the attained seed itself and proves zero-weight EFT soundness whenever f<=q, including f=q=0, for any nonnegative t. This proof is independent of h and the positive sampling estimate.
- Empty inputs, isolated vertices, zero weights and parallel original identities are admitted; none is excluded by a new mathematical premise.

The remaining premises of the positive-budget bound are finite vertex/edge types, native graph G, nonnegative finite weights, t>1, f>0, and the stated integer budget inequality (plus h>0 only for division). This bounded native existence result does not claim the full paper's parameter specialization, runtime result, Theorem 34, aggregate acceptance or whole-paper completion. No false paper statement was found.

## Exact validation and evidence

Official unmodified Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Release. All nine dependency revisions remain pinned, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Exact toolchain executable and configuration hashes are in `evidence/toolchain-hashes.json`; dependency revisions and status are in `evidence/dependency-pins.json`.

This is incremental local verification. All 170 reused local object hashes were reconciled; no dependency rebuild, cache retrieval, default Lake build, clean build or CI run occurred. The three new modules passed `-j1 -DautoImplicit=false -DwarningAsError=true`. Their final submitted snapshots equal the source commit above. Each was individually replayed with official `leanchecker -v LightEFTSpanners.MODULE`, with exactly the corresponding singleton replay line. Entry points:

```
python checkpoints/light-eft-native-soundness-20261016/run.py compile NativeGreedySoundness
python checkpoints/light-eft-native-soundness-20261016/run.py compile NativeCompleteInput
python checkpoints/light-eft-native-soundness-20261016/run.py compile NativeMinimumOutput
python checkpoints/light-eft-native-soundness-20261016/run.py replay NativeGreedySoundness
python checkpoints/light-eft-native-soundness-20261016/run.py replay NativeCompleteInput
python checkpoints/light-eft-native-soundness-20261016/run.py replay NativeMinimumOutput
python checkpoints/light-eft-native-soundness-20261016/run.py audit
python checkpoints/light-eft-native-soundness-20261016/run.py version
```

Every compiler/checker/version/audit invocation used the universal exclusive lock, one unique UUID, source hashes and snapshots, child PID, UTC and monotonic timings, process/resource preflight, and child reaping. Operations were strictly sequential with one ordinary worker. `evidence/commands.jsonl` contains exact executable paths/options/environment; UUID directories preserve authoritative raw logs and failed submitted sources. `SequentialLean.py` supervises external processes without modifying the Lean runtime.

Twelve receipts comprise seven compilation attempts, three individual replays, one audit and one version check. Four compilation attempts failed: a multiplication-lemma argument mismatch, an omitted definitional unfolding, ratio multiplication orientation plus an unused section instance, then an already-closed goal and doc-comment/omit placement. These are proof elaboration and strict linter repairs. They added no mathematical assumptions and disabled no warning checks. All raw diagnostics remain preserved. Final strict modules, replays and audit emitted zero warning headers; no hint text is counted as an extra warning. Failed strict diagnostics remain errors rather than being hidden in the warning count.

The recursive audit passed: 1844 actual-owner project roots, 39 declarations owned by the three new modules, 24379 recursively visited constants, and 14 opaque bodies. It recursively examines types and bodies, rejects unsafe/partial declarations and any axiom outside `propext`, `Classical.choice`, `Quot.sound`. This covers the imported native/extremal closure, not every LightEFT module or the full aggregate. `evidence/source-object-hashes.json` records the exact source commit, new source hashes, 173 local object hashes and preservation of 421 parent proof modules.

`reconcile.py` performs source/log/hash checks without Lean. `evidence/execution-reconciliation.json` verifies all 12 snapshot hashes, unique UUIDs, one lock inode, non-overlapping execution and reaped children. The original recursive TSV is preserved. Its 58 ordered row-aligned chunks and reconstruction hash are in [audit-export/manifest.json](audit-export/manifest.json); concatenate bytes in listed order without separators. `evidence-sha256.json` covers this report, scripts, raw diagnostics, receipts, snapshots, hashes, inventories and chunks.

The branch was created at accepted evidence 2c7ec73 and extends the existing remote branch tip faaaad5a31de3fef117f023154405ea21f2af1aa by ordinary fast-forward. No force push or workflow changes are used. Initial public CI checks found no in-progress, queued, waiting, pending or requested runs. Terminal state records no compiler/checker, a free universal lock, approximately 23 GiB free disk and a 16 GiB memory limit. After the additive evidence push with CI skipped, the worker pauses for independent review.
