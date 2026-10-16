# LightEFT native residual sampling and square-root fault bound

Tested source: `753ae06c2921597cb39cd72bde25bc99e13a71e5`.
Branch: `light-eft-spanners-checkpoints`; additive source/evidence commits use `[skip ci]`.
Paper directory: `Light Edge Fault Tolerant Graph Spanners`; worktree: `/workspace/light-eft-verification`.
Accepted parent source: `9cba496646e7a7c73513325b708cbfd0545a3133`.
Accepted parent evidence: `2b5b83d46afa2fe09d95243560e2f2f5af7857b3`.

This checkpoint proves the previously missing native residual-cap sampled-host theorem, carries it through pruning and component/forest aggregation, and proves the native square-root-f weight bound using the actual canonical EFT output. The coefficient retains the additive seed baseline and **L+1**. This is a corrected finite native-model existence theorem, not acceptance of the printed extremal threshold, the full aggregate, runtime claims, Theorem 34 or the whole paper. Independent review is pending.

The parent's acceptance above is recorded as prior independent source/log/hash review, not fresh CI or independent execution. All 426 prior LightEFT proof modules and the prior evidence manifest remain byte-identical. Only three new modules and three aggregate imports were added; the aggregate itself was not compiled. No applicable AGENTS.md or Lean-specific skill was found. Work stayed in the LightEFT directory and branch; no old SCC, distance-sparsification or deleted workspace was accessed, and no website was changed.

## Residual sampling with full-blocker disjointness

`NativeResidualSampling.exists_residual_sampled_component_host` works with an arbitrary candidate subfamily U contained in actual input IDs outside seed H, a supplied constructed seed-forest budget, and one explicit full blocker family. Its sample cap is `|(block e) minus H| <= r`, with r>0; it does not assume that the full blocker set has size at most r.

For a forest i and one of its actual component vertex subtypes, K is the candidate set assigned to that host component. Assignment still uses disjointness of the forest from the **full** blocker set. The existing finite weighted sampling theorem is applied to K with residual blockers `block e minus H`, yielding a sample S and its surviving candidates Q. The sampled native host is the component forest union Q.

The proof then establishes disjointness from every full blocker:

- A blocker cannot be a retained forest ID because the original host assignment excludes the full blocker set from the forest.
- A blocker that is a sampled candidate lies outside H, hence belongs to the residual blocker set; the sampling avoidance property excludes it.

All host IDs remain actual input IDs, endpoints remain in the original component, the component forest is retained, and the host weight satisfies `weight(K) <= 4*r*weight(sampledHost)`. The proof preserves original edge identities, including parallel IDs and loops. No simplicity or positive-edge-weight assumption is introduced.

## Pruning and aggregation with separate budgets

`NativeResidualExtremal.native_residual_component_bound` additionally assumes U is a subfamily of the actual native greedy output outside H and uses the same full `TracedBlockers` family throughout. Full-blocker disjointness supplies the existing native clean-cycle theorem. The accepted minimum-tree and seed-pruning construction retains sampled candidates, provides a minimum forest no heavier than the original component forest, and gives full native weighted girth.

The established native extremal transport therefore yields the per-component estimate

`weight(componentCandidates) <= 4*r*(L+1)*weight(componentForest)`,

where `L = extremalLightness(card V, t+1)` and t+1>2. The +1 is the actual pruning loss: the sampled host is covered by the pruned host plus the original component forest. It is not discarded or assumed absorbed into L.

`native_residual_extremal_aggregate` sums the exact component partitions, then the forest congestion weight budget, obtaining

`sum_i weight(hostCandidates_i) <= 8*r*(L+1)*weight(H)`.

`native_residual_candidate_charge` combines that estimate with the accepted seed-restricted host multiplicity. Its independent parameters are:

- b: cap on seed blockers `|(block e) intersect H|`;
- h: guaranteed host multiplicity, requiring `2*b+h <= q+1`;
- r>0: cap on residual blockers `|(block e) minus H|`;
- f: the original greedy fault budget, kept distinct from those three quantities.

Its conclusion is the undivided inequality

`h*weight(U) <= 8*r*(L+1)*weight(H)`.

It permits h=0, but makes no division-based inference in that case. Individual edge weights, component-tree weights and seed weight may all be zero. The component and aggregate estimates remain actual weight inequalities, not totalized ratios.

## Heavy/light combination and attained optimum

`NativeSquareRootOutput.native_heavy_light_candidate_bound` chooses one actual full traced blocker family for q=2f and partitions the selected nonseed IDs exactly:

- Heavy: residual count <= r. Use seed cap f, one host, and residual sampling cap r.
- Light: residual count > r. Its seed cap is <= f-r, so use 2r+1 hosts and residual sampling cap f.

The same residual theorem is applied separately to these genuine subfamilies. Under f>0, r>0, r<=f and `f <= r*(2*r+1)`, each side has weight at most `8*r*(L+1)*weight(H)`. The exact filtered weight partition prevents duplicate charging. Adding the seed back gives

`weight(nativeOutput) <= [1+16*r*(L+1)]*weight(H)`.

`native_sqrt_parameters` proves all the integer conditions for r=Nat.sqrt f when f>0. No square-root sampling result is postulated. `exists_native_sqrt_output` constructs the attained minimum 2f-connectivity seed and its forest budget, applies this proved heavy/light estimate to the complete duplicate-free sorted input, and retains the accepted native EFT soundness of the same output.

`exists_native_sqrt_bound` converts Nat.sqrt f to Real.sqrt f and proves:

`weight(S) <= [1+16*sqrt(f)*(L+1)]*opt_(2f)`.

The endpoint assumptions are exactly finite vertex and edge types, a native graph G, finite nonnegative weights w, t>1, and natural f>0. There is no externally supplied seed, forest packing, blocker family, sampled host, high-girth certificate, simplicity hypothesis or positive seed/edge weight. Output S is a subset of the actual input IDs and satisfies the native original-ID walkwise f-EFT contract. The accepted distance corollary handles extended distances at this positive stretch, including unreachable pairs.

`exists_native_paper_sqrt` instantiates the corrected paper stretch t=(1+epsilon)*(2k-1), epsilon>0 and integer k>0, and the established numerical extremal bound. It proves

`weight(S) <= [1+16*sqrt(f)*(9+2048/epsilon*n^(1/k))]*opt_(2f)`.

The 9 is 8 from the established numerical extremal bound plus the retained pruning loss. This now has square-root-f dependence; the earlier linear-f bound is preserved unchanged. The corrected exact threshold remains t+1, not the larger printed `(1+epsilon)*2k` whose issue was documented earlier. No new paper counterexample is asserted.

## Boundary cases and remaining scope

There is no division by the optimum or a tree weight. The zero-optimum corollary `exists_native_sqrt_zero` proves that the **constructed canonical positive-f output itself** has weight zero when opt_(2f)=0; it does not rely on defining a quotient at zero. Empty inputs, isolated vertices and arbitrary zero weights are admitted. Residual sampling requires r>0, fulfilled by Nat.sqrt f for f>0, including f=1. The established repaired sampler is used unchanged.

No positive-sampler claim at f=0 is made. The prior canonical zero-fault soundness and direct zero-optimum theorem for f<=q remain available unchanged. The undivided h=0 statement remains qualified. No sharper positive-optimum opt_0 bound is inferred.

This closes the native residual-cap weighted bridge and corrected square-root-f existence endpoint described as open in the prior report. Further full-paper reconciliation, any desired normalization/absorption of additive constants, a full aggregate build, runtime/algorithmic-complexity conclusions and Theorem 34 remain outside this checkpoint. No whole-paper completion is claimed.

## Validation and raw evidence

Official unmodified Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Release. All nine dependency pins remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Exact toolchain/configuration hashes, dependency revisions and status are retained.

This was incremental local verification. All 176 reused local object hashes were reconciled; no dependencies were rebuilt. The three new modules passed `-j1 -DautoImplicit=false -DwarningAsError=true`, and their successful submitted snapshots equal the source commit above. Each new module was individually replayed with official `leanchecker -v LightEFTSpanners.MODULE` and exactly the expected singleton replay output. No default Lake build, aggregate build, clean rebuild, cache retrieval, dependency update or CI run occurred.

Entry points:

```
python checkpoints/light-eft-native-residual-20261016/run.py compile NativeResidualSampling
python checkpoints/light-eft-native-residual-20261016/run.py compile NativeResidualExtremal
python checkpoints/light-eft-native-residual-20261016/run.py compile NativeSquareRootOutput
python checkpoints/light-eft-native-residual-20261016/run.py replay NativeResidualSampling
python checkpoints/light-eft-native-residual-20261016/run.py replay NativeResidualExtremal
python checkpoints/light-eft-native-residual-20261016/run.py replay NativeSquareRootOutput
python checkpoints/light-eft-native-residual-20261016/run.py audit
python checkpoints/light-eft-native-residual-20261016/run.py version
```

The recursive audit passed: **1893 actual-owner project roots, 13 declarations owned by the three new modules, 24541 recursively visited constants, and 14 opaque bodies**. Types and bodies are traversed; unsafe/partial declarations and axioms outside `propext`, `Classical.choice`, `Quot.sound` are rejected. Coverage is the actual imported native/extremal closure, not the full aggregate or every paper module.

Nine unique source-bound locked receipts cover four compilation attempts, three individual replays, one recursive audit and one official version check. One compilation failed: a candidate-subfamily membership was used where membership in output-minus-seed was required. The repair explicitly transports membership through the already stated subfamily inclusion. Its UUID `39452fe724434358ab2589a7ec305aae`, full raw diagnostic and submitted source remain preserved. This was a proof repair, not a new assumption or false mathematical statement.

Final compilations and audit emitted zero warning headers; no linter was disabled. The failed attempt is classified as an error. Every invocation had a process/resource preflight and ran sequentially under the universal exclusive lock, with UUID, submitted source SHA256/snapshot, child PID, UTC/monotonic timings and child reaping. No parallel worker or runtime shim was used. Exact executable paths/options/environment are in `evidence/commands.jsonl` and authoritative UUID receipts/raw logs are under `evidence/attempts`.

`reconcile.py` checks source/log/hash evidence without running Lean. `evidence/execution-reconciliation.json` verifies all nine snapshots, unique UUIDs, one lock inode, non-overlap and reaped children. `evidence/source-object-hashes.json` binds the frozen source, 179 local objects and preservation of 426 parent proof modules. The original recursive TSV is retained with **59** ordered row-aligned chunks and [reconstruction manifest](audit-export/manifest.json); concatenate listed bytes without separators. `evidence-sha256.json` covers reports, scripts, logs, receipts, failed snapshots, hashes, inventories and chunks.

Initial resource/process/lock checks and public CI checks preceded compilation. There were no compiler/checker processes or active/queued/waiting/pending/requested CI runs. Approximately 23 GiB disk was free, with a 16 GiB memory limit. Terminal evidence shows no compiler/checker and a free universal lock. Remote state is checked before an ordinary additive fast-forward push with CI skipped; the worker then pauses for independent review.
