# Light EFT authorized attempt: stopped on first import failure

**Result: failed compile; no acceptance.** Exactly one authorized entry call used reviewed wrapper **`f49febff6967af577496e79b18e58899253d2fce`**. Its fresh coordination callback ran once after planning. Lean then exited **1** during the first stage. Resolution, singleton replay and the focused owner/axiom audit were **not run**. No repair, second entry call or retry was attempted.

## Exact failure and source scope

The [raw compiler log](../light-eft-supplied-forest-activation-20261018/production-evidence/compile/raw.log) contains this single Lean diagnostic:

```text
SuppliedForestGoodEvent.lean:1:0: error: object file '/workspace/light-eft-verification/.lake/supplied-forest-staged-782280b1cbdf496b9d5e228002e17686/objects/LightEFTSpanners/VotingOutput.olean' of module LightEFTSpanners.VotingOutput does not exist
```

The log retains the full source path. There were **zero Lean warnings**; mimalloc option names such as `max_warnings` are not compiler warnings. Its allocator output, complete exception traceback, and exit status are preserved unchanged.

The compiler requested the dependency under the fresh output root. That file is absent there. A read-only [post-failure observation](missing-import-observation.json) confirms that the accepted `LightEFTSpanners.VotingOutput` object exists in the older bound input root and matches its accepted hash. The physical dependency/shadow and preservation checks had passed. This result exposes an import-selection blocker; it does not establish that the compiler selected the accepted object, and no cause beyond these observations is asserted here. No object was copied, linked, rebuilt or relocated to repair it.

The attempted mathematical source remains the staged source at **`40029953e9e53525f0f1f431d6d56333b05183a3`**, SHA256 **`6356a3b369813a155e824e471b0f7a48d29a66fb117db41eca767ed3300febee`**, 4,988 bytes. The exact submitted source snapshot is in the compile evidence. Frozen import source remains **`78cb40c7837db049d645d73696f2e0b724ce8a3b`**. No target `.olean` was produced, so there is no new object hash, kernel replay result or new audit closure to report. The failure occurs on the initial import; this attempt supplies no acceptance of the theorem body. Source and pins remain unchanged and unpromoted.

## Execution and bounds

[Controller result](controller-result.json), [entry source](invoke_once.py), [raw controller output](controller-raw.log), [exact executed command/environment and tool bindings](commands-and-tools.json), and the complete [compile receipt](../light-eft-supplied-forest-activation-20261018/production-evidence/compile/receipt.json) are preserved. The official pinned Lean 4.34.0 executable was used directly with `-j1 -s65536 -M5120 -DautoImplicit=false -DwarningAsError=true` and the reviewed root/output/source arguments. Leanchecker was bound but never executed. There was no aggregate build, retrieval, source promotion or CI execution.

The unique compile attempt UUID is **`405e02f9be5d488f973d15fff877c052`**; controller PID **5334**, isolated child PID/PGID/SID **5489**. The new common lock was device/inode **`33:3258`**, epoch `e89a17dc569247b482fb1b36522052bc`; historical inode continuity is not claimed. Fresh coordination preceded lease acquisition by **0.074636302 seconds**, within the unchanged 60-second window. All ownership facts, submitted-source bindings, inherited lock identity, kernel readbacks, samples and monotonic/UTC timestamps are recorded.

The approved resource settings remained unchanged. Kernel readback verified AS **12 GiB**, CPU **60 seconds**, ordinary FSIZE **16 MiB**, CORE **0**. The per-stage wall deadline remained **90 seconds**, with existing visible/host admission, RSS and anonymous-growth checks. Preexec admission recorded visible headroom **8,458,100,736 bytes**, host available memory **17,236,123,648 bytes**, and free disk **4,774,785,024 bytes**. Visible accounting retains its `PARTIAL_VISIBLE_ANCESTORS; unseen limits UNKNOWN` qualification.

There are **8** recorded runtime samples. Preexec preservation/handshake waiting took **35.472890390 seconds**; terminal confirmation occurred **35.780505705 seconds** after runtime-wall start. Recorded sampled RSS peak is **56,111,104 bytes**, while `wait4` reports **525,160 KiB** maximum RSS. The sampled metric is intermittent, not a continuous peak or kernel heap cap. No resource guard or timeout was reported as the failure; the child returned status 1 with the import diagnostic.

## Preservation and terminal state

The entry stopped at the failed compile. Its success-only `stages` list is empty, which means **zero successful stages**, not zero compiler invocations. `between_child_preservation_passed` is true and the batch records `preservation_failed=false`. Exact canonical input and initial excluded-metadata journals remain alongside the stage receipt, source snapshot, logs, samples, lease, production claim and batch results. [Runtime bindings](runtime-bindings.json) hash all ten runtime/claim files.

Because the batch failed, `Context.finish` did not run. There are no completed-batch final metadata, resolution, replay or audit exports. This evidence checkpoint exports the **existing** journals and diagnostics after termination; it does not fabricate successful end-of-batch artifacts. The [export summary](export-summary.json) gives readable ordered chunks: 101 canonical input chunks, 87 initial metadata chunks, two receipt chunks, and one chunk each for compiler log, samples and controller log. Concatenate each manifest's listed part bytes without added separators.

The signature supplement remains **newly observed local evidence**, with no historical-preservation or authenticated-dependency-provenance claim. Under-lease checks bound those signatures and the old inputs; the import failure does not retroactively strengthen their provenance.

[Execution reconciliation](execution-reconciliation.json) verifies the source/log bindings, one entry/callback, limit readbacks, reaping, waitid/wait4 status agreement and clean release. The child was reaped, all descendants were gone, and kernel ECHILD was confirmed. Terminal inspection found **no active Lean/Lake/checker/extractor/tracer process** and the same common lock inode **free**. The released lock file, production claim and empty work directories remain in place; none was removed or reset for a retry. The [work-root listing](work-root-listing.json) records no generated files.

[Prior evidence preservation](prior-evidence-preservation.json) reverified all 60 activation, 917 inventory and 85 earlier failure-evidence entries unchanged. The master manifest covers this report, the invoker, all outer evidence and exports; `runtime-bindings.json` covers the additional runtime files in the reviewed wrapper directory. No reviewed helper/data file or historical manifest was rewritten.

This additive failure evidence is published on `light-eft-spanners-checkpoints` with `[skip ci]`. The sole worker stops for independent result review. There is no acceptance, source promotion, new mathematical conclusion or whole-paper completion claim.
