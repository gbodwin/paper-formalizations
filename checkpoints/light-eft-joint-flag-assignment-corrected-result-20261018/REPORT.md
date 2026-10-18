# Corrected joint-flag attempt — compile failed, later stages skipped

The **one approved attempt stopped at compile with exit 1**. Exact singleton resolution, singleton kernel replay and focused audit were **not run**. There was no retry, source correction, option change or new object. The joint-law theorem remains unaccepted; this checkpoint preserves the actual failed attempt for independent result review.

Tested source: **`7a4ab29cebfdd86808d4d6708411967fdb4a3bd4`**. Adapter: **`154e108179324f74f163049f2fe450be5522d616`**. Reviewed preparation evidence: **`84b22163e171e8146cff0af75cb8209811a18ade`**. Target: `LightEFTJointFlagSamplingStage.JointAssignmentLaw`. The 11,752-byte submitted source remains SHA256 **`ada2dee81f9596a616789458eaebda43745ced3c21bc4ffd6f97367584870579`**. [Source/toolchain/object bindings](source-toolchain-object-hashes.json) record exact hashes; the new object is null.

## Raw diagnostics and classification

The [complete 6,730-byte compiler log](../light-eft-joint-flag-assignment-corrected-draft-20261018/future-validation-evidence/compile/raw.log) is unchanged, SHA256 **`46ba128bb1e2de58833b9528325539395b9f4c2ecfebaf4257c49d1bfe2cb167`**. [Machine-readable classification](diagnostic-classification.json) counts anchored source/line/column severity headers. Hints, suggested options, variable names within a header and allocator `max_warnings` text are not counted again.

There are **seven error diagnostics: one parser error and six unused-section-variable linter errors promoted under `-DwarningAsError=true`**. There are zero unpromoted warning headers and no other elaboration-error header. This does not establish acceptance of any repaired proof.

| Location in JointAssignmentLaw.lean | Classification | Raw message / variable payload |
|---|---|---|
| 113:0 | Promoted linter | `automatically included section variable(s) unused in theorem ...samplingSchedule_nodup`: `decidableEqJ` |
| 121:0 | Promoted linter | `automatically included section variable(s) unused in theorem ...mem_samplingSchedule`: `decidableEqJ` |
| 128:0 | Promoted linter | `automatically included section variable(s) unused in theorem ...samplingSchedule_length`: `decidableEqJ` |
| 157:0 | Promoted linter | `automatically included section variable(s) unused in theorem ...decodeHost_typed`: `fintypeJ`, `decidableEqJ` |
| 167:72 | Parser | `unexpected token 'include'; expected 'lemma'` |
| 169:0 | Promoted linter | `automatically included section variable(s) unused in theorem ...decodeAssignment_head`: `fintypeJ`, `decidableEqJ` |
| 175:0 | Promoted linter | `automatically included section variable(s) unused in theorem ...decodeAssignment_outside`: `fintypeJ`, `decidableEqJ` |

The raw log includes the full theorem names, payloads and notes. No linter was disabled and no source repair followed this failure. These are observed compiler/parser/linter blockers, not a mathematical counterexample.

## Executed command and skipped checks

[Commands](commands.json) preserve all four planned argv, complete environment, cwd and ordered source bindings. [Executed command record](executed-commands.txt) identifies the one invocation and static postprocessing. Only compile has a child/receipt. Its exact official pinned Lean **4.34.0** binary ran with **`-j1 -s65536 -M5120 -DautoImplicit=false -DwarningAsError=true`**, the reviewed `--root`, fresh `-o` and original corrected staged source path. No extra version/compiler/checker probe, broad Lake build, shim or dependency retrieval was used.

Compile UUID: **`2309c027a1c541f58bcea9ab9af8fdf3`**; child PID **16225**; supervisor PID **15915**. The [source-bound receipt](../light-eft-joint-flag-assignment-corrected-draft-20261018/future-validation-evidence/compile/receipt.json) records the exact source/adapter commits, `state=failed`, `exit=1`, UTC/monotonic timing, actual terminal status, matched waitid/wait4 ownership, direct/adopted child reaping and kernel no-children verification. Receipt creation/finalization UTC: 2026-10-18 19:07:51.576715 to 19:10:29.948155. Those times include protected pre/post checks; they are not the child runtime interval. The raw child/runtime timing remains in the receipt. The driver's empty successful-stage list reflects that it appends only successful stage returns; it does not mean compile never launched.

There is **no new `.olean`, resolution result, individual kernel replay, actual-owner root inventory, recursive closure or executed 16-root/eight-interface check**. No prior-module or synthetic audit count is substituted. [Work-tree evidence](work-tree.json) records zero files; [partial-artifact bindings](partial-artifact-bindings.json) are empty. All three later stage directories are absent.

## Resources, preservation and release

The unchanged compile **3 GiB** admission gate passed; later **3/4/4 GiB** gates were not exercised. Kernel limits read back as 12 GiB address space, 60 seconds CPU, 16 MiB file size, zero core size. The unchanged 90-second child wall deadline and lifecycle controls remain documented in the receipt. Pre-exec visible headroom was **7,406,022,656 bytes**. Disk admission/pre-exec free bytes were **3,936,301,056 / 3,936,231,424**, each above 2 GiB. Wait4 max RSS was **3,404,564 KiB**, sampled peak RSS **3,486,576,640 bytes**, sampled peak VM **6,498,820,096 bytes**. Sampled values are not continuous heap/VM caps. No resource control was weakened and no memory-stop/cleanup error was recorded.

All **77 dependencies** retain their exact source/object bindings. Planned scope remains **78 project imports, 16 required roots, eight interfaces**, including all generated/private actual-owner roots if an audit is later authorized. The post-child preservation check passed. All six preservation-only source/object bindings for the three accepted modules still match contents and filesystem identities, outside search roots. None was imported, recompiled, replayed, copied into a project cache or promoted. Previous accepted source/evidence, all earlier failure evidence, pins and local-signature/provenance qualifications remain unchanged. Review acceptance is recorded as source/log/hash reconciliation, not fresh re-execution of accepted proofs.

[Fresh coordination](fresh-post-planning-coordination.json) was issued only after read-only planning. The adapter authenticated the approved prior epoch **`9dd0d7e576bc4fb7b7fa05d4413d4bff`**, its 719-byte SHA256 **`06054c674a4566e9b344b7fd4c4c12f646c1c2a7a6b74b315538ef4d34e21aa1`**, and reused only device/inode **33:3258**, directory `[33,1]`, nonblockingly under the unchanged controls.

The new [released lease receipt](../light-eft-joint-flag-assignment-corrected-draft-20261018/future-validation-evidence/lease.json) has epoch **`837cbf167bbc4f50b2290477d88eb751`**, **719 bytes**, SHA256 **`6d3372280e561f5b8bfecfe63c8a70364e1e233c886c937a261a1d71922c7327`**. It records `state=released`, `kernel_echild=true` and no release error. The failed child interval is wholly inside this lease. Clean ownership release is not theorem acceptance, historical inode continuity or new execution authorization. The adapter's reviewed prior-release policy is unchanged. No additional common-lock acquisition occurred after release.

## Complete outcome exports and pause

[Available-export index](available-export-index.json) covers **all nine raw runtime files**: canonical inputs, initial excluded metadata, batch/result, lease, exact submitted source, compile log, receipt and samples. **Nine manifests / 209 ordered chunks** reconstruct each original exactly. Originals remain in the corrected draft's runtime evidence. [Driver-export index](driver-export-index.json) is empty because focused audit/final exports never ran. No omitted stage output was invented. The new object hash and all replay/audit results remain absent.

[Preservation script](preserve-outcome.py) and [raw postprocessing log](preserve-outcome-attempt-1.log) document static comparison/copy/classification/chunk reconstruction. All reconciliation checks passed; that statement concerns evidence preservation, not proof acceptance. [Execution summary](execution-summary.json) retains exact command/limits/resource/lifecycle results. [Final idle evidence](final-idle.json) and [process listing](final-idle-processes.txt) show no compiler/checker/extractor/tracer running.

Publish these additive actual-outcome files and the one production claim with `[skip ci]`, verify exact remote Git blobs and every export, then remain idle for independent result review. No retry, source correction/promotion, accepted-module compilation, broad rebuild, retrieval, SCC or website work occurred in this attempt. The joint-law theorem, charged sampling/serialization, seed approximation, packing, final runtime composition and provenance/whole-paper obligations remain unaccepted or open/qualified.
