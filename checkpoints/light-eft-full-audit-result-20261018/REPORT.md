# Fresh bounded Light EFT audit — passed, pending independent result review

The single authorized audit completed successfully using the unchanged reviewed adapter at **`a13f2738bd4e9f3a2e6de291c2f40e636fec3406`**. It exited zero, passed the fresh execution/output contract, matched its full initial/final preservation pair and reconstructed all publication chunks. **No rebuild, ordinary replay, second audit attempt, automatic retry, cache-scope expansion or CI run occurred.** Mathematical source remains **`78cb40c7837db049d645d73696f2e0b724ce8a3b`**. No source, mathematics, pin, website or reviewed adapter file was changed.

This is a fresh incremental actual-owner/type/body audit of the retained objects. Independent result review is pending. Dependency authentication, full clean/provenance validation, exact CI, semantic/mathematical-hypothesis review and whole-paper acceptance remain separate. Local hash agreement and this audit do not upgrade provenance.

## Actual execution

Approved adapter source is `31cbb7b7e9bacb0cadc266a2d77d8c420a223c3c`, sealed by the reviewed publication commit above. All **37 published files**, including the 36-entry manifest and publication metadata, were compared to that exact commit before invocation and remained unchanged afterward. The user reports acceptance of all 485 ordinary chains; aggregate compilation remains separate. The preparation's 35 static/synthetic tests were not treated as capacity evidence and were not rerun.

The sole controller invocation, with stdout/stderr preserved in [invocation.log](invocation.log), was:

```text
python3 -B -u checkpoints/light-eft-audit-adapter-review-20261018/run_audit.py --execute-reviewed-audit a13f2738bd4e9f3a2e6de291c2f40e636fec3406
```

The one official Lean argv was:

```text
/workspace/toolchains/lean-4.34.0-linux/bin/lean -j1 -s65536 -M5120 -DautoImplicit=false -DwarningAsError=true /workspace/light-eft-verification/scripts/LightEFTFullAudit.lean
```

The unchanged submitted audit source has SHA256 **`f4e44e8994c4d43c8bd38fb5f4c029adb52e87192baa73e554178c41b5bb43db`**. Official Lean 4.34.0, the exact retained 486-object search root, all nine pinned dependencies and the accepted allocator/search environment were reused. There was no `-o`, checker invocation, prefix replay, runtime shim, dependency rebuild or source edit.

Run UUID: **`cece4176767e4d6cba0bcef97e5da486`**. Attempt UUID: **`32f3492771964df0a090166882f06143`**. Supervisor PID **295632**; sole child PID **295782**. The fresh working directory is `.lake/light-eft-full-audit-cece4176767e4d6cba0bcef97e5da486`, with a new `ci-evidence` directory and no preexisting outputs. The exclusive invocation claim remains preserved, preventing an automatic retry.

Primary raw execution evidence is under [the execution directory](../light-eft-audit-adapter-review-20261018/executions/cece4176767e4d6cba0bcef97e5da486/). Entry points are [receipt.json](../light-eft-audit-adapter-review-20261018/executions/cece4176767e4d6cba0bcef97e5da486/attempt/receipt.json), [raw.log](../light-eft-audit-adapter-review-20261018/executions/cece4176767e4d6cba0bcef97e5da486/attempt/raw.log), and [audit-reconciliation.json](../light-eft-audit-adapter-review-20261018/executions/cece4176767e4d6cba0bcef97e5da486/audit-reconciliation.json). They retain exact environment, source snapshot/hash, limit and inherited-lock handshake/readback, PID/start identity, every runtime decision, actual owned terminal confirmation and matching wait4 reaping. Controller exit was **0**; there was no refusal, failed new audit stage or hidden retry.

## Fresh audit result

| Check | Actual result |
| --- | ---: |
| Required ordinary modules actually loaded | **485** |
| Aggregate actually loaded | yes |
| Total loaded modules | **5,849** |
| Complete actual-owner project roots | **8,950** |
| Ordinary-module-owned roots | **8,950** |
| Recursively visited constants | **60,369** |
| Opaque bodies traversed | **48** |
| Unsafe/partial declarations or project axioms | **0** |
| Strict findings | **0** |
| Actual Lean warning/error headers | **0 / 0** |

The only recursive axioms are exactly **`propext`, `Classical.choice`, `Quot.sound`**. This is not described as axiom-free.

The audit enumerated roots by actual owning module rather than public declaration-name prefixes, including private/generated declarations. It traversed types and definition/theorem/opaque bodies, inductive families, constructors and recursor rule right-hand sides. The reviewed reconciler independently checked exported root/closure consistency, all required module names, complete recursive reachability, duplicate/malformed/unresolved rows, safety flags, project/disallowed axioms, empty strict findings and agreement of the fresh printed counts with the complete outputs. A diagnostic line alone was not accepted as proof of success.

The fresh counts and the recursive TSV hash happen to equal the historical comparison. They were **not acceptance substitutes**: acceptance required the new owned zero-exit receipt, fresh directory/outputs, source-bound invocation, complete preservation and all semantic/chunk conditions.

## Actual output budget and row-aligned publication

| Output | Bytes | Publication chunks |
| --- | ---: | ---: |
| `actual-owner-inventory.tsv` | **1,065,840** | **6** |
| `recursive-dependencies.tsv` | **41,067,675** | **207** |
| `import-closure-loaded.txt` | **198,035** | **1** |
| `strict-violations.txt` | **1** (newline only) | **1** |
| Combined raw stdout/stderr | **3,410** | **1** |
| Total source-directed output | **42,334,961** | **216** |

The source-directed total is below **335,544,320 bytes (320 MiB)**, and every file is below the **67,108,864-byte (64 MiB)** per-file cap. In particular, the actual 41,067,675-byte dependency export exceeds the old 16 MiB profile and fits the explicitly approved audit-only cap. No quota or capacity expansion was silently substituted.

The complete recursive export SHA256 is **`47469d94d75ebb388bad2e9e62f07fd3d58d4e8c5a81af35d8a9c78281cb7bf0`**. Hashes for all five outputs and the chunk counts are in [actual-result.json](actual-result.json). The [publication export index](../light-eft-audit-adapter-review-20261018/executions/cece4176767e4d6cba0bcef97e5da486/audit-export-manifest.json) links each ordered part manifest. All **216 chunks** were checked for per-part lengths/hashes and exact full-file reconstruction. Concatenate bytes in manifest order without extra headers or separators; the original header appears only in the original first-part bytes. Source-output copies match the fresh originals. Raw original files, copies and chunks are all retained.

The separate decision log is **3,398,146 bytes**, below its unchanged **16 MiB** bound. It is not charged to the source-directed five-file budget. Publication copies/chunks and supervisor metadata likewise are not represented as a filesystem quota.

## Actual capacity, limits and ownership

Admission used real accounting, not preparation fixtures. Before the approved bootstrap, visible headroom was **274,161,664 bytes**; the unchanged finite advice produced an observed **4,901,568,512 bytes** afterward. The adapter then completed its initial preservation and approved one-time finite extension before the actual audit admission. No advice scope was expanded and no automatic recovery retry was used.

| Gate | Required | Actual |
| --- | ---: | ---: |
| Visible admission | 4,294,967,296 | **4,780,478,464** |
| Visible pre-exec | 4,294,967,296 | **4,779,130,880** |
| Host admission | 3,221,225,472 | **17,693,585,408** |
| Host pre-exec | 3,221,225,472 | **17,692,794,880** |

Values are bytes. Fresh disk guards requiring **strictly greater than 2 GiB** passed both admission and pre-exec. The reviewed adapter does not separately log the exact disk byte values at those two checks; [preflight.json](preflight.json) and terminal evidence preserve their own timestamped observations, not invented admission measurements.

Before Lean was authorized, the launcher handshake and kernel readback confirmed **AS 12 GiB**, **CPU 60 s**, **FSIZE 64 MiB**, and **core zero**, all soft/hard. Wall deadline remained **90 s**. The inherited common-lock device/inode and PID/PPID/session/process-group/start identities matched. Runtime floors/stops were unchanged: visible/host 1 GiB, observed RSS 6 GiB, per-cgroup anonymous-growth 3 GiB, and 100 ms sampling. Ancestor growth and thread RSS were never summed.

Across **149 runtime decision samples**, minimum visible headroom was **1,245,958,144 bytes** and minimum host MemAvailable **17,150,091,264 bytes**. Peak sampled RSS was **3,729,117,184 bytes**; wait4 maximum RSS was **3,641,480 KiB**. These are intermittent observations, not a continuous hard RSS cap; Lean `-M` is not a kernel heap cap, and visible accounting retains its partial-ancestor qualification. Detailed actual values are in [actual-result.json](actual-result.json).

One continuous common lease, device **33**, inode **3849**, covered bootstrap, initial preservation, the single child, mandatory final preservation and diagnostic copying. Kernel ECHILD was verified before release. Acceptance parsing and chunk generation then ran without another Lean process, as specified by the reviewed adapter. The child exited **0** with an owned terminal waitid result matching the owned wait4 result; all children were reaped. Complete UTC/monotonic timings are in the [lease record](../light-eft-audit-adapter-review-20261018/executions/cece4176767e4d6cba0bcef97e5da486/batch-lock.json) and receipt.

## Preservation and publication boundary

There was exactly **one initial/final full preservation pair** covering **83,032 bindings**. The canonical inventory is **30,357,324 bytes**, SHA256 **`cbd1cf79ad3f136c92585821f317cd1c98a1c1d001fa7468943df652fbceaf4e`**. Initial preservation completed at **2026-10-18T04:08:26.643455Z**; final preservation completed at **04:09:18.210688Z**, attempted every path and matched the identical stream hash with no changes. All retained **486 objects and 414 resolutions** were covered and remained identical in content and identity. No project object was generated or overwritten.

Post-execution checks are offline hash/metadata reconciliation, not a second audit or full frozen-input pass. They verified all **1,639 prior production manifest entries**, all **36 reviewed preparation entries**, all **900 retained bindings**, and the exact **37 reviewed files**. Previous rejected replays, failed fixture/metadata attempts, source snapshots and raw diagnostics remain preserved. Only the new invocation claim, fresh execution evidence and this result checkpoint are added; the reviewed adapter and old preparation status/report remain immutable historical evidence.

The execution manifest seals the complete fresh evidence tree. This checkpoint's manifest seals the readable report, actual summary, command/preflight/terminal records and a hash-bound link to that execution manifest. Both are published additively with `[skip ci]` and exact remote verification. No compiler/checker is running and the common lock is free. The worker pauses for independent result review.

**Dependency-cache authentication, clean validation, exact CI, website/math changes and whole-paper acceptance were not performed and remain separate.**
