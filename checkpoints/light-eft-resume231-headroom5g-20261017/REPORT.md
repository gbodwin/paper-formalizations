# Finite archive/data pass completed; first 5 GiB admission refused before Lean

The one authorized finite hash-then-advice pass completed, but **BernoulliFlagEncoding compilation was refused before any Lean child spawned**. Actual visible headroom was **4,955,549,696 bytes**, below the required **5,368,709,120 bytes (5 GiB)** by **413,159,424 bytes**. The pre-exec gate was configured but never reached. No further advice, retry, extraction, scope expansion or cap change followed.

The exact new extension was **Scope A: 3,809 files / 818,684,031 bytes**, **Scope B: 708 files / 385,582,329 bytes**, combined **4,517 files / 1,204,266,360 bytes**. Every new target passed its recorded hash, same-file identity, regular/nonexecutable/no-symlink checks and same-descriptor advice. No nominal byte total was credited as reclaimed capacity. The actual combined pass still did not provide the required 5 GiB.

Actual batch outcome: **one failed admission receipt, zero executed Lean/compiler/checker children, zero newly completed chains and 230 later stages skipped**. All **94 accepted objects and 23 existing resolution records remain unchanged**. Final full preservation matched **79,881 input bindings**, with no changes, before the common lock was released. This is a capacity blocker under the approved finite scope, not a proof diagnostic or paper-level result.

## Connection, review and immutable plan

Execution access was verified usable at **2026-10-17T20:38:06.633672 UTC**, after the reported idle disconnect at **20:31:36 UTC**. There was no compiler/checker/tracer and the original universal lock (device 33, inode 3849) was free. The previously stopped attempt was not restarted; this is the separately authorized finite extension and new 231-stage plan.

Frozen proof source: `78cb40c7837db049d645d73696f2e0b724ce8a3b`.
Base evidence: `8c4b132ca21293bda1c11b6dca8f84eb669dc878`.
Branch: `light-eft-spanners-checkpoints`; additive publication commits use `[skip ci]`.

The user reports independent acceptance of the 23 preceding new chains at the base evidence commit, totaling 94 qualified chains. BernoulliFlagEncoding produced no object in the prior resource-floor stop; that failed attempt remains unchanged. This records prior source/log/hash review, not repeated execution or a stronger provenance claim.

`PLAN.json` fixes exactly **graph entries 95–171**, from `LightEFTSpanners.BernoulliFlagEncoding` through `LightEFTSpanners.StoredPreparedCandidateOriginal`: **77 compile/resolve/replay chains, 231 stages**. All source/Git bindings and import closure were checked before execution. Binding checks do not constitute execution acceptance of skipped sources. The 486-row frozen graph SHA256 remains `262e8af8f758f8d7224e8b1e7a87b4b4e8c47aab31098df3fd253af7cdbcf24c`.

The exact existing root was retained:
`/workspace/light-eft-verification/.lake/light-eft-batch100-entries72-171-20261017-ee496fe7834c4e86994b3933112caff7`.


`retained-root-binding.json` records the 94 accepted objects, 23 resolution files and expected directories. Object/resolution content, identities, exact membership and absence of symlinks were checked; no accepted stage was rerun. No new object, resolution, partial output or unexpected root file was created. `source-toolchain-object-hashes.json` preserves the exact object/tool/source bindings; `module-status.json` marks the refused first compile and all skipped phases.

## Exact finite scopes at the accepted commit

Both new scopes use only recorded bindings anchored at base commit `8c4b132ca21293bda1c11b6dca8f84eb669dc878`. Authority files and their exact hashes are in the plan. The selector reads those explicit inventories/manifests, never performs a broader archive/data inventory hunt, and rejects duplicate/noncanonical paths, symlinks, nonregular/executable targets, changed sizes or changed hashes/identities.

**Scope A** is exactly the 3,808 recorded `/workspace/cache/mathlib/*.ltar` files in `checkpoints/light-eft-provenance-inspection-20261017/evidence/candidate-archive-inventory.json` and `/workspace/toolchains/lean.tar.zst` from `toolchain-archive-identity.json`: **3,809 files / 818,684,031 bytes**. The candidate records remain local candidates not authenticated for installation. These archives were read as raw bytes and advised only. No extraction, decompression, leantar invocation, installation, fresh HTTPS authentication or stronger provenance claim occurred.

**Scope B** is exactly the user-authorized finalized-data subset:

| Checkpoint | Files | Bytes |
| --- | ---: | ---: |
| light-eft-batch20-20261017 | 12 | 28,792,228 |
| light-eft-batch20-wholeprocess-20261017 | 27 | 35,715,061 |
| light-eft-batch100-entries72-171-20261017 | 14 | 29,190,727 |
| light-eft-resume298-retained-root-20261017 | 211 | 94,057,832 |
| light-eft-finitelaw-finite-recovery-20261017 | 444 | 197,826,481 |
| **Total** | **708** | **385,582,329** |

For the first four checkpoints, only `attempts/*/{receipt.json,samples.jsonl,raw.log}` and the seven finalized top-level data names are included. The names are `inputs.jsonl`, `output-records.jsonl`, `cache-advice.jsonl`, `result-reconciliation.json`, `module-status.json`, `source-toolchain-object-hashes.json`, `publication-checks.json`. For finite-recovery, selection includes those top-level names where present, the seven explicitly authorized `evidence/replay/` files, and only the hash-advice/inputs reconstruction parts. It excludes submitted code, object payloads, unrelated chunk sets and sample reconstruction chunks. Metadata names containing object/source hashes refer to JSON data only, not the referenced binaries or code.

The two new scopes total **4,517 distinct files / 1,204,266,360 bytes**, exactly the absolute ceiling. `expanded-scope-selection.json` keeps their metadata alongside the separately authorized old 623-file scope; that old scope is not counted as part of the new 4,517-file authorization.

## Integrated preservation and exactly one new-scope pass

The existing full-initial preservation hashes all inputs, including A/B, and fixes file identities. New A/B targets are not advised during that initial full pass. After it completes, `one_time_extension.py` performs exactly **one** finite same-descriptor hash-then-advice pass before the first actual compile admission. It opens each new target without following symlinks, checks regular/nonexecutable type and frozen identity, streams its recorded content hash, checks size and identity again, issues POSIX_FADV_DONTNEED on that same descriptor, and rechecks file and pathname identity. No extraction or content write is performed.

The new pass is integrated with ordinary advice of the previously reviewed scopes. Thus its overall eligible set includes the old 66,961 dependency/tool paths, 7,129 historical data paths, and 623 finalized data paths, plus the new A/B set. The old scopes are unchanged. **The new A/B set is not repeated in later ordinary advice**; the override explicitly skips both new categories after this one pass. In this actual run there was no later advice at all.

`one-time-extension-verified.jsonl` records exactly 4,517 verified new bindings, matching the canonical inventory and accepted authority hashes. `extension-pass-claimed.json` prevents a duplicate pass. `one-time-cache-advice.json` and the sole `cache-advice.jsonl` entry preserve the full raw before/after accounting, counts by scope, identities/digest and measured capacity. The previously approved old 623-file initial same-FD handling remains separately recorded in `expanded-scope-initial.json`; it is not a second new A/B pass.

The pass's nominal combined legacy-and-new set is **79,230 files / 13,229,175,341 bytes**. That is a binding footprint, never a reclaimed-byte promise. The measured overall visible capacity was:

| Reading | Visible headroom bytes |
| --- | ---: |
| Before combined finite pass | 14,532,608 |
| After combined finite pass | 4,955,549,696 |
| Fresh first-compile admission | 4,955,549,696 |
| Required first-compile gate | 5,368,709,120 |
| Remaining shortfall | 413,159,424 |

The counter difference is for the combined pass and is not attributed solely to the newly authorized files. Host MemAvailable at refusal was **17,715,765,248 bytes**, which does not replace the visible requirement. No extra pass was made to chase a margin after the refusal.

## First admission and untouched runtime controls

Failed receipt UUID **`1491287432294cc29c429f7a58fedd2f`**, interval **20:45:56.078603–20:46:06.320385 UTC**, stage `LightEFTSpanners.BernoulliFlagEncoding compile`. The recorded failure is `MemoryGuardError('Visible headroom below required floor')`; in this attempt that generic error refers to the **5 GiB admission gate**, not the 1 GiB running floor.

The actual decision was made before process creation. There is **no child PID, exit status, launcher handshake, pre-exec readback, raw compiler log or runtime sample file**. The 5 GiB pre-exec gate is configured in the source but was never reached. No Lean warning/error classification or kernel result exists for this attempt. The planned argv/environment are preserved as planned data, not described as executed commands. The full admission accounting and invocation traceback remain in the failed receipt and `invocation.log`.

The reviewed supervisor, lifecycle/effective-reread handling, launcher and all runtime guards remain byte-identical. The new code is confined to the authorized scope integration, retained-root plan and first visible gate. No lifecycle fixture, tracing pilot or accepted-stage rerun occurred.

Configured limits remain AS **12 GiB**, sampled RSS stop **6 GiB**, per-visible-group anonymous-growth stop **3 GiB**, running visible/host floor **1 GiB**, CPU 60 seconds, wall 90 seconds, file size 16 MiB and core zero. Ordinary subsequent compiler/resolver admission remains 3 GiB visible and checker admission 4 GiB visible, with host admission 3 GiB. Only first BernoulliFlagEncoding compilation requires 5 GiB visible at admission/pre-exec. No runtime limit or ordinary subsequent gate changed. No child was launched to exercise those limits in this attempt.

Toolchain remains official Lean **4.34.0**. Hashes remain:

- lean: `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
- leanchecker: `ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe`.
- Resolution script: `9f2a3d83e0b90d75a7e0ddc3693f09e27d50040bc8fc65a2b5b9df4eb1797caf`.

Mathlib remains `5ed2965256430c3649e86755f9576b54eca72435`; all nine pinned revisions and clean tracked sources were checked. No proof source, dependency pin, runtime shim, network/security setting or website changed.

## Continuous exclusion, full final preservation and evidence

Supervisor PID `190462` held the original universal lock (device 33, inode 3849, FD 3) from **2026-10-17T20:45:16.992013+00:00** through **2026-10-17T20:46:36.108083+00:00**. No compiler/checker/tracer conflict occurred. The refused stage and final release both verified kernel ECHILD; there was no tool child to reap.

Full initial preservation completed at **2026-10-17T20:45:51.911557+00:00**. Full final preservation completed at **2026-10-17T20:46:32.331976+00:00**, matching all **79,881** paths with no changes. The batch ended at **2026-10-17T20:46:36.108222+00:00**.

The sole canonical `inputs.jsonl` is **29,088,831 bytes**, SHA256 **`84ceb002c3459834922465d47822e55348bf6a34cc2b114ca3baccc6bb0b8aaf`**. There was one full initial and one full final input-content pass, plus the separately authorized finite subset hash/advice pass. Post-stop reconciliation reads the inventory file and small source/control/object/authority bindings; it does not hash all archive/data bodies again or perform another full input-content pass. No full inventory is duplicated per child.

Terminal readings in `terminal-environment.json`: disk free **7,681,089,536 bytes**, host MemAvailable **17509416 kB**, visible cgroup current **16990347264** against limit **17179869184**. No compiler/checker/tracer is active and the common lock is free. Terminal cache reflects the required final hash pass and is not used as a substitute for the failed admission decision.

`verify_publication.py` is an offline post-stop helper. It checks exact A/B selection and ceilings, accepted authority bytes, the single finite pass and verified binding log, canonical/final preservation, first admission refusal before spawn, unchanged root objects/resolutions, source/control hashes and free terminal state. `reconciliation.log` saves its initial result. No extraction, further advice, retry, fixture or Lean invocation occurred after the refusal.

`PUBLICATION.json` binds the result commit; the following publication commit binds it and `evidence-sha256.json`. Reports, receipts, raw accounting/traceback, source/control snapshots, binding logs and 94 object payloads are covered by that manifest, except the manifest itself and bytecode caches. The archive payloads and old finalized evidence are referenced, not copied into this publication. Raw whitespace diagnostics and exact preserved-data exclusions are recorded in `publication-checks.json`.

## Remaining qualifications and stop state

The current blocker is actual visible capacity under the approved finite pass: it did not provide the required 5 GiB. No new module or chain completed. The 94 prior accepted chains, all prior partials and the earlier resource-floor failure remain preserved. New scope integration and this refusal await independent review.

Archive hashing/advice establishes only agreement with the recorded local bytes. It does not authenticate the dependency-cache archives for installation, compare installed extractor members, or strengthen the historical provenance claim. Accounting remains `PARTIAL_VISIBLE_ANCESTORS; unseen limits UNKNOWN`. Exhaustive owner/axiom audit, coordinated full-clean/CI validation and paper-level review remain outstanding. Mathematical hypotheses are unchanged; no whole-paper completion/acceptance is claimed.

Paused after publishing this actual outcome with CI skipped, no compiler/checker process and the original common lock free.
