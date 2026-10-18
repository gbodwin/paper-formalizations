# Light EFT audit-only adapter — preparation, not audit execution

**Status: prepared for independent read-only review. No audit, rebuild, replay, Lean/compiler/checker invocation, cache advice, or full initial/final preservation pass was run in this task.** The proposed 64 MiB launcher profile has been checked statically, not exercised with a child. Source, mathematics, dependency pins and websites are unchanged.

The user reports independent acceptance of `4bc6d398cee4e65c1550a585fff6778381262bdf`: all **485 ordinary chains** qualified, aggregate compilation separate, the frozen **486-source graph** covered, and all 206 receipts, 68 resolutions, 486 source/object bindings, preservation and 573 fetched text hashes reconciled. This records the reported independent review, not fresh execution. The accepted root has **486 objects and 414 resolution records**; [protected-bindings.json](protected-bindings.json) binds all 900 files to their accepted hashes and observed identities. All 900 were reconciled locally during preparation. That is local hash agreement, not dependency-cache authentication or a provenance upgrade.

## Exact future invocation and working directories

The unchanged source is `scripts/LightEFTFullAudit.lean`, SHA256 **`f4e44e8994c4d43c8bd38fb5f4c029adb52e87192baa73e554178c41b5bb43db`**. Its verbatim snapshot is [LightEFTFullAudit.lean.txt](LightEFTFullAudit.lean.txt). Its required-module array contains exactly the same **485 ordinary names** as the accepted source graph; no name or declaration filter was added. Mathematical source remains `78cb40c7837db049d645d73696f2e0b724ce8a3b`.

After independent review and a later explicit execution authorization, the adapter permits exactly one official Lean invocation:

```text
/workspace/toolchains/lean-4.34.0-linux/bin/lean -j1 -s65536 -M5120 -DautoImplicit=false -DwarningAsError=true /workspace/light-eft-verification/scripts/LightEFTFullAudit.lean
```

There is **no `-o`**, build command, resolver, checker, or aggregate-prefix replay. `PLAN.json` preserves the accepted isolated search environment: the exact retained 486-object root first, existing pinned dependency object roots, and the official toolchain library. The existing strict options, `MIMALLOC_ARENA_RESERVE=128MiB`, `MIMALLOC_VERBOSE=1` and source search environment are retained. All nine dependency revisions, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`, remain pinned.

Default adapter behavior is describe-only:

```text
python3 -B checkpoints/light-eft-audit-adapter-review-20261018/run_audit.py --describe
```

The later authorized execution entry point is `run_audit.py --execute-reviewed-audit <exact-reviewed-adapter-commit>`. That command was **not invoked**. Before claiming an attempt, it compares all published adapter files against the exact reviewed Git commit and rejects unreviewed Python membership. Its exclusive invocation-claim file prevents an automatic second attempt, including after an admission failure.

An authorized run creates a new `.lake/light-eft-full-audit-<uuid>` working directory and an empty `ci-evidence` subdirectory with recorded device/inode identities. Neither may preexist. Runtime evidence goes in a new adapter `executions/<uuid>` directory. No execution directory, claim, or actual audit output was created in preparation. The pinned source writes exactly:

| Relative to the fresh working directory | Purpose |
| --- | --- |
| `ci-evidence/actual-owner-inventory.tsv` | All actual-owner project declarations, including private/generated names |
| `ci-evidence/recursive-dependencies.tsv` | Recursive type/body dependency rows, with safety/kind metadata |
| `ci-evidence/import-closure-loaded.txt` | Modules actually loaded in the fresh environment |
| `ci-evidence/strict-violations.txt` | All strict root/recursive findings |

Combined raw stdout/stderr is the separate fresh `attempt/raw.log`; decision samples are `attempt/samples.jsonl`.

## Explicit resource profile

| Control | Proposed audit-only value |
| --- | --- |
| Per-file FSIZE, soft/hard | **64 MiB** |
| Four source files plus raw output | **at most 320 MiB**, source-directed |
| Separate decision-log bound | **16 MiB**, unchanged |
| Fresh visible admission and pre-exec | **4 GiB** |
| Host admission and pre-exec | **3 GiB** |
| Fresh free disk at admission and pre-exec | **strictly greater than 2 GiB** |
| AS, soft/hard | **12 GiB**, unchanged |
| CPU, soft/hard | **60 seconds**, unchanged |
| Wall | **90 seconds**, unchanged |
| Core | **0**, unchanged |
| Runtime visible/host floor | **1 GiB**, unchanged |
| Observed shared-mm RSS stop | **6 GiB**, unchanged |
| Per-cgroup anonymous-growth stop | **3 GiB**, unchanged; never summed over ancestors |
| Decision sampling | **100 ms**, unchanged |

The FSIZE difference is needed because the historical dependency export was **41,067,675 bytes**, exceeding 16 MiB. Four fixed source writes plus raw output, each bounded by 64 MiB, give the 320 MiB source-directed budget. Runtime checks also reject unexpected files/directories, symlinks, linked outputs, directory identity changes and oversize output files. This is **not a filesystem quota**. Publication copies, chunks, inventories and supervisor metadata are outside that source-directed total. The decision log remains separately bounded at 16 MiB.

Only the numeric FSIZE value changes in `pilot_child.py`; unchanged handshake and `prlimit` readback verify it along with AS/CPU/core. `child_runner.py` adds output-budget collection and fresh pre-exec disk checks using the existing fail-stop/error path, plus audit-specific receipt metadata. No ownership, termination, wait4 matching, cleanup barrier, memory gate, deadline or decision-log rule was loosened. [supervisor-adapter.patch](supervisor-adapter.patch) is the complete diff from the accepted production copies for these changes and bootstrap evidence-path routing. [lifecycle-static-comparison.json](lifecycle-static-comparison.json) records unchanged lifecycle function ASTs and unchanged run/cleanup code after the initial metadata assignment and added output guard.

Approved `exit_transition.py` and `decision_telemetry.py` remain byte-identical, hashes **`1135140dd7dd3d075953d5d621f727a7a7c13796985c27da0c5afba68f95e76a`** and **`08ae50f987ba67655e21d504e561ff5a23eda79104f35fe4c0d48e6e59de87fe`**. The existing exclusive lease, shared Linux lifecycle module, accounting collector, narrow fresh-memory classification, fixed non-resetting grace, owned terminal confirmation, matching wait4 and kernel-ECHILD release barrier are retained. [unchanged-controls.json](unchanged-controls.json) lists the unchanged files.

## Future preservation and finite advice

One continuous exclusive lease, device **33**, inode **3849**, will cover idle verification, approved bootstrap, the initial full preservation pass, the single child, mandatory final full preservation and copying existing diagnostic outputs. Failure is sticky; no second Lean invocation is possible. Failed/partial output and raw diagnostics remain preserved. Release requires kernel ECHILD.

The accepted 82,856-row inventory, SHA256 `0c7e38ad5b0db85c1bc9b32b958dd036639e920ff6cfbfd1f6db9445dddea460`, supplies existing source/tool/dependency bindings and advice eligibility. The future inventory additionally protects all final **486 objects / 414 resolutions**, the unchanged audit source and the reviewed adapter files. Accepted source/tool/lifecycle pins are compared before reuse; current hashes cannot silently replace an existing pin. The final pass must visit and match the entire initial set; retained-root membership, dependency/source membership and all 900 object/resolution identities/hashes are checked separately. The accepted project-source preservation set has 490 files, while the imported audit graph has the stated 486 nodes; unchanged extra source files do not expand the loaded audit graph.

No advice was executed in preparation. The proposal reuses the unchanged bootstrap and finite scopes from accepted inventory bindings: 66,961 dependency/tool files, 7,129 preserved evidence files, the 2,905-file finalized-data subset, and once the already recorded 3,809 archives plus 708 finalized-data extension files. [finite-advice-profile.json](finite-advice-profile.json) records counts and byte totals. No new path is eligible; no audit output or adapter file is added to an advice scope. Actual fresh capacity, not nominal advised bytes or fixture results, gates the future child. There is no historical 4.375 GiB exception and no automatic recovery expansion.

## Fresh acceptance and reconciliation contract

[audit_contract.py](audit_contract.py) requires all of the following; no single summary line or historical count suffices:

- One fresh source-bound audit attempt from the exact reviewed adapter, exact official command/environment, fresh working/evidence nonce, and verified pre-exec authorization.
- A new zero-exit receipt, actual owned child PID, terminal confirmation, waitid/wait4 status match, all children reaped, matching inherited lock/limit readbacks and continuous lease release after kernel ECHILD.
- Actual 4 GiB visible and 3 GiB host admission/pre-exec, the 64 MiB FSIZE profile, unchanged limits, complete raw/decision-log bindings and the separate 16 MiB sample limit.
- Fresh complete four-file outputs, stable identity/size/hash bindings, exact allowed working-directory membership and the 320 MiB source-directed budget.
- Complete matching initial/final preservation. Reconciliation streams the canonical inventory and requires all 900 accepted object/resolution bindings and the pinned audit source to be present and identical.
- All **485 ordinary modules** and the aggregate actually loaded, with no unexpected project module outside the frozen graph. Every actual-owner root must be exported and consistent in the closure, including declarations whose names are private/generated or outside a public project namespace.
- Exact root-to-recursive-closure reachability through exported type and body references. Inductive families, constructors and recursor-rule references must be covered. The pinned Lean source traverses imported opaque values using `setExporting false`; it does not rely on cached `collectAxioms` results.
- No unsafe or partial declaration, no project axiom, no unresolved/ambiguous dependency reference, no omitted project-owned closure row, no unreachable extra closure row, no malformed/truncated/duplicate row, and no strict finding. The only permitted recursive axioms are **`propext`, `Classical.choice`, `Quot.sound`**.
- Fresh printed root/covered/visited/opaque counts and axiom names must agree exactly with the complete exports. **8950 roots, 60369 visited constants and 48 opaque bodies are comparisons only**; they are never acceptance constants.
- Copies of all four outputs must match the originals. Ordered byte-row-aligned chunks of the four outputs and raw output must reconstruct exactly, with per-part and whole-file hashes. There is no duplicated header or inserted separator. Target chunk size is 200,000 bytes; a larger single row is preserved intact and explicitly labeled. Chunk creation/reconstruction failure prevents acceptance. Diagnostic chunks may also be exported after rejection, with acceptance false.

The source's existing informational line still says `DIAGNOSTIC ONLY`; that label is not changed or treated as a pass. Audit acceptance requires the fresh execution, preservation, semantic checks and publication reconstruction together. Initial/final preservation failure, admission failure, runtime guard failure, nonzero exit, missing output, or semantic/chunk failure leaves the run rejected with diagnostics retained.

## Preparation checks and review boundary

The final preparation command was:

```text
python3 -B -u checkpoints/light-eft-audit-adapter-review-20261018/test_preparation.py
```

**35 tests passed** with exit zero. They use synthetic plain files/TSVs and Python static/AST checks, not historical audit acceptance data or real Lean children. They cover private/opaque and recursor closure, required module loading, missing/duplicate roots, generated-root omission, unsafe/partial declarations, project/disallowed axioms, dangling type/body links, missing recursor coverage, unreachable rows, historical-count mismatch, findings, truncation, default describe-only behavior, nonfresh/nonzero/unreaped receipt rejection, four-output/raw completeness, size/link/staleness checks, strict disk boundary, row-aligned reconstruction and approved profile constants. The raw logs from all four preparation invocations remain preserved; the final log is [preparation-tests-invocation-04.log](preparation-tests-invocation-04.log). There were no failed tests. [preparation-checks.json](preparation-checks.json) records commands, final source hash, unchanged bindings and the explicit zero Lean/audit/advice counts.

The preparation metadata is not a fresh audit result and does not prove runtime capacity under the 64 MiB profile. One terminal-metadata probe initially had an extra closing parenthesis and failed to parse before any Python statement ran. Its exact saved source and diagnostic remain in `terminal-probe-failed-01.py.txt` and `terminal-probe-failed-01.log`; the corrected probe succeeded. This was a metadata-helper syntax error, not a failed test, Lean invocation or audit attempt. [implementation-bindings.json](implementation-bindings.json) binds proposed Python files; [PLAN.json](PLAN.json) gives the exact future command, fixed module set, profile and acceptance scope. No actual audit output or result is present.

The adapter is published additively with `[skip ci]`, then paused for independent read-only review. No compiler/checker is active and the common lock is free. **Dependency-cache authentication and clean validation remain separate and unresolved. Local hash agreement and a future incremental audit do not upgrade provenance or constitute whole-paper acceptance.**
