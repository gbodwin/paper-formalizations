# Light EFT IR-signature inventory correction

This is a preparation-only correction following the pre-execution failure at `c1f0f12f1f781c3d087d42b3e0b90208fa0d4220`. The exact implementation exercised by the complete plan check is **`ea6cfc563e16fef2b20cef82a46c3faea909a843`**. It is additive on `light-eft-spanners-checkpoints`; no mathematical source, pin, resource limit, retrieval setting, or prior evidence was changed. This checkpoint awaits independent review and supplies no production execution authority or theorem acceptance.

## Correction and qualifications

The pinned local Lean 4.34.0 source reads an existing `.ir.sig` with `CompactedRegion.read` before the associated `.ir`. The module-format writer emits both when IR writing is enabled; the legacy/nonmodule writer has a different branch. Thus `.ir.sig` is a loadable semantic input, not disposable Lake hash metadata. [Local source evidence](loader-writer-evidence.json) and [numbered snippets](loader-writer-snippets.txt) identify the exact file/hash/lines. That source file was **not** in the prior canonical inventory. This observation does not authenticate a toolchain distribution or establish new binary provenance.

The separate [signature supplement](signature-supplement-summary.json) binds **11,426** newly observed local `.ir.sig` files, totaling **2,010,976 payload bytes**, to exact SHA256, bytes and `[device,inode,size,mtime_ns,ctime_ns]`, module name, and the old `.olean`/`.ir` family hashes. Its JSONL is 9,896,073 bytes, SHA256 **`887fbf98a695a0b5992aa172cd098fc237bd6572d2a52491531c769bc73da964`**. It is explicitly `NEWLY_OBSERVED_LOCAL`: earlier receipts did not bind these signatures and therefore do not prove their historical preservation or authenticated dependency provenance. The real plan verified these newly observed bindings again; it does not repair that historical gap retroactively.

`semantic_inventory.py` retains every old binding as authoritative, including old native inputs or any old input whose name resembles excluded metadata. It adds the signature supplement and rejects missing, changed, replaced, duplicate or newly appearing signatures. Only exact previously diagnosed paths for these seven Lake metadata forms are excluded from content hashing:

| Form | Real paths |
| --- | ---: |
| `.ilean.hash` | 8,926 |
| `.olean.hash` | 8,926 |
| `.olean.server.hash` | 8,908 |
| `.olean.private.hash` | 8,908 |
| `.ir.sig.hash` | 8,908 |
| `.ir.hash` | 8,908 |
| `.trace` | 8,926 |

The remaining ten exclusions are the **exact** static archive paths in [inventory-policy.json](inventory-policy.json), under the pinned sysroot. There is no wildcard archive/native exclusion. This archive classification is valid only for the unchanged four direct Lean/leanchecker commands and exact environments; changed argv, environment, sysroot, work root or linker selection is rejected. Excluded paths receive metadata enumeration with regular-file, parent/symlink and link-count checks, membership checks and initial/final metadata exports. Their contents are not opened or hashed. Unknown paths and physical shadows still fail.

`contracts.py` includes `.ir.sig` in semantic target sidecar detection, output capture and the existing live output allowlist. `driver.py` uses the real classifier before content hashing. `scope.py` preserves the newly bound signatures alongside old inputs, references the separate supplement in stage receipts and exports excluded metadata separately. The other **12 of 15** base Python files remain byte-identical, including process ownership, resource admission, limits, supervision and reaping code. [Base comparison and preparation checks](preparation-reconciliation.json) record this scope. The initial classifier draft is retained in diagnostics; its archive coverage condition was tightened to keep an already bound archive authoritative rather than requiring its exclusion.

## Tests and actual complete plan check

[Exact commands](commands.txt) and unedited diagnostics are preserved. No legacy process fixture, Lean, checker, production entry, lease acquisition, lock creation, resource probe, retrieval or CI was run in this validation.

- Python fixture attempt 1: **23 passed**, exit 0. Its source copy and log remain preserved.
- Expanded fixture attempt 2: **28 passed**, exit 0. It exercises real classifier/output APIs plus production Context classification, journals, receipt references, between-stage preservation and export wiring using a synthetic inventory and no child/lease. The synthetic finish/export test supplies synthetic audit data and does **not** validate a Lean audit or simulate compiler acceptance.
- Actual complete plan builder: **one attempt, passed**, exit 0, against implementation `ea6cfc563e16fef2b20cef82a46c3faea909a843`. `driver.make_production_plan` and its real `reviewed_inputs`, `reviewed_wrapper`, Git self-binding, supplement authentication and inventory scan were exercised without substitution. The existing independent shadow check was then exercised on the real existing input roots. [Result](plan-evidence/57d4c4726c1f4781bb8b074d6c09e97b/result.json), [exact four prepared commands/environments](plan-evidence/57d4c4726c1f4781bb8b074d6c09e97b/plans.json), and [raw output](diagnostics/complete-real-plan-attempt-1.log) are available.

The actual result retained **57,661 old semantic root inputs**, including five old native shared-library bindings, added **11,426 signatures**, and enumerated **62,420 excluded paths** as metadata only. The complete protected journal has **69,624 rows**, including source/helper/tool/pin/data bindings outside those root-input counts, and covers the existing **196** project dependencies. The exact argv/environment/sysroot and independent existing-root shadow checks passed. Guards recorded **zero** excluded-content open attempts, forbidden operations, production calls, compiler/checker calls, lock/lease calls or resource probes. The future work root remained absent. The only child commands permitted by the validation guard were read-only `git show` and `git ls-tree`, recorded individually in the result.

Fixtures cover missing/changed/new signatures, same-byte identity replacement, bad family/qualification/size, metadata-vs-signature classification, unknown native/archive/hash paths, old object/IR/native/hash failures, old archive precedence, missing old inputs, links/FIFO/parents, target-signature and module shadows, generated signature capture and post-completion mutation, generated hash-sidecar rejection, exact command/environment restrictions, context journal preservation and metadata export reconstruction. Their source snapshots, fixture files, result records and logs are retained; expected rejection fixtures are not Lean failures.

## Exports, preservation and disposition

[Export summary](export-summary.json) gives the ordered reconstruction hashes: 50 signature-supplement chunks, 101 complete semantic-journal chunks and 87 excluded-metadata chunks. Each has a row-aligned manifest and byte/hash verification; concatenate listed part bytes without added separators. The master checkpoint manifest also records symlink target text for deliberate link fixtures without following those links.

[Historical preservation](historical-preservation.json) rechecks all **2,640 original wrapper entries**, **306 delta entries** and **85 failure-evidence entries**, with their manifests/parts. This is byte reconciliation, not execution. The raw pre-lock `Unlisted effective search input` failure at `c1f0f12f` and its diagnosis remain unchanged; it has not been retried through production. Both Python fixture attempts and the complete plan attempt passed; no new failed Lean attempt exists.

The staged supplied-forest mathematical draft remains uncompiled by this work. No new module resolution, kernel replay or Lean axiom audit occurred. Independent review and separately authorized fresh coordination are still required before any production entry. Published with `[skip ci]`; the worker pauses for review.
