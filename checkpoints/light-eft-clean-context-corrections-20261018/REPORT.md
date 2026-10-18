# Disabled Light EFT preparation corrections

Base packet: **`83cd543c23fbf7349e82baa61cfccf1b2e27da4d`**. Frozen mathematical source remains **`78cb40c7837db049d645d73696f2e0b724ce8a3b`**. This is a correction to preparation contracts and evidence attribution only. Production remains disabled; the artifact descriptor remains `UNAVAILABLE_REVIEW_REQUIRED`. No Lean/compiler/checker/version-check, retrieval, extraction, cache advice, CI, mathematical source or website operation occurred. Existing accepted proof and audit results are unchanged.

Independent review of the base packet verified its 59 manifest bindings, 486 source hashes, 1,107 project import edges, 2,912 receipt/log bindings, 20 supervisor/production bindings and historical preservation. That review identified the four preparation issues corrected here. This records the reported review, not new compiler execution or acceptance of this correction. The correction awaits independent review.

## Runtime evidence cannot be empty or unbound

`clean_contract.validate_runtime_evidence` now requires a nonempty list of **live-runtime** observations. There is **no terminal-only exception**, including for genuinely short-lived children; if no live sample exists, the modeled stage rejects. Each sample binds its attempt UUID, stage, module and complete child incarnation to the stage receipt.

Every sample must include timestamped accounting for **all actually observed visible nodes**, with the same pinned directory/file identities, limits and OOM/PID-event identities as pre-exec accounting. Missing nodes, file identities or anonymous-growth entries reject. Growth keys must exactly match visible node paths, and each value must equal the observed anonymous statistic minus that node's pre-exec baseline. Shared RSS, headroom, host memory and the unchanged stop thresholds remain checked. Unknown ancestors stay unknown; no full-ancestor visibility gate is added.

The temporal contract is:

`receipt.started_ns ≤ runtime_wall_started_ns ≤ ordered sample interval < terminal_confirmation.finished_ns < launch + 90 seconds`.

Owned terminal confirmation must precede or equal final cleanup `ended_ns`. Cleanup may finish after the child runtime deadline; the deadline is never calculated from cleanup time or receipt-creation time. Samples at/after terminal confirmation, before launch, out of order, with missing/misbound timestamps, or at/after the deadline reject. These remain intermittent observations, not a continuous-peak or physical-runtime proof. The fields are normalized synthetic contracts for a later reviewed executor; accepted supervisor implementations are not modified or invoked.

## Invalid text and blank names reject permanently

`audit_data.utf8` converts `UnicodeDecodeError` into `Rejected`. The existing finalization failure handler then marks the run stopped and quarantines all 486 provisional objects plus 485 provisional resolutions. A retry with repaired audit bytes cannot promote either ledger. Negative fixtures inject invalid UTF-8 into each of the five audit outputs, repair all chunk hashes so rejection reaches output validation, and verify the sticky state, quarantine and rejection of a subsequent valid retry. Strict-findings bytes also reject independently of decoding.

Loaded module lines and declaration names/owners must be nonempty and have no surrounding whitespace. Fixtures include empty and whitespace module lines, and declaration names made consistently blank in both root and closure tables. Cross-table agreement alone cannot accept blank names.

## Review attribution corrected

Both [the chain index](../light-eft-clean-context-preparation-20261018/chain-evidence-index.json) and [the dated repository index](../../Light%20Edge%20Fault%20Tolerant%20Graph%20Spanners/verification/current-exact-source-evidence-20261018.json) now distinguish:

- **Worker:** locally rehashed all 244 original execution files.
- **Independent reviewer:** verified the 244-entry manifest, 216 ordered chunks and all five complete reconstructed exports.
- **Retained limitation:** the parent connector could not retrieve the entire approximately 30 MB canonical input inventory. Matching 83,032-binding preservation receipts and manifest review remain recorded; this is not independent retrieval of all original files, provenance authentication or clean validation.

The regeneration helper carries the same attribution, and a static fixture verifies it agrees across both indexes. Original audit reports, audit files, proof sources, per-chain evidence, historical 57/56-partial metadata, statement statuses and mathematical qualifications remain unchanged.

## Validation and preserved history

All **80 synthetic/static tests passed**, including all 46 tests in the reviewed base packet and all original 40 tests. There are 28 runtime-evidence cases, including two positive timing cases, five added finalization/name tests (with invalid-byte subcases for all five outputs), and one attribution case. These fixtures remain explicitly fictional and cannot enable production or establish actual clean execution.

- [First correction run](tests-invocation-01.log): 78 tests passed.
- [Final correction run](tests-invocation-02.log): 80 tests passed.
- [Commands](commands.txt), [validation result](validation.json), [correction manifest](manifest.json).

Before edits, all 59 previous bindings were verified. [preservation.json](preservation.json) records 18 snapshotted files, including previous implementations, both indexes, validator, report and manifest. All original test logs 01–04 and original failed attempts remain byte-identical; the reviewed Git commit preserves the complete previous packet. The earlier failed draft and metadata-validation attempts remain intact. No failed correction test attempt occurred.

The refreshed preparation bindings still match all **14 unchanged supervisor references** and **six unchanged production/pin files**. The frozen 486-source/1,107-edge graph is unchanged. The plan still has **1,457 stages** and one **separate unexecuted** version check. Ordinary/audit file limits remain distinct at 16/64 MiB. The manifest and validation record cover the corrected implementation and current evidence layer.

The original preparation report is retained below a correction notice; original reports and test histories are not rewritten as fresh runs. Publication uses `[skip ci]` and only the Light EFT correction, preparation and dated evidence files. Authenticated clean validation, reviewed production execution, exact CI, Theorem 34 replacement scaling, runtime-model qualifications, website completion and whole-paper acceptance remain separate and pending. The worker pauses for review with no compiler/checker active and the common exclusive lock free.
