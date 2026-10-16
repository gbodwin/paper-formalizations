# StoredWeightLookup.rowValue total-recursor pilot

Tested source: `60824d24211dee4a7437f226910c9232950606c4`. Branch: `light-eft-spanners-checkpoints`. Exact source/object binding is in `evidence/source-binding.json` and `evidence/source-object-provenance.json`.

This bounded incremental repair awaits independent review. Exactly `LightEFTSpanners.StoredWeightLookup.rowValue._unsafe_rec` disappears: **34 → 33 partial roots**, with none added. The unchanged exhaustive strict gate still fails with **66 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open. No other target is started.

## Accepted baseline and connection

The parent independently accepted source `bfe8ac83406e6811c6038f04e91ad08000fcacdb` and evidence `c317528a4cf6e399ec9c9b6a5784c217075579e2`. Review had finished. This records source/log/hash reconciliation, not fresh reviewer execution or live-object inspection.

A disconnection event was reported at 19:32 after the preceding task completed. Live environment commands succeeded before this task admitted any compiler. HEAD and tracked source were clean at the accepted evidence commit. All 964 parent manifest entries and all 486 live source/object bindings were rehashed. No prior build was resumed or duplicated. No Lean/Lake/checker process was active; the universal exclusive lock was free. Approximately 19 GiB disk was available, and the 16 GiB cgroup had more than 4 GiB headroom. The actual rowValue declaration was inspected before replacement. No canceled workspace was accessed.

Every compiler/checker invocation requires at least 4 GiB cgroup headroom and 4 GiB system MemAvailable. Unique observations in memory-admissions.jsonl precede matching receipts; memory-admission-summary.json records minima. These are admission observations, not reservations or peak-memory guarantees. MemoryAdmission.py and the common exclusive supervisor are unchanged from the accepted parent. Per-invocation process/disk preflights, lock identity, UUID, PID, source snapshots, hashes, UTC/monotonic times, exit and child reaping remain recorded.

## Exact rational semantics and preserved scope

Only rowValue changes definition. Explicit total List.rec folds the rational list into a function of the arbitrary natural index: an empty list gives zero; index zero returns the head verbatim; a successor uses the tail's lookup at the predecessor. The three equations are proved by rfl. No nonnegativity, matrix-size, in-range, bank-validity or ordering premise is introduced. Signed and fractional payloads, duplicate entries and arbitrary large indices remain supported; out-of-range results remain zero.

LegacyEquivalence.lean imports the exact hash-bound accepted objects and proves equality of the entire rational output for every j and every list of rationals. The replacement body is identical to production. The successful proof uses induction on the list, generalizing j; its axioms are only propext and Quot.sound. This is exact semantic equality, not a runtime or implementation-cost claim.

Twenty fixtures compare the complete rational result, covering empty lists, zero/successor/huge indices, all positions in a signed fractional list, its first out-of-range index, zero before nonzero, repeated values, negative values, large rational payloads and longer lists. Universal equation examples and metadata checks verify safety, totality, computability, explicit List.rec, no self-reference and no partial companion.

The transition, State, value, rowSteps and steps definitions remain byte-identical. All seven pre-existing theorem statements retain their hypotheses unchanged. Three simplification arguments in row_trace and rowValue_eq use the new explicit equations; these anticipated proof-interface adjustments were made before compilation. All other existing proof bodies remain unchanged. All other 485 closure source files, including the accepted repaired row and rows, remain unchanged.

## Validation and audit

The independently source-derived closure has 131 affected modules and 355 unaffected modules. All 131, including aggregate compilation, receive fresh strict builds. Affected build-state entries were removed before rebuilding so byte-identical intermediate outputs cannot bypass required compilation. The other 355 objects retain accepted source, direct-import and object hashes. Reconciliation independently rederives the closure; historical receipts are not counted as new execution.

Official Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and all nine pinned packages remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Runners verify each dependency revision before use. Exact executable, supervisor and manifest hashes are retained. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build, warning suppression, alternate runtime, dependency change or blanket noncomputable conversion occurs.

The complete actual-owner and recursive audit is unchanged except output-directory substitution. It covers 9166 actual-owner roots, 60585 recursive constants and 48 opaque bodies, including recursive types/bodies and generated declarations. No partial root or violation is filtered or exempted. Only propext, Classical.choice and Quot.sound occur as axioms. No unsafe project root or aggregate-owned declaration occurs. Exactly the rowValue companion disappears; all other 33 partial roots remain. The audit exits 1 with 66 findings. This remains a failing strict gate.

The official resolver selects only LightEFTSpanners.StoredWeightLookup; the supervisor repeats target resolution under the lock. `leanchecker -v LightEFTSpanners.StoredWeightLookup` passes with exactly one replay line. No aggregate-prefix replay occurs. Current audit/replay use isolated current outputs, official toolchain and pinned package paths, with no historical project fallback. The legacy equality uses the separately hash-bound accepted outputs.

## Raw attempts and preservation

137 source-bound receipts contain 629 submitted-source entries, each with persisted preflight and memory admission. Reconciliation checks all hashes, UUID uniqueness, one common lock inode, strict non-overlap and reaped children. Zero anchored warning headers occur; hints and option names are not counted as warnings.

The first legacy equality attempt failed because the legacy empty-list definition did not reduce at an arbitrary index with rfl alone. Its UUID is ca4aa582069847869bfd8cc46106ed2d. Splitting the index into zero/successor cases repairs that proof. The failed log's sorryAx is Lean's error-recovery output and is not in the successful equality object or audited closure. The complete failed source snapshot and raw diagnostic are preserved. The remaining nonzero invocation is the unchanged exhaustive audit rejecting partial roots. No production compile or fixture failed.

UUID directories are authoritative; semantic-label logs are convenience copies and can reflect the latest attempt. All historical checkpoint trees, raw failures, earlier execution qualifications, aggregate-prefix OOM/sequencing issue, statement-count correction and evidence-writer-label correction remain unchanged. No website or other paper is modified.

The original recursive TSV and 207 ordered row-aligned chunks are retained. audit-export/manifest.json gives chunk hashes and the whole-file reconstruction hash. Concatenate bytes in order with no additional headers or separators. evidence-sha256.json seals all checkpoint files except itself.

`reconcile.py` is an evidence writer: it regenerates current derived evidence and chunks, without running Lean/checker, and reads historical manifests without modifying them. Entry points are legacy_compare.py; run.py pilot/build/audit/replay; and reconcile.py. No compiler/checker runs during publication reconciliation. Terminal resource/process/lock/CI observations are saved. Source and evidence use additive [skip ci] commits, with normal push only after remote-state verification. Paused for independent review.

Observed minimum cgroup headroom: 8925052928 bytes; minimum system MemAvailable: 17452634112 bytes.
