# rowsSteps exact full-count repair

Tested source: `c0584cb7f2dc2ba34e49457d4dac8c36de7126a9`. Branch: `light-eft-spanners-checkpoints`. This bounded incremental repair awaits independent review. Exactly `LightEFTSpanners.StoredRecords.rowsSteps._unsafe_rec` disappears: **9 → 8 partial roots**, none added. The unchanged exhaustive unfiltered strict gate still fails with **16 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open.

## Accepted baseline and preservation

The parent reports completed independent review accepting source `5d34b4c7337136fb9d4c82d4cc48511882867e39` and evidence `d0a3ef16b14f039568217461b0b196a628ca8edf`, with 9 partial roots / 18 findings. This records source/log/hash reconciliation, not fresh independent execution or CI. The reviewer was idle. The live connection, clean branch, all 1,860 accepted-manifest entries, 486 production source/object bindings, disk/memory, processes and universal lock were checked before admission.

Only StoredRecordTrace.lean changes among the 486 production sources. All seven existing theorem statements and full proof bodies remain byte-identical: reverse_row_trace, reverse_matrix_trace, rows_trace, materialize_trace, rowSteps_le, rowsSteps_le and matrixSteps_le. The prefix before rowsSteps and suffix from rows_trace onward are unchanged. Other definitions and partial roots remain untouched, including rowSteps, values and matrixSteps. All previous checkpoint trees, failures, memory refusals/recoveries and historical sequencing qualifications remain preserved. No other paper, deleted workspace or website was accessed.

## Exact full count

rowsSteps now uses total List.rec returning a function of the starting row index. The empty matrix still costs zero. At r::rs, the exact term order is `rowSteps es i 0 r + r.length + 2 + next (i+1)`, preserving the reset column index, row reversal/transition charges and row-index increment. Ragged and empty rows are allowed. No matrix-final reversal/halt charge is added; matrixSteps remains unchanged. Nil and cons equations are proved by rfl.

`RowsStepsComparison.rowsSteps_eq_prior` proves equality of the complete natural count against the hash-bound accepted old implementation for arbitrary edge lists es, starting index i and matrix W. Induction generalizes i and applies the hypothesis at i+1 through congrArg without reordering the surrounding additions. The proof has **no axioms**. The exact replacement body is byte-bound to the production definition. This is full-count equality, not merely a bound or a restriction to well-formed matrices.

Twenty-four kernel-checked numerical fixtures cover empty matrices, empty/ragged rows, nonzero and very large starting indices, duplicate/reversed undirected edge-list entries, differing scan costs by row/column, and signed rational payloads. Expected counts are retained with a separate finite-scan derivation. Three symbolic rfl fixtures check empty, cons and two-row equations in the exact additive order. Metadata confirms safe, total, computable, explicit List.rec, no self-reference and no partial companion. These are counts in the inherited rational-atom controller model, not physical-runtime measurements.

## Failed attempt and definitional transparency

The first owner compile failed in the unchanged rowsSteps_le proof: nlinarith treated the unfolded recursor tail and the named rowsSteps tail as distinct arithmetic atoms. Its entire raw diagnostic, submitted source and UUID receipt `57187fb03f214553a075cd55a43d8d55` are preserved.

The final definition is marked reducible using the ordinary Lean attribute, letting arithmetic normalization identify those definitionally equal counts. This does not alter the function body, add a premise or axiom, modify the toolchain/runtime, suppress warnings, or exempt any audit finding. All seven original proof bodies then compile unchanged. Exact legacy equality was rerun against the final source and remains axiom-free. No completed production build was repeated after resource recovery.

## Resource refusal and recovery

After the successful owner compile, fixture admission `f35ee34f7e284a7f9880e411e8828c51` was refused with 4227612672 bytes of observed cgroup headroom against the unchanged 4,294,967,296-byte requirement. No fixture compiler was started. The original admission JSON, intended source snapshots, partial build state and tool diagnostic are retained in refused-admissions and the evidence directory.

Authorized recovery applied POSIX_FADV_DONTNEED on read-only descriptors to 4374 inactive prior task-created .olean files totaling 959158792 bytes. Each file was first hashed against its preserved source/object provenance; inode, size and mtime stayed unchanged. The common lock was held, and no compiler/checker was running. The recovery JSON records every file and before/after memory ownership statistics. Headroom observed immediately before advice was 4315324416 bytes and afterward 5309902848 bytes. These later observations are distinct from the earlier refusal.

No file was deleted or written by the advice; no global cache drop, memory/security-limit change, unrelated process interference or gate weakening occurred. The unchanged gate then admitted pending fixtures and builds. The successful owner state was reused; the remaining 165 affected modules were compiled without repeating it. Earlier accepted recovery records remain unchanged.

## Complete sequential validation

Import analysis and an independent fixed-point computation agree on **166 affected modules / 320 inherited objects**. All affected entries were removed from the initial state. Every final affected module, including aggregate compilation, passed strict rebuilding. The 320 inherited objects retain accepted source/object/direct-import provenance. The initial binding file also records all 486 copied objects; final provenance distinguishes fresh and inherited validation.

Official Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, all nine pins and mathlib `5ed2965256430c3649e86755f9576b54eca72435` are unchanged. Strict flags are `-j1 -DautoImplicit=false -DwarningAsError=true`. Full argv, executable/manifest/supervisor hashes, source/object hashes, snapshots, PIDs and timing are retained. Entry points are `python checkpoints/light-eft-rows-steps-pilot-20261017/legacy_compare.py`, `run.py pilot`, `build`, `audit`, `replay`, and the guarded recover_cache.py after a refused admission. No default Lake build, aggregate-prefix replay, warning suppression, alternate runtime or blanket noncomputable change was used.

The unchanged exhaustive audit covers **8997 actual-owner roots**, **60416 recursively visited constants**, and **48 opaque bodies**. Types, bodies, generated declarations, inductive families and recursor rules are traversed. Only propext, Classical.choice and Quot.sound occur as axioms in the full project closure. There are no unsafe project roots or aggregate-owned declarations. Exactly rowsSteps's companion disappears; all other partial roots remain. The audit exits 1 on 8 partial roots / 16 root-and-recursive findings. No filtering, exemption or allowlist expansion occurred.

Official target resolution and the locked supervisor both select exactly `LightEFTSpanners.StoredRecordTrace`. `leanchecker -v LightEFTSpanners.StoredRecordTrace` passes with one replay line. Audit/replay use the completed isolated outputs and pinned packages without historical project fallback. Legacy equality separately uses hash-bound accepted old objects. This remains incremental validation, not a clean final exact-source gate.

## Evidence and handoff

The pilot retains 173 unique source-bound receipts, 665 submitted-source entries, individual successful memory admissions and locked preflights, one universal lock inode, non-overlapping execution and reaped children. No receipt is carried forward. The separately preserved refusal has no compiler receipt. There are 2 nonzero invocations: the initial owner proof failure and the expected exhaustive strict-audit rejection. Zero anchored warning headers occur; hints and option names are not counted as warnings. All raw logs and failed attempts remain preserved.

Minimum successful admission cgroup headroom: 4312018944 bytes; minimum system MemAvailable: 17395073024 bytes. Minimum locked-preflight headroom: 4311855104 bytes. Successful-admission minima exclude the refusal. These separate observations are not reservations or continuous-headroom guarantees.

The full recursive TSV and 207 ordered row-aligned chunks are retained. audit-export/manifest.json gives lengths, per-chunk hashes and reconstruction SHA256 `4708590d27a619e799b76ea557968c3bcd12b876f70957e5528c79f4f3a720d7`. Concatenate bytes in order with no additional headers or separators. evidence-sha256.json seals every checkpoint file except itself. Reconciliation invokes no compiler/checker, rewrites only current derived evidence, and verifies historical manifests without modifying them.

Terminal checks show no compiler/checker, a free common lock, 14216880128 bytes free disk and a 17179869184-byte memory limit. Repository-wide CI observations are preserved. Additive commits use [skip ci], followed by normal push after remote-state verification. Paused for independent review; strict-gate or whole-paper acceptance is not claimed.
