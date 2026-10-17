# SampleRecords.values complete nested optional-cell repair

Tested source: `43533b0b36a63bbcba15722628ddbf38b510e8d8`. Branch: `light-eft-spanners-checkpoints`. This bounded incremental checkpoint awaits independent review. Exactly `LightEFTSpanners.SampleRecords.values._unsafe_rec` disappears: **4 → 3 partial roots**, none added. The unchanged exhaustive unfiltered strict gate still fails with **6 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open.

## Accepted baseline and frozen scope

The parent reports completed independent review accepting source `99efafffcb7de3652a61e9f2426a4df049654a11` and evidence `bcbdfd5dc641343e07f46edf0120ab8bb2274b35`, with 4 partial roots / 8 findings. This records source/log/hash reconciliation, not fresh independent execution or CI. Review had finished. The live connection, clean branch, all 1,664 accepted manifest entries, 486 source/object bindings, disk/memory, processes and common lock were verified.

Only SampleRecordMatrix.lean changes among the 486 production sources. The entire prefix before values and suffix from rowValues_length onward are byte-identical. Entry, Records, value, accepted rowValues/equations/reducible attribute, both length theorem statements/full proofs and encode remain unchanged. All four preexisting theorem declarations (rowValues_nil, rowValues_cons, rowValues_length, values_length) retain their statements and full proofs. Every sibling source and historical checkpoint is preserved. No SCC or deleted workspace was accessed, no website changed.

## Exact nested semantics

values uses total List.rec returning a function of the starting row. Nil returns []; cons returns exactly `rowValues i 0 row :: next (i+1)`. Complete nested ordered optional-rational cell lists are preserved, including ragged records, leading/interior/trailing empty rows, ordered duplicates, signed rational weights and none positions. Each row advances the row index even when empty, and resets its column to zero. The unchanged value function retains diagonal suppression and `host || (drawn && selected && !seed)`.

`ValuesComparison.values_eq_prior` proves universal full nested-list equality against the hash-bound accepted implementation for arbitrary starting i and Records. Induction generalizes i and uses congrArg with the entire rowValues output at i+1. The proof has **no axioms** and its replacement body is byte-bound to production. This is not merely a length or projection check. Ordinary reducible transparency is applied only to values for definitional matching in the unchanged length proof. No axiom, premise, runtime modification or audit exemption is introduced.

Seventy-six fixtures compare complete explicitly written nested Option Rational lists through ordinary kernel rfl. They cover all sixteen field combinations on and off the diagonal, arbitrary/huge starting rows, ragged dimensions, empty rows, row advancement, column reset, duplicates, host override, seed suppression and signed weights. Independent host-side expected-matrix computation and exact data are retained. Three symbolic equations check nil, cons and a ragged four-row record matrix. Metadata verifies safe, total, computable List.rec without self-reference or partial companion. No physical-runtime claim follows.

## Capacity boundary and preservation

The previous saved terminal headroom was below 4 GiB. Before any compiler/checker, a new startup memory admission was refused. Its original observation, process check, accepted source snapshot and refused build-state snapshot are preserved under evidence/startup-capacity. With no compiler/checker and the universal lock held, hash-verified inactive prior task-created objects received read-only per-file POSIX_FADV_DONTNEED advice. No unique file was deleted or modified, no global cache drop or resource/security setting change occurred, and no unrelated process was interfered with.

Startup admissions are distinct from per-compiler admissions: a fresh qualifying startup observation follows recovery and precedes the first compiler receipt. Every compiler/checker still obtains its own fresh memory admission and locked preflight. Startup recovery reconciliation verifies the recorded file hashes and no-live-compiler observations. Recovery records (including any later per-invocation recovery): `[{"path": "startup-capacity/cache-recovery-4d38aa96cdf94d719cc7bd088c937cb4.json", "files": 6804, "bytes": 1490827496, "before_headroom": 3334512640, "after_headroom": 4843634688}]`. Additional per-invocation refusals: 0. All refusals and recovery hashes remain preserved; the gate stays at 4,294,967,296 bytes for cgroup headroom and system MemAvailable.

## Sequential validation

Independently recomputed closure: **177 affected modules / 309 inherited objects**. All affected modules, including aggregate compilation, passed strict rebuild; inherited objects retain accepted source/object/direct-import provenance. Completed builds were reused, never duplicated. Official Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, all nine dependency pins and mathlib `5ed2965256430c3649e86755f9576b54eca72435` remain unchanged.

Compiler flags: `-j1 -DautoImplicit=false -DwarningAsError=true`. Entry points: `python checkpoints/light-eft-sample-values-pilot-20261017/legacy_compare.py`, then `run.py pilot`, `build`, `audit`, `replay`. Full argv/options, executable/manifest/supervisor hashes, submitted source snapshots, source/object hashes, PIDs and times are retained. No default Lake build, aggregate-prefix replay, blanket noncomputable change, alternate runtime, warning suppression, filtering, exemption or gate weakening was used.

The unchanged exhaustive audit covers **8961 actual-owner roots**, **60380 recursively visited constants**, and **48 opaque bodies**, traversing types, bodies, generated declarations, inductive families and recursor rules. Full-project axioms are exactly propext, Classical.choice and Quot.sound. No unsafe project roots or aggregate-owned declarations occur. Only values's partial companion disappears; all other partial roots remain. The audit exits 1 on three partial roots / six root-and-recursive findings. The strict gate does not pass.

Actual-owner resolution selects exactly `LightEFTSpanners.SampleRecordMatrix`. Official `leanchecker -v LightEFTSpanners.SampleRecordMatrix` passes with one replay line. Audit/replay use completed isolated outputs and pinned packages without historical project fallback; legacy comparison separately uses hash-bound old objects. This remains incremental validation, not a clean final exact-source gate.

## Receipts, raw diagnostics and handoff

There are 182 unique source-bound receipts and 672 submitted-source entries. Reconciliation verifies individual admissions/preflights, one lock inode, non-overlap, reaped children, all snapshots, unchanged frozen source and inherited provenance. Anchored warning headers total zero; hints and option names are not warnings. Nonzero invocations: `[{"uuid": "528ded83c93a4f1ab2f39362347653f3", "label": "complete-all-owner-audit", "exit": 1}]`. Every raw diagnostic and source snapshot is retained. Startup refused admissions are not counted as compiler invocations.

Minimum per-invocation admitted headroom: 4513341440 bytes; minimum system MemAvailable: 17375670272 bytes; minimum locked-preflight headroom: 4513046528 bytes. Observations are not reservations or continuous-headroom guarantees.

Full recursive TSV plus 207 ordered row-aligned chunks are retained. audit-export/manifest.json supplies per-chunk lengths/hashes and reconstruction SHA256 `dde39c2032ac0c297adbfab01c7ea04326cab5139b9d08011cf941c5ad631ab6`. Concatenate listed bytes in order without added headers or separators. evidence-sha256.json seals every checkpoint file except itself. Reconciliation runs no compiler/checker and verifies historical manifests without modification.

Terminal evidence records no compiler/checker, a free lock, 13156769792 bytes disk free and 17179869184 bytes memory limit. Terminal observed headroom is 3119263744 bytes; it is not an admission for future work. Fresh qualifying admission is required before any later compiler/checker. Repository-wide CI observations are retained. Additive commits use [skip ci] and normal push after remote verification. Paused for independent review; no strict-gate or whole-paper acceptance claimed.
