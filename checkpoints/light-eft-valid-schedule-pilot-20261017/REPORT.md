# ValidSchedule partial checkpoint — memory admission refused

Source: `88ffd43c81989b621922df852962b0c9378aac8c`. Branch: `light-eft-spanners-checkpoints`. **Partial development only; not a validated repair or acceptance claim.** No CI was started. The accepted baseline remains 12 partial roots / 24 findings. No fresh exhaustive audit was executed, so no new root count or strict-gate improvement is claimed.

## Preserved baseline and scope

The parent accepted source `be9acc66ab0829b16a4f6adefd40f8ef4119358c` and evidence `7d000cc37fc2b37a2f3084c708871fb8fe0ec308`, and stated review had finished. This records independent source/log/hash reconciliation, not fresh independent execution or CI. Live connection, clean accepted tracked state, resources, processes and common lock were checked before admission. All 1,521 parent-manifest entries and all 486 source/object bindings matched. No Lean/Lake/checker was active and the lock was free.

Only `StoredCandidates.ValidSchedule`, owned by StoredCandidateRefinement, is changed. Its body uses total `List.rec` returning a predicate on E, with base True and exactly the original budget equality, HostRepresentation conjunction and recursive predicate at `updated Q E w h R`. Two nil/cons iff equations are added. All three preexisting theorem headers and their complete proof bodies are unchanged. HostRepresentation and the entire originalStep-and-later suffix are byte-identical. All other 485 production source files, including repaired work and selected, are unchanged. No new premise was added.

The independent fixed-point closure is 147 affected modules and 339 inherited objects. All affected entries were removed from fresh build state before compilation. One affected module compiled; **146 remain pending**. The isolated directory also contains copied stale objects for those pending modules, but they are explicitly absent from fresh build state and are not counted as validated. No complete audit or replay is permitted by run.py until all 486 state bindings are present and verified.

## Completed execution

Two sequential source-bound invocations completed successfully under the unchanged universal lock:

1. Universal exact-legacy equivalence, against the hash-bound accepted owner object. The proof covers arbitrary n, J, Q, E, weights, scale, eligible sets, host sets, tape, threshold and input list. Induction generalizes E and applies the induction hypothesis at the original updated state; both conjunctions are preserved verbatim. The proof reports exactly propext, Classical.choice and Quot.sound. No sorryAx or other axiom occurs.
2. Strict compilation of StoredCandidateRefinement using the official Lean toolchain.

Official Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and all nine pinned packages remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Exact executable, manifest, source and object hashes are retained. Commands use `-j1 -DautoImplicit=false -DwarningAsError=true`. Both completed raw logs contain zero anchored warning/error diagnostics. Their two receipts, two locked preflights, four submitted-source entries, child PIDs, timings, snapshots, lock identity and reaping are verified by partial_reconcile.py. No aggregate replay, default Lake build, runtime alteration, warning suppression or blanket noncomputable change occurred.

## Admission refusal and pending validation

At `2026-10-17T02:02:06.980705+00:00`, the unchanged MemoryAdmission.py refused label `pilot-semantics-and-safety`:

- Admission ID: `5432808d3cc24919bf19b73f5381f741`.
- Cgroup current: 12,935,749,632 bytes; limit: 17,179,869,184 bytes.
- Observed cgroup headroom: **4,244,119,552 bytes**.
- Required headroom: **4,294,967,296 bytes** (4 GiB).
- System MemAvailable: 17,788,088,320 bytes; this separate threshold passed.

The fixture compiler was **not spawned**. There is no compiler receipt for the refusal; the persisted memory-admission record is the evidence. The two admitted invocations and this one refused admission are counted separately. Raw admission data, the transcribed tool diagnostic and unchanged proposed source snapshots are preserved under evidence/. No retry, threshold reduction, cache eviction, memory-limit change or safety-policy change was made. Later observed headroom fluctuated above the threshold; this report asserts the actual refusal, not permanently unavailable memory. Observed admission and locked-preflight samples are distinct and do not certify continuous headroom.

PilotCheck.lean contains 16 proposed kernel proof cases for exact nil/singleton/two-element contracts, necessity of each conjunct, accepted/rejected updated states, duplicate records, zero vertices, negative scale/negative budget and an invalid budget. **These cases have not been compiled or checked.** They are logical proposition tests, not an executable decidability oracle for arbitrary HostRepresentation.

Pending work: validate/fix the fixture harness, finish the remaining 146 strict builds, run the unchanged unfiltered recursive audit, resolve and replay only StoredCandidateRefinement, then reconcile and seal completed evidence. The full reconcile.py is preserved for that later completed state and handles refused admissions separately; it has not been used to claim completion. The checkpoint was reconciled with partial_reconcile.py instead.

## Evidence and handoff

`evidence/partial-reconciliation.json` is the bounded result. `evidence/source-object-provenance.json` contains exactly 340 valid state entries: one fresh module plus 339 inherited bindings. `evidence/source-binding.json` binds all current source bytes to the source commit. `evidence/prior-preservation.json` verifies all earlier evidence manifests without modifying their trees. Raw failed attempts from prior checkpoints and all historical recovery qualifications remain unchanged.

There are **no new audit chunks**, because no new audit ran. The accepted [prior full audit export](../light-eft-candidates-selected-pilot-20261017/audit-export/manifest.json), with all 207 chunks and reconstruction hash, remains preserved unchanged and is historical evidence only. `evidence-sha256.json` seals all files in this partial checkpoint except itself.

Terminal resources/process/lock and GitHub CI observations are preserved. No compiler/checker remains running; the common lock is free. Additive commits use [skip ci], with remote-state verification before normal push. Stopped for independent review and resource/admission coordination. No other paper, deleted workspace or website was accessed. Clean final exact-source validation, strict-gate success, Theorem 34, physical-runtime claims and whole-paper completion remain open.

Initial free disk: 14942040064 bytes (13.92 GiB). Terminal free disk: 14941495296 bytes (13.92 GiB). Terminal observed cgroup headroom: 4332191744 bytes.
