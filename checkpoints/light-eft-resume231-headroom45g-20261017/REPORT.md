# Light EFT: 77 sequential module chains at the 4.5 GiB first gate

All **231 planned stages passed**: 77 compilations, 77 exact checker-target resolutions, and 77 individual official kernel replays. Frozen source: `78cb40c7837db049d645d73696f2e0b724ce8a3b`. Base evidence: `0261a5a9d1948ebab7be44514bace02b9a60b03a`. These 77 new chains await independent review. The 94 previously accepted chains were reused without rerunning accepted stages. This is incremental module validation, not whole-paper acceptance.

## Reporting correction and scope

The preceding terminal response substituted unrelated SCC evidence. That response does not describe this batch. The preserved Light EFT receipts and artifacts were subsequently reconciled read-only. This publication concerns only `light-eft-resume231-headroom45g-20261017`; no SCC evidence is used. No Lean, fixture, cache-advice pass, or full input-content pass was rerun during reconciliation or publication.

The sole authorized gate change was the first `LightEFTSpanners.BernoulliFlagEncoding` compile's visible admission/preexec floor, from 5 GiB to **4.5 GiB = 4,831,838,208 bytes**. The production-guard boundary tests accepted equality and refused 4,831,838,207 bytes. [gate-boundary.json](gate-boundary.json) binds the tested controller and plan hashes. Runtime helpers remain byte-identical to the prior 5 GiB checkpoint; `run_batch.py` differs only in that gate literal. Historical helper prose mentioning 5 GiB is not the executed gate: the plan and receipts record 4.5 GiB.

## Actual execution and resources

Graph entries **95–171**, from `BernoulliFlagEncoding` through `StoredPreparedCandidateOriginal`, ran in dependency order, with compile → resolve → replay for each module. There were zero failed or skipped stages, no retries, no accepted-seed reruns, and zero anchored Lean warning headers. [module-status.json](module-status.json) lists every chain, source/object hash, UUID, and receipt. [result-reconciliation.json](result-reconciliation.json) gives full commands, environments, timing, resource measurements, and results for all 231 stages. Each attempt directory retains its raw diagnostics and samples.

| First compile measurement | Bytes |
| --- | ---: |
| Required visible admission/preexec | 4,831,838,208 |
| Actual visible admission | 4,875,730,944 |
| Actual visible preexec | 4,873,035,776 |
| Host available at admission | 17,698,488,320 |
| Host available at preexec | 17,694,093,312 |
| Sampled RSS peak | 3,445,067,776 |
| wait4 maximum RSS | 3,456,544,768 |

The first compile's sampled RSS peak was also the maximum sampled RSS across this batch. Sampled peaks are not continuous measurements. Null teardown metrics remain in raw telemetry; terminal completion requires the reviewed whole-process checks and owned waitid/wait4, not a leader-state shortcut.

Unchanged controls: AS 12 GiB; CPU 60 seconds; wall deadline 90 seconds; FSIZE 16 MiB; CORE 0; sampled RSS stop 6 GiB; per-cgroup anonymous-growth stop 3 GiB; runtime visible/host floor 1 GiB. Ordinary compile/resolve admission remains 3 GiB and replay admission 4 GiB; host admission remains 3 GiB. Compiler and resolver options are `-j1 -s65536 -M5120 -DautoImplicit=false -DwarningAsError=true`; compile logs confirm the 128 MiB allocator arena. Each replay uses official `leanchecker -v MODULE`, with singleton output checked exactly.

Official Lean **4.34.0** was used. Lean executable SHA256: `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`; checker: `ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe`. All nine dependency revisions still match the unchanged manifest, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. [source-toolchain-object-hashes.json](source-toolchain-object-hashes.json) records exact source, tool, object, and dependency bindings. No runtime shim, default Lake build, dependency update, or new CI was used.

## Finite advice and preservation

Exactly one renewed finite new-scope hash/advice pass completed, **20:59:03.737724–20:59:05.950805 UTC on October 17, 2026**. Scope A comprises 3,809 explicitly authorized archive files / 818,684,031 bytes; scope B comprises 708 selected finalized evidence-data files / 385,582,329 bytes. Their combined ceiling is **4,517 distinct files / 1,204,266,360 bytes**. [one-time-extension-verified.jsonl](one-time-extension-verified.jsonl) records every new binding; [one-time-cache-advice.json](one-time-cache-advice.json) records the pass. Authorities and selectors are pinned in [PLAN.json](PLAN.json). The 141 subsequent ordinary advice passes exclude both new scopes. No extraction, installation, extra archive search, or new-scope repeat occurred. Nominal advised bytes are not claimed as reclaimed memory. Agreement with recorded local candidate archive hashes does not establish stronger cache-installation provenance.

The initial and final full preservation checks cover **79,882 bindings**. Both digests equal `bead9d4e5ec6e56d0b95718e82dcb4d9cb9bbc25916c505bc79791cd45dd3e35`; all paths were attempted and changes are empty. [final-content-verification.json](final-content-verification.json) completed at **21:53:41.057372 UTC**. Publication hashes the evidence itself and small source/tool/object bindings; it does not perform a third full frozen-input pass.

The retained output root is `.lake/light-eft-batch100-entries72-171-20261017-ee496fe7834c4e86994b3933112caff7`: **171 objects and 100 resolutions**, preserving the original 94 objects and 23 resolutions unchanged. All 171 objects are also retained under [preserved-objects](preserved-objects). The final ledger's object-stream digest is `70709ee710ad909ff1cb9abf7c2cbe047caa93a403e601c8244a7adb776600f0`. Original bindings are in [retained-root-binding.json](retained-root-binding.json).

## Sequencing, limits, and review handoff

One continuous universal lease, supervisor PID **191463**, FD **3**, device **33**, inode **3849**, lasted **20:58:21.028425–21:53:44.672246 UTC**. All 231 UUIDs and child PIDs are unique; receipt intervals do not overlap; all children were reaped. The last stage ended **21:53:13.864518 UTC**. Final preservation preceded the verified ECHILD/release checks; the batch ended **21:53:44.672508 UTC**. See [batch-lock.json](batch-lock.json), [batch-result.json](batch-result.json), and [reconciliation.log](reconciliation.log).

The previous 5 GiB admission refusal and earlier runtime-stop attempts remain failures in their original evidence; this successful batch does not relabel them. Raw data and frozen source snapshots are preserved verbatim, including formatting. Publication-only failed offline edit/path-lookup diagnostics are recorded in [publication-notes.json](publication-notes.json).

Visible resource accounting remains **PARTIAL_VISIBLE_ANCESTORS; unseen limits UNKNOWN**. No new exhaustive owner/axiom audit, clean rebuild, coordinated full CI, or mathematical review was performed. Mathematical hypotheses remain those of the frozen source. No stronger provenance or whole-paper completion is claimed. No proof source, website, workflow, or older evidence was modified.

Both additive publication commits use `[skip ci]`. [PUBLICATION.json](PUBLICATION.json) identifies the result commit; [evidence-sha256.json](evidence-sha256.json) covers every checkpoint file except itself and bytecode. For read-only reconciliation, run `python3 -B checkpoints/light-eft-resume231-headroom45g-20261017/verify_publication.py` from the repository root; this runs no Lean or advice. Current resources and idle/free-lock checks are in [terminal-environment.json](terminal-environment.json). Paused for independent review of the 77 new chains.
