# Reproduction and evidence guide

All work was read-only against the frozen packet and production repository. Auditor files are isolated in this directory. No Git ref, proof source, shared dependency cache, live Site, or audience setting was changed.

## Integrity / remote reads

- `python prepare.py`: verifies all 416 frozen manifest entries and supplied handoff hash, reconciles all 284 archived Git blobs to candidate tree, checks working source equality, proves 116 mathematical files unchanged from parent and 112 unchanged from the prior audit target; prepares isolated import paths and checked-body audit code.
- GitHub connector GETs of candidate Git commit and runs 38182298230 / 38189023870, jobs, and terminal decoded job logs. Raw connector responses are retained in `raw/`. This was independent readback, not reuse of a prior verdict.
- `python check-dependencies.py`: hashes sources and imported oleans for the 1,748 modules in the checked type/body union, verifies dependency Git revisions against the nine manifest pins and source blobs against their pinned checkout objects.
- `python check-root-closures.py`: computes full type/body dependency closures for 32 mapped/additional roots and verifies no partial/unsafe dependencies and only the three allowed axioms.
- `pdftotext -layout <frozen source PDF> source-pdf.txt`: local source comparison; the public arXiv v4 PDF was separately opened and its identity, page count and main-claim text cross-checked. No claim of an independently downloaded bytewise PDF comparison is made.

## Local Lean checks

`source env.sh` selects Lean4.34.0 and the isolated fresh artifacts before the source-matched dependency cache. Every compiler/replay turn uses a nonblocking shared flock, one Lean thread, and at most55seconds; batches stop starting work before their window expires. A busy lock defers work without starting a compiler.

- `run-fresh-batch.sh <modules...>`: `lean -j1 -DautoImplicit=false -o <auditor artifact> <frozen module source>`. Selected fresh source checks are listed by exact result and timestamp in `raw/fresh-batch-*.log`; diagnostics are `raw/fresh-<module>.log`.
- `lean -j1 -DautoImplicit=false AuditFrozen.lean`: inventories by defining module, invokes collectAxioms, then separately traverses `env.checked` ConstantInfo types and bodies. It rejects custom axioms/unsafe constants and records generated partials for closure analysis. All 116 production modules are explicitly imported from the frozen root enumeration.
- `lean -j1 -DautoImplicit=false Statements.lean`: prints underlying distance, route, tree, extremal, rigidity, weight and obstacle-input definitions plus auxiliary theorem types.
- `lean -j1 -DautoImplicit=false Nonvacuity.lean`: reruns the inspected supplementary finite/eventual nonvacuity proof for the corrected terminal cap.
- `run-replay-batch.sh <modules...>`: official `leanchecker -j1 -DautoImplicit=false -v LinearDistancePreservers.<module>` against the audited artifacts.
- `lean -j1 --run ReplayClosure.lean <module> <root>`: recursively collects the checked type/body dependencies of the named theorem, rejects every partial/unsafe/nonstandard axiom, and uses the official Lean.Replay implementation to replay into an empty kernel environment. This is stronger than ordinary module mode with imported dependencies already trusted.

The replay driver is an executable audit tool and is marked unsafe only to use the import/environment IO APIs. It is not imported by any mathematical module or proof. The dependencies it sends to the kernel are explicitly rejected if unsafe or partial.

## Companion tests

`python check-companion.py` verifies byte-preservation outside marker blocks, the original ten placements, all95 assets, updated dp-1 weight baseline, two additional notes and exact agreement with the authoritative plan. It makes auditor-local copies of the test harnesses that read frozen inputs and write output only here.

`node check-dom.cjs`, `node check-diagrams.cjs`, `node check-markers.cjs` rerun the candidate DOM tests, nine diagram checks and432 marker interaction groups. These do not claim browser-pixel QA or live deployment verification.

## Limitations and unsuccessful setup attempts

Tooling setup/import-path errors and bounded-window deferrals are retained in `raw/tooling-adjustments.log`, the initial statement-print error and relevant logs. They were not mathematical proof failures. No failing mathematical check was silently treated as passed. No full local rebuild of all116 sources or all mathlib was performed. Full exact-commit CI supplies the exhaustive source build/index/declaration/module-replay gate; selected fresh local elaboration and a full theorem closure replay are independent supplements. The other three papers in the shared repository are outside this semantic audit.
