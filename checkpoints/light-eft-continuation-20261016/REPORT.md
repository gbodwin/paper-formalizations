# Light Edge Fault Tolerant Graph Spanners: bounded threshold checkpoint

Tested source: `7e4c0a730d13655fc75a4629dd4056a21a9a7cce`. Preserved parent: `faaaad5a31de3fef117f023154405ea21f2af1aa` on `light-eft-spanners-checkpoints`. This is a bounded additive checkpoint awaiting independent review, not whole-paper acceptance.

## Recovered scope and gate

The exact parent's verification/CHECKPOINT.md describes 398 modules, literal Bernoulli filtering and independent repeated-draw controllers, while retaining a stale “latest fully verified 353” assembly note. Saved GitHub run and job metadata reconcile that note: [run 38338948024](https://github.com/gbodwin/paper-formalizations/actions/runs/38338948024), job 115105368002, succeeded on the exact parent, completing 2026-10-13 04:20:35 UTC. This is reconciliation of recorded CI metadata, not fresh execution or artifact reconstruction. Parent remote remains at the exact preserved commit.

The mathematical scope includes corrected exact-extremal upper bounds for finite undirected simple graphs with nonnegative real weights, positive actual-edge weights where required, positive parameter hypotheses and explicit denominator conventions. Later controller results use the original finite assignment law and retain their stated seed/forest and representation hypotheses. Historical open lists are not all current: later checkpoints close several sampling/output joins. Optional physical bit runtime and random-generation extensions were not pursued here.

Theorem 34's claimed lower-denominator/lightness scaling remains open; so does the weighted-multigraph main extension. The exact tree-blowup certificate obstruction does not by itself refute every possible replacement construction. No new false-paper-statement claim is made. This checkpoint's missing gate is independent review of the bounded addition and its evidence; no full 399-module CI is claimed.

## Bounded preserved partial

BlowupCertificateThreshold joins two existing results: LargeCloudCertificate's sufficiency and GenericBlowupFailure's complete-base obstruction. For any nonempty finite cloud I, any complete base of order n >= 3, any tree T on that base, and any natural fault budget q, the lifted tree is a q-fault connectivity certificate iff q < |I|. Thus q+1 copies suffice, and q copies fail for q > 0. The equivalence includes q=0. These are three theorem statements; the audit covers four owned declarations including generated support.

This characterizes that certificate family only. It does not establish the original square-root-cloud scaling, a weighted lower bound, Theorem 34, the multigraph extension or the whole paper.

All 398 original mathematical sources match the preserved manifest byte-for-byte. The aggregate adds exactly one import (399 modules). Existing partials and historical documentation remain preserved. source-reconciliation.json records all current source hashes.

## Failed and superseded attempts

An initial weaker 2q+1 certificate draft overlooked the already present stronger q+1 theorem and temporarily replaced LargeCloudCertificate locally. It was never pushed. The original file was restored byte-for-byte and strictly recompiled; the redundant draft is preserved under drafts/RedundantLargeCloudCertificate.lean, and its raw source-bound attempts remain in evidence. Local archival branch archive/light-eft-redundant-draft-20261016 retains the superseded local commit. The final source commit is directly additive to the preserved parent.

The first threshold compile failed due to a missing explicit type binder under autoImplicit=false and proof-valued letI style errors under warningAsError. Its UUID is ed2d7a5c6c874c918397f5c7d885c187. Raw diagnostics and submitted source remain intact. No admitted proof is present in the final source. execution-reconciliation.json explicitly distinguishes three superseded-source receipts from final-source validation.

## Sequential validation

Official Lean 4.34.0, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b, Release. All nine dependency revisions match lake-manifest.json, including mathlib 5ed2965256430c3649e86755f9576b54eca72435. Binary, pin, source and object hashes are retained. No runtime shim, default Lake build, parallel worker, dependency update or new CI was used.

Commands are recorded verbatim in every UUID receipt, including executable, options, environment and submitted-source hashes. Entry points: `python3 checkpoints/light-eft-continuation-20261016/run.py compile`, `replay`, and `audit`. Final target compilation and audit use `-j1 -DautoImplicit=false -DwarningAsError=true`; target compilation emits zero diagnostics. Six unchanged dependencies were compiled with autoImplicit=false; the restored LargeCloudCertificate was compiled strictly. The two inherited GenericBlowupFailure warning headers are “Try this” tactic suggestions, not axioms or admissions. Hint occurrences are not counted again.

Final individual official `leanchecker -v MODULE` replay passed for all eight modules listed in evidence/dependency-order.json: four LightSpanners support modules and LightEFTSpanners.Basic, GenericBlowupFailure, restored LargeCloudCertificate, and BlowupCertificateThreshold. Each raw replay log is preserved.

The strict recursive audit passed: 117 actual-owner project roots, four owned declarations covered for the addition, 14953 recursive constants, 13 opaque bodies. It traverses types and bodies, rejects unsafe/partial declarations and unapproved axioms, and found only propext, Classical.choice and Quot.sound. This covers the loaded eight-module project closure, not all 399 modules. Full raw TSV and 29 ordered chunks are preserved; audit-export/manifest.json specifies reconstruction and hashes.

There are 27 historical locked invocations in this packet: one version probe, ten compilation attempts (including one failure and the superseded draft), fifteen replays (seven preliminary, eight final), and one final audit. Reconciliation verifies unique UUIDs, a single universal lock inode, nonoverlap, all children reaped, and every submitted snapshot hash. Raw logs are never discarded. The convenience semantic log filenames may describe the latest attempt; UUID directories are authoritative.

At handoff the universal lock is free and no compiler/checker is running. Capacity is approximately 23 GiB disk free, 16 GiB memory limit, and four CPUs. Source and evidence are pushed only to the additive checkpoint branch with CI skipped. Pause for independent review; no acceptance claim.
