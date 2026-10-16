# LightEFT coverage reconciliation and blocked strict aggregate preparation

Coverage/source checkpoint: `0c3d4c62ecf5f74c85b6589a0300c999945b8688`.
Accepted proof source: `753ae06c2921597cb39cd72bde25bc99e13a71e5`.
Accepted proof evidence: `88fa6ea4990488c2d3af870283ba47d6b35fec85`.
Branch: `light-eft-spanners-checkpoints`.

**Outcome: coverage reconciled; strict full-aggregate preparation blocked; no clean CI triggered.** Existing proof source and strict warning policy were preserved. No aggregate, full replay, complete aggregate audit, clean-CI or whole-paper pass is claimed.

## Coverage reconciliation

[PROOF_COVERAGE.md](../../Light%20Edge%20Fault%20Tolerant%20Graph%20Spanners/PROOF_COVERAGE.md) maps the agreed main-result coverage to the actual accepted native endpoints. README now points to it; statement-map entries gain `current_native_coverage` addenda while every historical field is retained. The parent independently accepted all 122 residual-checkpoint manifest entries, 59 chunks, the native full-blocker sampling chain and square-root endpoint, all nine receipts and preservation. This records that review, not new reviewer execution or CI.

The native upper results now include exact-2f square-root dependence with coefficient `1+16 sqrt(f)(L+1)`, corrected numerical specialization with `9+2048/epsilon*n^(1/k)`, and rounded higher competition with the additive seed baseline. Finite original-ID native graphs, nonnegative weights, positive relevant parameters, actual input containment and zero-optimum treatment remain explicit. The corrected threshold is stretch+1; the documented printed-threshold defect is not retracted. Theorem 9/fixed-parameter lower-family scope and its uniformity qualifications are retained. Native deterministic existence is not a native randomized/runtime result. Theorem 34 remains a separate substantive open obligation. No source correction was silently broadened into whole-paper acceptance.

## Strict blocker and exact diagnostic

The full source-derived import closure has **486 modules**: 429 LightEFT leaves, 56 required LightSpanners support modules and the LightEFT aggregate. Every LightEFT leaf is reachable from the aggregate. `evidence/full-order.json` is its topological order and `evidence/source-graph.json` gives every path, source root and SHA256. These are read-only source checks, not compiler acceptance.

The accepted local object set covered 179 modules. The runner attempted the remaining 307 sequentially with official Lean and strict options. Eighteen additional modules compiled successfully. The nineteenth invocation stopped at the unchanged `LightEFTSpanners.TreePruning`:

```
Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/TreePruning.lean:12:21:
error: Variable name `hKG` is not explicitly referenced.
```

Its exact command was:

```
/workspace/toolchains/lean-4.34.0-linux/bin/lean -j1 -DautoImplicit=false -DwarningAsError=true --root=/workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners -o /workspace/light-eft-verification/.lake/build/lib/lean/LightEFTSpanners/TreePruning.olean /workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/TreePruning.lean
```

The authoritative argument array, including paths containing spaces, is in `evidence/commands.jsonl` and the UUID receipt. The unquoted command display above is explanatory, not a shell-ready invocation. Entry point used: `python checkpoints/light-eft-aggregate-20261016/run.py dependencies`.

Failed UUID: `e8692d341a9e42f0b445eea4129dfdd2`. Its submitted snapshot and complete raw log, including the compiler's hint, are preserved under `evidence/attempts`. This is an inherited unused-variable linter promoted to an error by `-DwarningAsError=true`; it is not a mathematical counterexample or kernel rejection. The warning-header count is zero because the strict diagnostic is an error. The hint is not counted again.

The compiler suggests an underscore binder or disabling the linter. Neither change was applied: accepted proof bytes were to be preserved and strict compilation was requested. A decision permitting a minimal linter-only source edit, or explicitly specifying a frozen inherited-diagnostic baseline policy, is needed before this strict full build can progress. Other blockers may exist after this first failure; they have not been ruled out.

The full aggregate itself was **not compiled**. No singleton replay set or complete recursive audit was run in this checkpoint, because the strict dependency closure was incomplete. Earlier bounded audits remain preserved and accepted only within their recorded scope. There is no new audit TSV or chunk set to mislabel as full-aggregate evidence.

## Supported CI flow and readiness

The repository's only current workflow is `.github/workflows/lean.yml`. It uses the ordinary push/PR/dispatch flow, a 120-minute job cap and broad all-paper build/index/audit/replay steps. `verification/CI_RESOURCE_120.md` documents why the previous cap was increased without dropping verification. `scripts/KernelCheck.sh` replays sequentially, but it enumerates all papers; `scripts/CheckModuleIndex.sh` also spans all papers. Those broad entry points are unsuitable for this LightEFT-only request and were not invoked.

A future clean gate needs a dedicated LightEFT-only job over the 486-module source-derived closure, frozen exact source, official toolchain and all nine dependency pins, official cache retrieval, sequential strict compilation, singleton replay of every leaf/support module, aggregate compilation, and complete actual-owner recursive type/body audit. The existing universal-lock/source-snapshot receipt supervisor is retained for that work. Local verification must be idle before CI starts, and normal push triggering must not also launch the multi-paper job. A dedicated workflow was planned, but **was not installed or triggered after the strict blocker appeared**. No incomplete or knowingly failing clean gate is presented as ready.

There is no access/credential/security blocker: ordinary remote reads succeeded. No API restrictions were bypassed, credentials added or settings changed. Source/evidence publication uses `[skip ci]` and an ordinary additive fast-forward on the existing authorized branch. No CI trigger commit was made, so there is no exact-commit CI run URL or result for this checkpoint.

## Preserved evidence and terminal state

Official unmodified Lean 4.34.0 at the accepted executable path was used. The toolchain executable/configuration hashes and all nine dependency revisions remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. This was incremental validation, not clean cache/bootstrap testing or a default Lake build.

Nineteen source-bound unique UUID receipts record 18 successful strict compilations and one failed strict compilation. Every invocation had a resource/process preflight and ran sequentially under the same universal exclusive lock, with submitted source SHA256/snapshot, child PID, UTC/monotonic timestamps and reaped child. No parallel worker or local/CI overlap occurred. Raw logs and the failed attempt are preserved.

`reconcile.py` runs only source/log/hash checks. It verifies every submitted snapshot against source checkpoint `0c3d4c62ecf5f74c85b6589a0300c999945b8688`, all 486 proof/aggregate source files unchanged from accepted parent evidence, all 179 reused object hashes plus 18 new successful objects (197 total), all 122 parent evidence manifest entries, all nine pins, receipt uniqueness, one lock inode, non-overlap and child reaping. Historical statement-map values also reconcile exactly after removing the new addenda.

`evidence/execution-reconciliation.json`, `evidence/source-object-hashes.json`, `evidence/toolchain-hashes.json` and the full UUID logs provide the exact evidence. `evidence-sha256.json` covers this report, scripts, graph/order, logs, receipts, snapshots and derived checks.

Initial checks found about 23 GiB disk free, a 16 GiB memory limit, no compiler/checker and a free lock; public repository CI statuses were all zero. Terminal evidence shows no compiler/checker and a free lock. No other project or completed/deleted workspace was reopened. Paused for independent review and resolution of the strict-source-preservation conflict; Theorem 34 and runtime claims remain excluded.
