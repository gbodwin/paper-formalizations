# Exact-source CI gate preparation

Status: prepared and statically checked, NOT TRIGGERED; no CI pass is claimed.

Integration branch: `integration/conditional-plus6-ci-20261015`. The candidate/evidence branch and certified branch remain unchanged. [Independent review record](INDEPENDENT_REVIEW.md) preserves the coordinator's bounded-review report, not a fresh compiler run.

## Why scoped CI changes are needed

Existing lean.yml enables the default multi-paper build, all-paper audit and replay. Existing slack-sparsification.yml calls `lake build SlackSparsification`, which does not enforce one compiler process at a time and does not apply the requested per-module warning policy. Neither is the requested gate.

The integration branch adds `.github/workflows/conditional-plus6.yml` and `scripts/ConditionalPlusSixCI.py`. Its lean.yml skips the general job only for this integration branch (including a possible PR from that branch); other branch behavior remains intact. The new gate is push-only on this exact integration branch, has one job and no matrix, and uses a single-worker concurrency group. No workflow on the certified branch is edited.

The gate first fails closed if GitHub lists any other queued/running/pending/waiting/requested repository workflow. This prevents starting alongside an existing CI job but cannot prevent a separately triggered legacy workflow on another branch from starting later. The coordinator must retain the sole-worker slot for the entire run and keep local Lean work idle. No unrelated CI should be triggered during this gate.

## Exact source and sequence

The workflow checks out the integration CI definition, then independently checks out immutable tested source `d0f9ee2364bf4a5aaa7e0ca4da48216e42bbc63e` into `source/`. Its source receipt validates all 165 manifest entries by size, SHA256 and Git blob identity. Workflow/script edits are therefore never substituted into tested mathematical source.

It downloads the official Lean 4.34.0 release archive and verifies the independently confirmed SHA256. Each of nine dependencies is cloned/checked out sequentially at the manifest revision. To avoid Lake's parallel build scheduler even during cache setup, the gate compiles only the official cache tool's dependency closure sequentially, then invokes official `Cache/Main.lean` via `lake env lean -j1 --run ... get`. This bootstrap path is prepared but has not been exercised here; any failure is retained and fails CI rather than silently using a shim or alternate toolchain.

Project compilation then follows the previously tested 28-entry order: 23 inherited modules with autoImplicit=false/default linters; four new modules and the import-only aggregate with warningAsError=true. Inherited raw warnings must match reviewed diagnostics after normalizing only the absolute source root. Each of 27 exact leaf objects is replayed separately with the official checker, followed by the unchanged recursive audit. Sources and pins are checked again after execution. There is no default Lake build, aggregate-prefix replay, matrix, or subprocess parallelism in the runner.

The always-run artifact upload preserves command arrays, return codes, timings, raw logs, source/object hashes, diagnostic classifications and audit TSVs, even on failure. The workflow commit and separately tested source commit are recorded distinctly.

## Trigger/observability blocker

On 2026-10-15, `gh auth status` reported that GH_TOKEN could not authenticate, and `gh run list --repo gbodwin/paper-formalizations ...` failed with Forbidden against api.github.com. No token values were printed or saved. The available connector's commit-workflow wrapper explicitly filters to pull-request-triggered runs and cannot establish repository-wide active jobs or observe this push-triggered gate reliably.

Therefore this preparation is published with `[skip ci]`, and no job is intentionally triggered. An authorized GitHub Actions status/dispatch connection is needed to establish the single-worker slot, trigger the next integration commit without a skip marker, and obtain the exact workflow commit/run result. Do not treat preparation, skipped checks, or the earlier local pass as a CI pass.

Static verification performed: Python AST parsing, workflow YAML parsing when available, exact source/pin preservation outside the three scoped CI files, and branch/diff inspection. No local compiler or checker was started. No website changes or paper-completion claim.
