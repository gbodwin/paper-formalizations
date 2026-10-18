# Supplied-forest probability package — executed checkpoint

The one authorized sequential validation **passed all reviewed adapter gates**: compilation, exact resolution, singleton kernel replay and focused audit each exited 0. This is execution evidence awaiting independent result review. No source promotion or whole-paper completion is claimed.

The tested immutable draft is **`88d297fa58a15406aac6e7c0ea3c85f65965d19a`**; the approved adapter implementation is **`b6483cccabdf4afdbb8004a768afe8ea9ed0ff32`**. The frozen project imports retain source authority **`78cb40c7837db049d645d73696f2e0b724ce8a3b`**. Independent approval of the draft and adapter is recorded as supplied review, not fresh execution of their earlier evidence. This checkpoint performs the newly authorized execution only.

## Tested statement and hashes

The sole new module is `LightEFTSuppliedForestProbabilityStage.PolynomialFailureProbability`, with theorem `LightEFTSpanners.SampledGreedy.polynomial_supplied_forest_package_failure_probability`. Its 3,378-byte source has SHA256 **`e1db9fb7e7b70d6287eee4df38d231fd882efd08ab8b29da0d7313c6ac4621fc`**. The 4,532-byte audit source has SHA256 `bf118b8a15541d2fc7e00fafeac19c857e61b1587adad487f87283b039130500`; the 1,403-byte resolver source has SHA256 `b40c00f2e5d91d6c3f2cf1eb53a21e014d060599d8225f9f793fb364d0d18661`.

The resulting **76,720-byte object** has SHA256 **`0716fe2cc66dd6657243cfe6d5d34fb83722f59818d0cdb1838be0bf2d981eeb`**. Its exact bytes are preserved under [artifacts](artifacts/objects/LightEFTSuppliedForestProbabilityStage/PolynomialFailureProbability.olean). [Artifact bindings](artifact-bindings.json) connect the copies to original runtime paths and hashes. The original object and raw runtime files remain in the fresh work root.

The accepted supplied-forest object was an immutable dependency, with SHA256 **`b5e18c2425b50a2b7008f2a5f9ab928f22daae1d530293d373691a0a378cbc18`**, 185,576 bytes. Its exact content and identity were preserved throughout; it was **not recompiled**. All 213 dependency source/object bindings and the protected prior input inventory remained unchanged. The original draft sources and all reviewed adapter helpers are unchanged.

## Commands, receipts and sequence

Toolchain: pinned **`leanprover/lean4:v4.34.0`**, binaries at `/workspace/toolchains/lean-4.34.0-linux/bin`. The bound `lean` binary SHA256 is `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`; `leanchecker` is `ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe`. No additional version/compiler probe or runtime shim was used. All transitive runtime/library bindings are preserved in the original [input inventory](../light-eft-supplied-forest-probability-draft-20261018/future-validation-evidence/input-export/manifest.json).

The Lean commands retain `-j1 -s65536 -M5120 -DautoImplicit=false -DwarningAsError=true`; compilation also has the exact reviewed `--root` and fresh `-o` target. Replay invokes official `leanchecker` for the **single new module**, with reviewed thread/stack environment. [Execution summary](execution-summary.json) contains every exact argv, cwd, environment, source hash/identity and kernel-limit readback. Each raw receipt independently contains those bindings. Compile/resolve/replay/audit submitted respectively 1/2/1/2 reviewed source records. The source environment is draft `88d297fa…`, and the harness environment is implementation `b6483ccc…`.

| Stage | Unique attempt | PID | Exit | wait4 max RSS, KiB |
|---|---|---:|---:|---:|
| Compile | `968d1b3498b24dc5826e82c988991e1f` | 8490 | 0 | 3426052 |
| Exact resolve | `5dd54e91b39b489998ead8214d1c3a9b` | 8528 | 0 | 900776 |
| Singleton replay | `7eb3a38205bb4c72a2f792964560f2b6` | 8578 | 0 | 2999804 |
| Focused audit | `3acc33b23a354baaa33234af078095d0` | 8624 | 0 | 3550884 |

There was one invocation and no retry or failed compiler attempt. Full raw diagnostics, decision samples, submitted-source snapshots, exit/reaping records and resource decisions are preserved at [runtime evidence](../light-eft-supplied-forest-probability-draft-20261018/future-validation-evidence/). Readable receipt/sample chunks are under [receipt-exports](receipt-exports/). The exact resolution JSON is preserved in [artifacts/resolution.json](artifacts/resolution.json); it resolves exactly the expected fresh object and no other target. Replay's raw log announces only the new module, and the receipt verifies exit 0, matching waitid/wait4 status, reaping and kernel ECHILD.

The existing process supervision, resource limits, visible/host admission gates, package/shadow checks, exact dependency checks, first-failure stop and output guards were retained. The kernel handshake verifies 12 GiB address space, 60 seconds CPU, zero core size and file-size limits of 16 MiB (64 MiB for audit). The child wall deadline remains 90 seconds. Receipt spans also include preservation work and must not be interpreted as child execution duration. Runtime RSS measurements are sampled, not continuous heap caps.

At pre-exec, visible headroom was at least **8,085,594,112 bytes** across all four stages; the recorded visible cgroup limit was **17,179,869,184 bytes**. Per-stage disk admission was at least **4,470,665,216 bytes**. Raw accounting identities, OOM counters, host decisions and limits are in receipts/samples; no resource limits were raised. Final [idle evidence](final-idle.json) and [process listing](final-idle-processes.txt) show no active compiler/checker/extractor/tracer.

## Lock and ownership

Read-only planning completed before the [fresh coordination document](fresh-post-planning-coordination.json) was issued. The adapter authenticated the latest released receipt from `7eedd5b3c7860cf473f5deff3b4ed369f19e6e61`, SHA256 `e4b4b0ea64888fbc9c04afd3026870227a82af1cb335031ef4552fe9629815d1`, prior epoch `7d164441f8ac44d9b9c316cdd79869f3`.

It reused only the exact existing common lock **device/inode 33:3258**, directory identity `[33,1]`, with the reviewed nonblocking acquisition and FD/path/directory checks. This run's ownership epoch is **`f8ff4af575274e8c9aec76c264ef7726`**, supervisor PID 8193. [Released lease receipt](../light-eft-supplied-forest-probability-draft-20261018/future-validation-evidence/lease.json) records `state=released`, `kernel_echild=true` and no historical-continuity claim. The four source-bound attempt intervals are strictly ordered and wholly inside this lease. Every child was reaped before proceeding; final receipt reconciliation passed.

The intermediate `batch-under-lease.json` deliberately records `accepted=false`: it was written before release and final receipt reconciliation. Final `result.json` records the adapter's gate result `accepted=true`; this does **not** substitute for independent result review.

## Recursive audit and diagnostics

The audit covers the **one actual-owner declaration** in the new module and its complete recursive type/body closure: **51,084 constants and 44 opaque bodies**. It reports exactly **214 project imports**: the 213 dependencies plus the new target, across all four approved namespaces. Independent Python reconstruction passed exact ownership, import-set, closure reachability, safe/nonpartial and axiom checks, with **zero strict findings**. The only axioms are **`propext`, `Classical.choice`, `Quot.sound`**. See [audit summary](audit-summary.json).

Each of the three required interfaces is independently present in the reconstructed reachable closure: supplied-forest deterministic good event, `polynomial_inaccurate_probability`, and `FiniteProbability.Law.prob_mono`. Their exact exported rows are in [required-interface-rows.json](required-interface-rows.json).

There are **zero Lean warnings and zero Lean errors** in each of the four raw logs, using anchored diagnostic-line classification. Allocator option/statistics output, the replay announcement and audit PASS text are informational. No raw diagnostics were removed or rewritten. [Audit raw diagnostics](../light-eft-supplied-forest-probability-draft-20261018/future-validation-evidence/audit/raw.log) and all earlier preparation/synthetic failures remain preserved in their original checkpoints.

The recursive TSV is **33,664,860 bytes**, SHA256 **`d7a48b230dfb85a625faa20f50f8606f37e00e77df94a81a9971414fb045a4ab`**. Its [ordered 170-part export](../light-eft-supplied-forest-probability-draft-20261018/future-validation-evidence/exports/recursive-dependencies.tsv/manifest.json) reconstructs byte-for-byte. All 16 chunk manifests, **518 chunks total**, including input inventories, excluded metadata, receipts and samples, were reconstructed and hashed against their untouched originals. [Chunk index](chunk-index.json) provides exact source lengths/hashes and ordered manifest locations. The raw TSV and all six generated artifacts are copied intact under [artifacts](artifacts/).

## Scope and remaining hypotheses

The theorem bounds failure of the full four-part supplied-forest package by `((n:ℝ)^s)⁻¹`, using the same supplied family `F`, literal finite `executionLaw` and `assignmentTape`. It combines event containment with the existing polynomial inaccuracy bound. It preserves the explicit FT-connectivity preserver premise on `Q`, the acyclic supplied forests inside `Q`, eligibility/count and congestion hypotheses, positivity of `f,h,k,eps`, nonnegative weights and positive input-edge weights. No forest/seed/packing construction or new sampling implementation is supplied here; those premises are not discharged by this probability wrapper.

The inherited IR-signature supplement remains **newly observed local evidence**, without historical-preservation or authenticated dependency-provenance claims. Broader clean provenance, source promotion and whole-paper completion remain unclaimed. There was no retrieval, accepted-object recompilation, broader rebuild, automatic retry, SCC work or website change. Publication uses `[skip ci]`, followed by exact remote-hash verification and an idle pause for independent result review.
