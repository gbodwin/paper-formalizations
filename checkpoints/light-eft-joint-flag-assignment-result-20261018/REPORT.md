# Joint-flag validation — compilation failed, no retry

The **one authorized attempt stopped at compilation with exit 1**. Exact resolution, singleton kernel replay and focused audit were **not run**. No new `.olean` or audit result was produced. The source and reviewed adapter remain unchanged. This checkpoint preserves failure evidence for independent review; it claims no joint-law theorem acceptance.

Tested source commit: **`33e162e467cea919ee60d2c17e1f13d8586caba3`**. Reviewed implementation: **`41f4e793e8d56f754c152964b5af9c2445f2706e`**. Target: `LightEFTJointFlagSamplingStage.JointAssignmentLaw`. The 11,312-byte submitted source retains SHA256 **`ec9e696d0380e3bba0f58c8d5d2e81daab0d9f4c5e271d146a431eba03f6eaba`**; its exact executed-byte snapshot is in the compile evidence. The resolver/audit sources were protected inputs but were not executed.

## Exact failure and diagnostic classification

The [complete raw compiler log](../light-eft-joint-flag-assignment-draft-20261018/future-validation-evidence/compile/raw.log) is preserved unchanged. [Diagnostic classification](diagnostic-classification.json) counts anchored source/line/column severity headers, including coded `error(lean.invalidField)`. Notes, suggested fixes, allocator output and occurrences of words inside hints are not counted again.

There are **13 error diagnostics**: **four elaboration/proof-goal errors** and **nine linter diagnostics emitted as errors under `-DwarningAsError=true`**. There are zero unpromoted warning headers.

| Source location | Classification | Diagnostic |
|---|---|---|
| 45:2 | Elaboration | `change` pattern is not definitionally equal to the product/map mass target. |
| 81:44 | Elaboration | Dependent `Fin.cons` expression does not elaborate at expected type `α`. |
| 116:42 | Elaboration | Invalid `.product` projection from the pairwise/reverse expression. |
| 127:71 | Proof goal | Sampling-schedule length goal remains unsolved. |
| 119:0, 148:0, 159:0, 164:0 | Promoted linter, four headers | Unused automatically included section variables. A header listing two variables is counted once. |
| 128:31, 128:52, 129:4, 129:26, 129:48 | Promoted linter, five headers | Unused simp arguments in the schedule-length proof. |

These are the observed blockers under the reviewed source, toolchain and strict options. The run does not establish acceptance or a mathematical counterexample. No proof repair, linter suppression, option change or compiler retry was attempted.

## One executed stage and skipped checks

Compile UUID: **`050a7b27876244ea9d117d9de7502b50`**. Child PID: **12584**. Supervisor PID: **12296**. The [raw source-bound receipt](../light-eft-joint-flag-assignment-draft-20261018/future-validation-evidence/compile/receipt.json) records `state=failed`, `exit=1`, the nonzero owned terminal status, matched waitid/wait4 status, direct/adopted child reaping and kernel no-children verification. It has no cleanup error or memory-stop decision.

The official pinned **Lean 4.34.0** compiler ran with **`-j1 -s65536 -M5120 -DautoImplicit=false -DwarningAsError=true`**, exact reviewed `--root`, fresh `-o` and source path. No extra compiler/version/checker probe or runtime shim was used. [Commands](commands.json) and [execution summary](execution-summary.json) retain every exact argv, environment, cwd, submitted source identity/hash and stage status. Only compile has `executed=true`; later stages are explicitly skipped after first failure. The driver appends only successful stages to its batch list, so its empty `stages` array does not mean the compiler was never launched.

No individual kernel replay result, actual-owner inventory, 16-root check, eight-interface reachability result, 78-import audit or recursive axiom closure exists for this source. Those remain planned checks. No counts from a prior accepted module or from synthetic fixtures are substituted. [Work-tree evidence](work-tree.json) records zero produced files; the empty partial-artifact binding list is preserved.

All runtime limits and the compile **3 GiB** admission gate were retained. The unchanged plan's later 3/4/4 GiB gates were not exercised because their stages did not launch. Kernel readback verifies 12 GiB address space, 60 seconds CPU, 16 MiB file size and zero core size; the 90-second child wall deadline was satisfied. Pre-exec visible headroom was **7,520,661,504 bytes**; disk admission/pre-exec free space were **4,043,878,400 / 4,043,808,768 bytes**. Wait4 max RSS was **3,400,224 KiB**, sampled peak RSS **3,482,193,920 bytes**, sampled peak VM **6,364,467,200 bytes**. Sampled values are not continuous heap/VM caps. Raw resource decisions and limits remain in receipt/samples; no resource control was weakened.

## Preservation and clean release

The 77 dependency bindings and all protected inputs passed the adapter's post-child preservation check. All three accepted staged source/object pairs remain at their exact original contents and identities, outside the new search roots:

- Deterministic object, 185,576 bytes: `b5e18c2425b50a2b7008f2a5f9ab928f22daae1d530293d373691a0a378cbc18`.
- Probability object, 76,720 bytes: `0716fe2cc66dd6657243cfe6d5d34fb83722f59818d0cdb1838be0bf2d981eeb`.
- Actual-output object, 145,656 bytes: `000a803f858c98d95c53b57011785f5c08fc687ee5af081161b595bd32974499`.

None of these three staged modules was imported, recompiled or replayed by this bridge attempt. Prior accepted source/evidence, pins and signature classification remain unchanged. Supplied independent reviews remain source/log/hash review records, not fresh execution here. The inherited signature qualification remains newly observed local evidence without authenticated dependency provenance or new historical-preservation claims.

Planning finished before [fresh coordination](fresh-post-planning-coordination.json). The adapter authenticated the prior released epoch `f9446665c62e4e5c90b1578b930dd6ec`, its 719-byte receipt SHA256 `26141424860045dba7f6e2438abcf5615cef11b29b27b242ec24de5a9dc6e504`, and nonblockingly reused only **device/inode 33:3258**, directory `[33,1]`.

This failed attempt's new lease epoch is **`9dd0d7e576bc4fb7b7fa05d4413d4bff`**. Its [released receipt](../light-eft-joint-flag-assignment-draft-20261018/future-validation-evidence/lease.json) is **719 bytes**, SHA256 **`06054c674a4566e9b344b7fd4c4c12f646c1c2a7a6b74b315538ef4d34e21aa1`**, with `state=released`, `kernel_echild=true` and no release error. This records clean ownership release after a failed proof compilation, not theorem acceptance. The failed child interval lies wholly inside the lease. [Final idle evidence](final-idle.json) and [process listing](final-idle-processes.txt) confirm no compiler/checker/extractor/tracer remains running.

## Complete available exports and disposition

The [available-export index](available-export-index.json) covers **all nine raw runtime evidence files**, including the exact source snapshot, raw log, receipt, decision samples, canonical inputs, initial excluded metadata, lease and failed batch/result records. All **nine manifests / 211 ordered chunks** reconstruct their original bytes exactly. No audit or final-audit export is invented for a skipped stage. The complete originals remain under [runtime evidence](../light-eft-joint-flag-assignment-draft-20261018/future-validation-evidence/), with readable copies under [available-exports](available-exports/).

[Failure preservation script](preserve-failure.py) and [raw postprocessing output](preserve-failure-attempt-1.log) preserve the reconciliation procedure. Postprocessing only compared/copied/hashed existing evidence and used the unchanged chunk exporter; no Lean/checker, resource admission rerun or common-lock acquisition occurred after release. All failed diagnostics and prior partials remain preserved.

Publish this additive failure checkpoint with `[skip ci]`, verify the exact remote hash and stop for independent result review. The genuine remaining blocker is source elaboration under the reviewed strict toolchain. Charged sampling/serialization, seed approximation, packing, final runtime composition, authenticated provenance and whole-paper requirements remain open/qualified. No source promotion, repair, accepted-object recompilation, broad rebuild, retrieval, SCC or website change occurred.
