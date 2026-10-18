# Encoded supplied-forest probability package — draft only

**Unelaborated Lean source and unexecuted validation plan. No Lean invocation, checker, common-lock probe/acquisition or accepted-object recompilation occurred.**

The user reports independent qualified incremental acceptance of probability evidence **`df18cdab7f15e5f377e6c72487e7beff6c5268e5`**, testing source `88d297fa58a15406aac6e7c0ea3c85f65965d19a` through adapter `b6483cccabdf4afdbb8004a768afe8ea9ed0ff32`. This preparation records that review as source/log/hash reconciliation, not fresh execution. The accepted **76,720-byte probability object**, SHA256 **`0716fe2cc66dd6657243cfe6d5d34fb83722f59818d0cdb1838be0bf2d981eeb`**, and the accepted deterministic object, SHA256 **`b5e18c2425b50a2b7008f2a5f9ab928f22daae1d530293d373691a0a378cbc18`**, remain at their original exact paths and identities, unchanged and not recompiled.

## Proposed theorem

[PolynomialActualFailureProbability.lean](staged/LightEFTActualSuppliedForestProbabilityStage/PolynomialActualFailureProbability.lean) declares

`LightEFTSpanners.StoredForestCandidates.polynomial_actual_supplied_forest_package_failure_probability`.

Its distinct physical top-level package is **`LightEFTActualSuppliedForestProbabilityStage`**. The source is **4,727 bytes**, SHA256 **`faee0b34bdb811a7a1f97f3e7bd90b2e7e37dd0a2967fbddb06c2483e0ec5b86`**. It has no placeholder proof, new axiom or admitted gap.

The proof first applies the existing `StoredForestCandidates.assignment_failure_le` to the **entire four-part predicate**: EFT correctness, raw weight bound, zero-weight implication and competitive-lightness bound. It then applies the accepted supplied-forest probability theorem. Both steps use the same supplied forest family, literal finite assignment law, repetition count and assignment tape. The bound is exactly `((n:ℝ)^s)⁻¹`.

The actual result is `OutputSatisfies` for the existing `StoredForestCandidates.execute`, using its literal encoded forest list, repeated seed arguments, rational weights/threshold and candidate records. Seed edge-set equality, the exact reversed candidate order, and every ordered bank-to-assignment draw equality remain explicit. Rational-to-real threshold/weight transport is exact. No concentration proof, sampler or serialization/runtime implementation is added.

[Interface and assumption analysis](INTERFACE-ANALYSIS.md) explains the exact argument order, implication direction, law/type identities, full predicate association, representation equalities, cast/simp steps and remaining hypotheses. [Interface snapshots](interface-declarations.txt) and [bindings](interface-bindings.json) identify the inspected source/object contracts. The proof's elaboration, implicit instances and local-let reductions remain **untested**.

## Dependencies and physical packages

[Project dependency bindings](project-dependency-bindings.json) contain **344 exact dependencies**: **342 frozen modules** (286 LightEFTSpanners, 56 LightSpanners) and **two accepted staged modules**. All previous 213 dependency bindings are preserved. The stored-output transfer brings in **130 additional preexisting frozen modules**; each source matches the frozen graph and each object matches its already protected input-inventory binding. No missing object was found or generated.

[Readable closure export](project-closure-export/manifest.json) reconstructs the complete dependency JSONL in ordered row-aligned chunks. This is source/import and object-byte reconciliation, **not a new declaration/axiom audit**. [Accepted theorem bindings](accepted-theorem-bindings.json) preserve both accepted modules and the earlier 51,084-constant probability audit export without rerunning it.

The future search order is fresh actual-output root, accepted probability root, accepted deterministic root, frozen project root, then unchanged library roots. [Metadata-only package prediction](package-layout-prediction.json) selects all 344 dependency paths and the new singleton target as intended. The new top-level package is distinct from both accepted staged packages and both legacy project packages. No future work/evidence directory was created and no accepted object was copied into an output/project cache.

## Focused future plan

[Focused validation plan](focused-validation-plan.json) binds the three exact Lean sources, fresh paths, per-command environments, full ordered submitted-source bindings and four unexecuted commands. [Planned commands](planned-commands.txt) are documentation, not an activation script. The existing adapters `b6483ccc` and `2d75404b` do not support this new target/344-dependency scope as-is. A separately reviewed executable adapter and later explicit execution authority remain necessary.

The proposed stages are bounded new-module compile, exact official singleton resolution, singleton kernel replay and focused audit. Existing resource limits, admission gates, accounting, process supervision, first-failure stop, source/environment-bound UUID receipts, package/shadow/link/sidecar checks and raw-evidence preservation must remain. No accepted theorem is to be recompiled. The two accepted outputs require exact immutable supplemental bindings, with no root whitelist or replacement of old cache hashes. The 130 extra frozen objects already belong to the protected inventory.

The [audit draft](staged/PolynomialActualSuppliedForestProbabilityAudit.lean) inventories every actual-owner declaration, requires the new theorem and traverses complete types/bodies/inductive/recursor links. The future independent reconstruction must require exactly **345 project imports** including the target, across **five prefixes**, and independently require all five named interfaces: the assignment transfer, accepted package probability theorem, deterministic good event, polynomial inaccuracy theorem and `Law.prob_mono`. Actual root/constant counts remain unknown until execution; the old 51,084 count is not reused as a new result. Only `propext`, `Classical.choice` and `Quot.sound` are allowed.

The latest accepted release receipt is pinned at **epoch `f8ff4af575274e8c9aec76c264ef7726`**, **718 bytes**, SHA256 **`f1cb1eb90fcaa82f55c84d2be396f561794e6b83096a9e3970e3424d0f9cf6ef`**, from evidence `df18cdab…`, device/inode **33:3258**, directory identity `[33,1]`. Only that historical receipt was read. Any future acquisition still needs fresh post-planning sole-worker/idle-reviewer coordination, the unchanged freshness/current-facts gates and explicit exact-inode reuse authority.

## Evidence and disposition

[Preparation diagnostics](diagnostics/preparation-attempt-1.log) record one successful Python-only binding/plan preparation pass; its exact script snapshot is preserved. No Lean fixture or proof test was run. [Draft bindings](draft-bindings.json) explicitly leave the new object, replay and audit results null, with zero Lean invocations and lock acquisitions. [Preservation record](preservation.json) records unchanged accepted objects, old bindings and provenance qualifications. Exploratory read-only navigation diagnostics are also preserved; they were not compiler or proof attempts.

The theorem retains the supplied forests and structural count/congestion certificates, FT-preserver input, positive parameters and rational weight conditions. Paid sampling/serialization, seed approximation, packing and final runtime composition remain open. The IR-signature supplement remains newly observed local evidence; authenticated dependency provenance, clean validation and whole-paper completion remain unclaimed.

Publish this additive draft with `[skip ci]`, verify the exact remote commit, then stop for independent mathematical/interface/plan review **before Lean**. No source promotion, automatic CI, retrieval, SCC or website work is performed.
