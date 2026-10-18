# Joint flag-assignment law — mathematical draft only

**Unelaborated Lean draft and unexecuted interface/validation plan. No Lean, checker, common-lock probe/acquisition or accepted-module recompilation occurred.** Stop for independent mathematical review before an adapter or execution attempt.

The user reports independent qualified incremental acceptance of **`49f17551c0c092c9631f36e2108114cc83c8eebe`**. This is recorded as source/log/hash reconciliation, not fresh execution. The accepted **145,656-byte actual-output object**, SHA256 **`000a803f858c98d95c53b57011785f5c08fc687ee5af081161b595bd32974499`**, and all prior accepted objects/evidence are preserved unchanged. [Accepted preservation bindings](accepted-preservation-bindings.json) record the deterministic, probability and actual-output source/object identities. None is imported or recompiled in this minimal bridge.

## Proposed mathematical interface

[JointAssignmentLaw.lean](staged/LightEFTJointFlagSamplingStage/JointAssignmentLaw.lean) proposes **`LightEFTSpanners.JointFlagSampling.decoded_assignment_probability`**, plus exact map-law equality `decoded_assignment_law` and supporting product/decoder/schedule theorems. The distinct physical module is **`LightEFTJointFlagSamplingStage.JointAssignmentLaw`**.

Source: **11,312 bytes**, SHA256 **`ec9e696d0380e3bba0f58c8d5d2e81daab0d9f4c5e271d146a431eba03f6eaba`**. All supporting proofs are present as drafts, with no new axiom, admitted proof or coupling premise. **They have not been elaborated or checked.**

The joint flag cube has literal order

`candidate occurrence × host × repetition × original Sym2 identity`.

The source law is an explicit normalized finite product with coordinate probability `1/(2*f)`. It reuses `StoredFlagBatch.original_probability` and existing finite-product laws to show that the decoded assignment has **exactly `executionLaw`'s probability for every assignment event**. It introduces no new concentration argument.

The decoder initializes every candidate key to empty, recursively decodes the tail, and updates at the head. Repeated keys retain the leftmost occurrence's block; their occurrence coordinates still get independent draws. Values outside visited keys remain empty. The theorem works for arbitrary lists, without a nodup hypothesis, and includes empty candidates, vertices, hosts and repetition sets. Original identities include diagonals, matching the existing Bernoulli law; clipping is left downstream.

The exposed schedule traverses reversed occurrence indices, then all hosts, repetitions and original identities. Draft membership/nodup/length theorems give exactly

`l.length * Fintype.card J * m * Fintype.card (Sym2 (Fin n))`

coordinates. This counts the full mathematical table, including unused hosts/identities; it is **not** a charged sampler, bank serializer, efficient on-demand implementation or final runtime bound.

[Interface analysis](INTERFACE-ANALYSIS.md) explains exact definitions, argument order, all-event transport, duplicate/unvisited behavior, empty cases and remaining obligations. It identifies the small missing generic API steps—coordinatewise product pushforward, measure-batch singleton products and `Fin.cons` product splitting—and supplies their proof drafts instead of hiding them in a coupling hypothesis. [Source snapshots](interface-declarations.txt), [project bindings](interface-bindings.json) and [pinned mathlib API bindings](mathlib-interface-bindings.json) preserve the inspected contracts. Generic sum/measure API elaboration and dependent `Fin` recursion remain untested.

## Exact dependency scope and preservation

[Project dependency bindings](project-dependency-bindings.json) contain **77 existing frozen modules**: **70 LightEFTSpanners and 7 LightSpanners**. Their source hashes match the frozen graph and their existing objects match the prior protected input journal. No missing object was found or generated. [Readable closure export](project-closure-export/manifest.json) reconstructs all rows exactly. This is a source/module closure, not a fresh recursive declaration audit.

The only direct project imports are `StoredFlagBatchProbability` and `AdaptiveVotingConcentration`. Four explicit mathlib imports and three additional inspected mathlib APIs have source/object bindings; pinned `lean-toolchain` and `lake-manifest.json` remain unchanged. All transitive cache hashes retain their prior qualified inventory authority. No authenticated dependency-provenance or historical IR-signature claim is added.

[Metadata-only package prediction](package-layout-prediction.json) selects all 77 intended dependency paths and the new target. The proposed search order is fresh joint-law root, frozen project root, then unchanged library roots. All three accepted staged objects are preservation-only immutable inputs **outside the search path**, with no redundant import/compile/replay. Their exact hashes/identities must remain protected during any future execution.

## Unexecuted focused validation plan

[Focused plan](focused-validation-plan.json) and [planned commands](planned-commands.txt) bind the three staged sources, fresh work/evidence paths, full per-command environments and ordered submitted-source records. All commands have `executed=false`, the new object hash is null, and review-required draft/adapter commit slots remain unbound. No future work/evidence root was created. Existing adapters target different scopes and must not be used as-is.

A separately reviewed future adapter would run only bounded compile, exact singleton resolution, singleton kernel replay and focused audit for this new module. Preserve existing 3/3/4/4 GiB admission gates, runtime/output limits, process supervision, source/environment-bound UUID/PID/FD/timing/reaping receipts, first-failure stop and complete raw exports. No automatic retry or source promotion is proposed.

The [audit draft](staged/JointAssignmentLawAudit.lean) discovers **every actual-owner declaration**, including private/generated roots, and requires **16 named new theorems**. Future independent reconstruction must require exactly **78 project imports including the target across three prefixes**, all **eight imported interfaces**, complete recursive types/bodies/inductive/recursor links and standard axioms only. Actual new root/constant/opaque counts are **unknown** until execution. Only `propext`, `Classical.choice` and `Quot.sound` are allowed. The [resolver draft](staged/ResolveJointAssignmentLawTarget.lean) permits only the exact new singleton target.

The latest accepted historical release is pinned from `49f17551…`: epoch **`f9446665c62e4e5c90b1578b930dd6ec`**, **719 bytes**, SHA256 **`26141424860045dba7f6e2438abcf5615cef11b29b27b242ec24de5a9dc6e504`**, device/inode **33:3258**, directory `[33,1]`. Only its saved receipt was read. Fresh post-planning sole-worker/idle-reviewer coordination, unchanged freshness/current-facts gates and exact nonblocking inode reuse would still need separate authorization.

## Evidence and remaining work

[Preparation diagnostics](diagnostics/preparation-attempt-1.log) record one successful source/object/plan reconciliation pass; its exact script snapshot is preserved. [Draft bindings](draft-bindings.json) explicitly record zero Lean invocations/lock acquisitions and null object/replay/audit results. [Preservation record](preservation.json) retains all three accepted outputs and prior qualifications. A read-only exploratory filename lookup diagnostic is preserved separately; it was not a compiler or proof attempt.

The bridge proves only the proposed mathematical distribution interface if its draft validates. It does not supply the actual keyed-bank serialization path or remove seed/order/draw hypotheses from the accepted actual-output theorem. Charged sampling and serialization, seed approximation, packing and final runtime composition remain separate obligations. The finite full-table count is exposed without claiming it meets a final runtime target.

Publish this additive draft with `[skip ci]`, verify the exact remote commit, then remain idle for independent mathematical review. No Lean execution, accepted-object recompilation, source promotion, broad build, retrieval, SCC work, website change, clean-provenance claim or whole-paper completion occurred.
