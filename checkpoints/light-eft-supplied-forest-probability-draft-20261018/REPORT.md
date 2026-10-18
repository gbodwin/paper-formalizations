# Supplied-forest full-package probability lemma — draft only

**Unelaborated Lean draft, prepared for independent mathematical/interface/plan review. No Lean, checker, lock acquisition, activation or fixture run occurred.**

The user reports independent acceptance of `7eedd5b3c7860cf473f5deff3b4ed369f19e6e61` as qualified incremental verification of the exact supplied-forest theorem. That acceptance is recorded here as independent source/log/hash review, not a fresh execution. The accepted object remains at its original path with SHA256 **`b5e18c2425b50a2b7008f2a5f9ab928f22daae1d530293d373691a0a378cbc18`**; it was read for binding, never recompiled, moved into a project cache, or promoted.

## Proposed lemma and proof

[PolynomialFailureProbability.lean](staged/LightEFTSuppliedForestProbabilityStage/PolynomialFailureProbability.lean) declares only

`LightEFTSpanners.SampledGreedy.polynomial_supplied_forest_package_failure_probability`.

Physical module: **`LightEFTSuppliedForestProbabilityStage.PolynomialFailureProbability`**.
Draft source: **3,378 bytes**, SHA256 **`e1db9fb7e7b70d6287eee4df38d231fd882efd08ab8b29da0d7313c6ac4621fc`**.

The conclusion bounds failure of the complete conjunction—EFT correctness, raw weight bound, zero-weight consequence, and competitive-lightness ratio—under the existing literal `executionLaw`, using `polynomialRepetitions n s` and the same `assignmentTape a`. The bound is the existing API's **`((n : ℝ)^s)⁻¹`**, retaining its totalized n=0/s=0 conventions.

The new premise is **`IsFTConnectivityPreserver G Q q`**, with the same q indexing **the supplied F**. Its `.1` supplies `Q ≤ G` to the accepted deterministic theorem. All forest, eligibility, congestion, threshold and weight hypotheses remain explicit; no `AccurateTrace` premise appears in the new theorem interface.

The proof uses precisely this pointwise inclusion:

`failure of the full package → trace inaccuracy`.

For each assignment a, the accepted theorem applied to `assignmentTape a` turns accuracy into the full four-part package. `Law.prob_mono` transfers that inclusion under the exact same law; `polynomial_inaccurate_probability` supplies the existing concentration bound. There is no new sampling proof, replacement forest, change of law, executable-output correspondence, ratio-only shortcut, or factor-four union bound.

[INTERFACE-ANALYSIS.md](INTERFACE-ANALYSIS.md) gives the exact argument order, law/assignment/tape/input identities, implication direction, assumptions, zero/small-n handling and remaining scope. [Source interface snapshots](interface-declarations.txt) and [source/object interface bindings](interface-bindings.json) identify the inspected declarations. They are source-level analysis, **not fresh Lean environment queries**. The explicit `hmono` fixes the intermediate event; future elaboration must still confirm implicit instances and the definitional reductions of the local t/B/law/output lets.

## Dependency and package bindings

[project-dependency-bindings.json](project-dependency-bindings.json) binds the exact source/object paths, bytes and hashes of **213** project dependencies:

- **212 frozen project modules**, preserving every prior 196 binding and adding 16 existing concentration-framework modules;
- the **accepted staged supplied-forest module**, with its original b5e18c… object binding and qualified acceptance reference.

All 212 existing object hashes match their prior protected inventory rows, and their source hashes match the frozen source graph. The accepted staged object matches the exact accepted hash above. No missing object was found and none was generated. [Readable closure export](project-closure-export/manifest.json) has two ordered row-aligned chunks of these bindings. This source/module import closure is **not** a newly executed declaration/axiom closure.

[accepted-theorem-binding.json](accepted-theorem-binding.json) preserves its exact source, object and existing 22,362-constant audit export (SHA256 `a3bf42e240b49ddfd17a6566f5b51b546c465de25a4441a3a701c168298e4260`). That prior closure was only hashed, not rerun. A future audit of the new lemma must compute its own closure and counts.

The new physical top-level package differs from both `LightEFTSuppliedForestStage` and the legacy `LightEFTSpanners`/`LightSpanners` packages. Proposed search order is: fresh probability output root, existing accepted supplied-forest object root, existing frozen-project root, then the unchanged library roots. [Metadata-only package prediction](package-layout-prediction.json) selects all 213 existing dependency paths and the new target exactly as intended, without creating the future output root. No accepted object is copied into that output root.

## Focused validation plan, not an executable adapter

[focused-validation-plan.json](focused-validation-plan.json) supplies exact source/audit/resolver bindings, four unexecuted argv/environment plans, fresh work/evidence locations, unchanged resource profile and expected imports. [Planned commands](planned-commands.txt) are explicitly not an activation script. Commit placeholders must be bound after review, and a new adapter must be independently reviewed before execution. Existing implementation `2d75404b` hardcodes the previous module/196-dependency scope and must **not** be reused as though it already validates this draft.

The future adapter must preserve old bindings and explicitly admit the accepted b5e18c… output as a reviewed dependency supplement: it was a prior output, not an old canonical input row. The 16 added frozen dependency objects already belong to the old protected cache inventory. The expected project import set is **214 modules including the new target**, across all four physical project prefixes.

Future checks are only the new module's bounded compile, exact singleton resolution, singleton replay, and focused owner/axiom audit. The [unexecuted audit draft](staged/PolynomialSuppliedForestProbabilityAudit.lean) discovers every actual-owner declaration, requires the named theorem, traverses the existing type/body/inductive/recursor graph, rejects unsafe/partial/project axioms and nonstandard axioms, and requires all three reviewed interfaces to be reachable. Counts remain unknown until that future run; only `propext`, `Classical.choice`, and `Quot.sound` are allowed. [Resolver draft](staged/ResolvePolynomialSuppliedForestTarget.lean) permits only the exact new singleton target.

The plan retains independent duplicate/shadow/sidecar checks, predicted post-output and per-child actual package selection, exact command/environment binding, unique source-bound receipts, unchanged limits, first-failure stop and readable raw exports. Fresh post-planning coordination and separately approved exact released-inode reuse remain prerequisites. This preparation reads the latest accepted release receipt as historical evidence only; it neither probes nor acquires the actual common lock.

## Preservation and disposition

[draft-bindings.json](draft-bindings.json) explicitly records null new object/replay/audit results and zero Lean invocations/lock acquisitions. `prepare_bindings.py` performs only source/object-byte and metadata reconciliation. Its first Python-only attempt used an incorrect direct-journal lookup for the frozen graph; the diagnostic is preserved in `diagnostics/preparation-attempt-1.log`. The corrected attempt verifies the graph against the exact original Git-bound environment descriptor and succeeds. This was no mathematical failure or Lean run, and no earlier evidence was rewritten.

Authenticated provenance, clean validation, implemented sampling/runtime, and paid seed/packing remain separate open items. The inherited IR-signature supplement retains its newly-observed-local qualification; it establishes neither historical preservation before observation nor authenticated dependency provenance. F, its host-count/congestion certificates, and Q's connectivity-preserver property remain inputs; Q is not proved minimum-weight or paid for. No high-probability theorem about an unlinked implementation is asserted.

Published as an additive draft checkpoint on `light-eft-spanners-checkpoints` with `[skip ci]`. All accepted source/object/dependency and historical evidence is preserved. No source promotion, whole-paper completion, CI, SCC or website work is claimed. The worker pauses for independent mathematical and plan review **before Lean**.
