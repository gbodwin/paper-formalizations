# Probability-draft executable adapter — preparation only

**Adapter and synthetic tests only. No Lean, common-lock acquisition, real inventory scan or production attempt.** Implementation **`b6483cccabdf4afdbb8004a768afe8ea9ed0ff32`** adapts the mathematically reviewed draft/plan **`88d297fa58a15406aac6e7c0ea3c85f65965d19a`**. Elaboration remains untested. Independent adapter review and separately authorized fresh coordination are still required before execution.

The user reports approval of draft `88d297fa`; this records mathematical/plan review, not new execution. The draft's three Lean sources are reused at their original reviewed paths and bytes. No Lean source was edited or promoted. The accepted deterministic object remains unchanged at SHA256 **`b5e18c2425b50a2b7008f2a5f9ab928f22daae1d530293d373691a0a378cbc18`**.

## Exact draft and schema translation

The target is **`LightEFTSuppliedForestProbabilityStage.PolynomialFailureProbability`**, theorem **`LightEFTSpanners.SampledGreedy.polynomial_supplied_forest_package_failure_probability`**. `probability_plan.py` authenticates the original draft manifest and all 23 payload entries against Git commit `88d297fa`, including the three staged source bindings, closure data and full per-command plan. It checks each staged source's exact path/bytes/hash/identity.

The reviewed draft uses per-command `environment` dictionaries and ordered `submitted_sources` binding records. The adapter translates these explicitly into the supervisor's `env`, path-only `sources`, full `source_bindings`, and `cwd` fields. It does not infer a top-level environment, old additions/removals, or a legacy path-only source schema. Compile/resolve/replay/audit have respectively **1/2/1/2** source bindings. Command paths/options, sysroot, order, cwd, target, source roles and stage admission values are checked. Runtime receipts record the working directory and original planned source bindings, and the receipt verifier checks those records independently.

Only the two exact reviewed template slots are filled: `LIGHTEFT_SOURCE_COMMIT` becomes **`88d297fa…`**, and `LIGHTEFT_HARNESS_COMMIT` becomes the exact reviewed adapter commit. Unknown/unresolved placeholders and old origin `40029953e9e53525f0f1f431d6d56333b05183a3` are rejected as active source/adapter bindings. The old origin remains solely an explicit legacy authority for the preserved original inputs, not this new theorem's source commit.

[Concrete plan preview](concrete-plan-preview.json) binds source `88d297fa` and adapter `b6483ccc`; it is a read-only translation result, not an execution receipt or activation. The fresh work/evidence paths are exactly those reviewed in the draft plan. Neither was created. No local copied/rewritten staged Lean source is used by this adapter.

## Immutable accepted-object supplement and dependency scope

`scope.py` retains the original source/pin/cache verifier under its explicit legacy authority. It then binds exactly **213 dependencies** from the reviewed closure: **212 frozen modules** (156 LightEFTSpanners, 56 LightSpanners) plus the **one accepted staged deterministic module**. The new target is excluded from the input set. The draft's source/object hashes remain authoritative; no cache rebuild occurs.

[accepted-object-supplement.json](accepted-object-supplement.json) admits **one exact path/185,576-byte/hash/identity binding** for the b5e18c… object. The policy is separately authenticated against the reviewed adapter commit and checked against the accepted-object record inside draft `88d297fa`. Merging cannot replace a conflicting old binding. Every inventory scan enforces the accepted object's exact immutable content and identity; equal-byte inode replacement also fails. Extra objects, sidecars, signatures or other files under its root are not admitted. There is no root or filename-pattern whitelist. Original cache hashes and the qualified IR-signature supplement remain unchanged.

Independent duplicate-leaf, target-prefix, sidecar, symlink/type and package-selection guards remain. Predicted layout is checked during read-only planning, and actual selection is checked before each child. The new probability package, old accepted-stage package and legacy project packages stay physically distinct.

## Focused audit and ownership

The reconstructed audit requires **213 dependency names and exactly their 214 project imports including the new target**. All four prefixes are recognized: `LightEFTSpanners`, `LightSpanners`, `LightEFTSuppliedForestStage`, and `LightEFTSuppliedForestProbabilityStage`.

The reviewed Lean audit inventories every actual-owner declaration, including private/generated roots, and requires the named new theorem. Its traversal is unchanged. The Python reconstruction independently enforces exact root/closure metadata, complete reachability, owner/import scope, safe/nonpartial declarations, allowed axioms and actual counts derived from outputs. It additionally requires each of these three declarations in the reconstructed reachable closure, independently of printed PASS text or the Lean-side required-interface check:

- `LightEFTSpanners.SampledGreedy.voting_good_event_of_supplied_forests`
- `LightEFTSpanners.SampledGreedy.polynomial_inaccurate_probability`
- `LightEFTSpanners.FiniteProbability.Law.prob_mono`

No new real root count or recursive-constant count is assumed. The audit still permits only `propext`, `Classical.choice` and `Quot.sound`, and rejects project axioms, unsafe/partial declarations, incomplete ownership and unreachable/missing dependency rows.

## Latest released-lock authority and unchanged supervision

[released-lock.json](released-lock.json) pins the **latest successful release**, not the older failed attempt:

- Epoch: **`7d164441f8ac44d9b9c316cdd79869f3`**
- Device/inode: **33:3258**; directory identity **[33,1]**
- Receipt commit: **`7eedd5b3c7860cf473f5deff3b4ed369f19e6e61`**
- Receipt SHA256: **`e4b4b0ea64888fbc9c04afd3026870227a82af1cb335031ef4552fe9629815d1`**

The receipt's exact Git blob, release state, ECHILD and epoch are checked. Fresh post-planning coordination still explicitly authorizes this exact released identity, with current ownership facts, the unchanged less-than-60-second window, no timestamp refresh, and a recheck before claims. The lease implementation is byte-identical to the reviewed nonblocking exact-identity reuse code: no common-lock creation, truncation, unlink or other-inode adoption. It checks FD/path/directory identity before and after acquisition and throughout ownership, and retains the owned-child/ECHILD release barrier.

Process supervision, resource accounting, telemetry, limits, output guards and package-selection implementation are unchanged. There is no supervisor redesign or resource increase. The only batch-loop change is an explicit equality assertion binding its existing computed cwd to the reviewed per-command cwd. [Scope reconciliation](scope-reconciliation.json) records six changed base files and 12 unchanged base helper/data files; the source/pin verifier retains the same checks with explicit legacy names.

## Tests, bindings and disposition

**19 Python-only regressions passed, exit 0**, in one attempt. [Raw diagnostics](diagnostics/adapter-tests-attempt-1.log), [fixture results/source snapshots](test-evidence/e6cf103f22964f2a928cf936b159fdf0/result.json), and all private fixture files are preserved. Tests cover real reviewed-plan translation, source schema/role/cwd errors, commit placeholders/origin rejection, exact dependency scope, the actual builder with synthetic inventory, source/cwd receipt hooks, accepted-object mutation/replacement and root nonwhitelisting, masking/duplicates/sidecars, all four audit prefixes, each independently missing interface with otherwise self-consistent fabricated audit counts, and stale authority before claims/work/evidence/locking. Object bytes and audit rows in these fixtures are synthetic, not Lean objects or proof results.

[Small binding check](small-binding-check.json) verified this implementation's helper/policy Git bindings, the real draft's small-file authentication/translation, and the exact released receipt. It used explicit synthetic facts/time and never called the real plan builder, inventory scanner, activation or lease. The accepted b5 object was only read and hashed unchanged. [Base bindings](base-bindings.json) and the complete manifest preserve the reviewed foundations. The inherited signature supplement remains newly observed local evidence; no historical-preservation or authenticated dependency provenance claim is added.

All sealed files, including ignored synthetic `.olean` fixture paths, are explicitly staged and verified as Git blobs. Publish with `[skip ci]` on `light-eft-spanners-checkpoints` and pause for independent adapter review **before Lean**. No accepted theorem recompilation, source promotion, rebuild, memory diagnostic, retrieval, common-lock acquisition, SCC or site work occurred. No new theorem acceptance or whole-paper completion is claimed.
