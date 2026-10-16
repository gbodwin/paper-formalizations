# Controller.run total-recursor pilot

**Bounded pilot verified; the unchanged strict all-owner gate still fails on 56 remaining partial roots. No CI was started.** Only `Controller.run` was repaired. No extension to another definition, generated-name filtering, allowlist, blanket `noncomputable` change or whole-paper completion is claimed. Theorem 34 remains open; runtime complexity is excluded.

Tested source: `5e9df7b0ec4f9b6cb22c313fd82159a777035f41`. Exact binding is in `evidence/source-binding.json`. Publication is additive on `light-eft-spanners-checkpoints`, with CI skipped.

## Prior review and permanent qualifications

Independent review of source `e9d3f5ca8fe07062976d1681f8ad24294df6bb10` and evidence `adde368ce7b361a792ed66ea7bdec87a1b66afc1` confirmed diagnostic progress but rejected the strict all-owner gate with 57 partial roots. Safe-root reachability and successful official replays did not discharge it. This records review as source/log/hash reconciliation, not fresh reviewer execution.

All 5,161 entries in that evidence manifest were rehashed unchanged. Both failed audits and the aggregate-prefix OOM receipt remain permanently qualified. The old prefix invocation expanded into internal `IO.asTask` work and violated the sequential constraint; it is not rehabilitated by this pilot. No historical receipt is reused as a repaired-source clean gate.

## Exact repair and semantics

The only changed production file is `LightEFTSpanners/ControllerTrace.lean`; the other 485 production closure sources are byte-identical to the reviewed parent. Its definition now uses:

```lean
Nat.rec (motive := fun _ => S → S) (fun s => s)
  (fun _ previous s => match step s with | none => s | some t => previous t)
```

The type is still `{S : Type*} → (S → Option S) → ℕ → S → S`. The zero and successor equations are explicit `run_zero` and `run_succ`, both proved by `rfl`. `run_eq_of_equations` proves that any function satisfying the historical equations is equal to this implementation. The existing trace, terminal-state and addition theorems retain their statements; their proofs use those explicit equations.

A separate fresh proof, `ControllerPilotComparison.replacement_eq_prior` in `LegacyEquivalence.lean`, proves equality with the actual pre-pilot `Controller.run` imported from its preserved object. The candidate's `Nat.rec` body is byte-for-byte the production replacement body. All 486 old object hashes and the original Controller source snapshot are checked against the prior evidence before that comparison. Its reported axiom set is exactly `[Quot.sound]`. This is a new equality proof against old semantics, not a use of historical receipts or old objects as the fresh repaired-source audit.

`PilotCheck.lean` verifies the type and definitional equations, safe/nonpartial/computable status, explicit `Nat.rec` use, absence of a self-reference and absence of `Controller.run._unsafe_rec`. Five executable fixtures pass: zero steps, advancement, stopping after reaching a terminal state, immediate stopping, and a stationary successful step. They are behavioral checks, not runtime or complexity guarantees. No claim that the operational cost is unchanged is made.

## Why the pinned elaborator avoids the companion

The pinned official Lean source in `Lean/Elab/PreDefinition/Main.lean` tests `isNonRecursive` and sends an ordinary non-recursive definition to `addAndCompileNonRec`. `Basic.lean` assigns that declaration `DefinitionSafety.safe`. In contrast, `Structural/Main.lean` calls `addAndCompilePartialRec`, whose implementation in `Basic.lean` creates the `DefinitionSafety.partial` auxiliary using `Compiler.mkUnsafeRecName`.

The replacement contains no self-reference, so it uses the non-recursive declaration path while calling the existing total recursor. Fresh environment checks confirm that no Controller partial companion was generated. Exact official source snapshots and SHA256 values are retained in `evidence/official-toolchain-sources/`.

## Fresh complete owner audit

All **486 project modules**, including the 56 required LightSpanners support modules and the import-only aggregate, were rebuilt from source into a new `.lake/controller-pilot/lib/lean` directory. Its search path contains no old project-object fallback. The pinned dependency cache is reused; this is a fresh project rebuild, not clean dependency CI. Every project compilation uses official Lean with `-j1 -DautoImplicit=false -DwarningAsError=true`, and succeeds with zero warning headers.

The complete audit runs against that new object set, with all 486 source hashes/snapshots bound into its receipt. It inventories every declaration by actual defining-module owner, traverses types and bodies, opaque values, mutual inductive families and recursor rules, and rejects partial/unsafe declarations and axioms outside the same three-axiom policy. It exports every finding before returning failure; no root is filtered by name.

The fresh result is **9,317 actual-owner roots, 60,736 recursively visited constants, and 48 opaque bodies**. The only axioms are `propext`, `Classical.choice`, and `Quot.sound`. There are zero unsafe project roots, zero aggregate-owned declarations and **56 partial roots**. The exact partial-set difference from the parent is solely removal of `LightEFTSpanners.Controller.run._unsafe_rec`; no new partial appears and the other 56 names are unchanged.

The strict gate still returns exit 1 with **112 findings**: each of the 56 distinct partial declarations appears once at root inventory and once during recursive traversal. This is not a passing gate. The exact remaining list is `evidence/remaining-partial-roots.json`.

The full owner-name delta is confined to ControllerTrace: thirteen generated declarations disappear (including the companion and old generated equation/matcher helpers), while the three explicit equation/uniqueness theorems are added. This explains the net reduction of ten roots; it is not an audit exclusion. The complete delta is in `evidence/owner-inventory-delta.json`.

## Singleton protection and execution

The new `ResolveCheckerTarget.lean` uses the pinned official checker's `SearchPath.findAllWithExt`, `searchModuleNameOfFileName` and `Name.isPrefixOf` operations. It records every actual resolved module and object path before authorizing a checker. `ControllerTrace` resolves to exactly one module; one fresh official `leanchecker -v LightEFTSpanners.ControllerTrace` replay passes with exactly one replay line.

A negative preflight resolves the aggregate prefix to **430 modules** and refuses it before a checker is launched. The aggregate is never replayed. Compilation plus the complete owner audit validates the zero-owned-declaration aggregate. `scripts/LightEFTSequential.py` and this checkpoint's supervisor additionally reject aggregate prefixes and recheck actual filesystem resolution under the universal lock immediately before checker launch. Only a single explicit `-v MODULE` target resolving to exactly one module is permitted. `LEAN_SYSROOT` names the official toolchain, avoiding a nested `lean --print-prefix` query during checker initialization.

There are **495 fresh source-bound execution receipts**, with unique UUIDs, source snapshots/hashes, command arrays/options, PIDs, UTC/monotonic times, one universal lock inode, non-overlapping execution intervals and reaped children. There is only one checker invocation. The fresh project compile/audit search paths, exact source/object hashes and official target-resolution outputs are retained. Prior compiler/checker receipts are preserved but not used to fill any fresh execution count.

## Preserved failures

Four nonzero attempts remain in their UUID folders:

1. Initial precheck failed before elaboration because Lean selected the new namespace directory and could not find dependencies there. The recovery rebuilt the dependency closure and full project in a single fresh output root.
2. The complete all-owner audit rejects the remaining 56 partial roots under the unchanged strict gate.
3. The resolver's first version used reserved token `matches`; it was renamed to `targetModules`. No checker started after that parse failure.
4. The intentional aggregate preflight rejects 430 matching modules. No checker was launched by that negative test.

Raw diagnostics are not overwritten by the repaired attempts; UUID records are authoritative. Warnings are counted from actual diagnostic headers, not hints or option names. Successful strict project compilations have zero warnings. The historical OOM remains in the parent evidence unchanged.

## Review and evidence

`reconcile.py` is a read-only checker for all new snapshot hashes, source/object/import hashes, fresh command coverage, target resolution, recursive closure, exact removed/remaining partial sets, sequencing and preservation. The full diagnostic TSV is also exported as 208 ordered row-aligned chunks with a reconstruction hash in `audit-export/manifest.json`. Concatenate listed bytes without separators or repeated headers.

Entry points are `python checkpoints/light-eft-controller-pilot-20261016/run.py build`, followed sequentially by `audit`, `fresh-pilot-check`, `replay`, and `refuse-aggregate`; the audit and negative preflight are expected to fail for the recorded reasons. The separate old-semantics proof uses `legacy_compare.py`. No default Lake build, parallel worker, runtime shim, dependency update, website change or automatic CI is used.

The official toolchain remains Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`; all nine dependency pins remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. The environment was reconnected and resources/processes checked before work. Terminal idle/resource state is recorded separately. The requested bounded pilot ends here for independent review; the remaining 56 partial definitions are deliberately not repaired in this checkpoint.
