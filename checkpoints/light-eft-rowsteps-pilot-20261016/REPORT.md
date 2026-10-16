# StoredWeightLookup.rowSteps total-recursor pilot

Tested source: `041143e438c28bb4a4179dd8c6931a3422c788b3`. Branch: `light-eft-spanners-checkpoints`. Exact source/object binding: `evidence/source-binding.json` and `evidence/source-object-provenance.json`.

This bounded incremental repair awaits independent review. Exactly `LightEFTSpanners.StoredWeightLookup.rowSteps._unsafe_rec` disappears: **32 → 31 partial roots**, none added. The unchanged exhaustive strict gate still fails with **62 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open.

## Accepted baseline and resources

The parent accepted source `87a70c27a49e920349b53e31c9f96689bc237fb6` and evidence `00ccac3a880d20cf8e5f404040a3284a9b237d2f`; review had finished. This records source/log/hash reconciliation, not fresh reviewer execution or live-object inspection. The environment connection was live and accepted tracked state clean. All 1,422 parent-manifest entries and all 486 live source/object bindings verified before admission. The actual rowSteps declaration was inspected. No Lean/Lake/checker was active and the universal exclusive lock was free.

Initial and terminal resource bytes/UTC observations are retained. Every invocation requires at least 4 GiB cgroup headroom and 4 GiB system MemAvailable, independently of the supervisor disk gate. Unique memory observations are reconciled with each receipt. These are observations, not reservations or peak-memory guarantees. MemoryAdmission.py and the common supervisor are unchanged. No parallel worker or concurrent review was used.

## Exact transition-count semantics

The replacement uses explicit total List.rec over the rational list, returning a function of the arbitrary natural index. Empty lists return one. Index zero in a nonempty list returns one. A successor index returns the recursive tail count at the predecessor plus one. The final transition to halt is retained, including unsuccessful out-of-range lookup. Three equations are proved by rfl.

LegacyEquivalence.lean imports the exact hash-bound accepted implementation and proves equality of the complete natural count for every j and every rational list. Induction generalizes j; the successor case applies congrArg to adding one. The replacement body is identical to production. The successful theorem is axiom-free. No input-bound, sign, validity, nonempty-list or in-range premise is added.

Twenty exact-output fixtures cover empty rows at zero/successor/huge indices; singleton success and misses; every position of a signed fractional row; its first and later misses; zero and large rational payloads; repeated payloads; and the last cell and first miss of a longer list. They retain the final halt count rather than only successful accesses. Metadata checks verify safe, total, computable, explicit List.rec, no self-reference and no partial companion. This preserves the formal transition counts, not a physical-runtime claim about recursor evaluation.

Only rowSteps changes definition. The entire prefix before it is byte-identical, including State, transitions, repaired rowValue/value and all their equations. The steps definition is byte-identical. All thirteen pre-existing theorem statements retain their hypotheses. Four simplification arguments in row_trace and rowSteps_le use the explicit equations; these anticipated interface adjustments were made before compilation. All other existing proof bodies and all other 485 closure source files remain unchanged.

## Validation scope

The source-derived affected closure is independently recomputed: 131 fresh strict builds, including aggregate compilation, and 355 inherited objects with accepted source/import/object hashes. All affected state entries were removed before rebuilding so equal intermediate objects cannot skip required compilation. Historical receipts are not counted as fresh execution.

Official Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and all nine dependency pins remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Runners verify all revisions. Exact executable, manifest and supervisor hashes are retained. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build, warning suppression, alternate runtime, baseline weakening or blanket noncomputable change occurs.

The exhaustive audit is unchanged except output-directory substitution. It covers 9153 actual-owner project declarations, 60572 recursive constants and 48 opaque bodies, including generated names, recursive types/bodies, inductive families and recursor rules. Only propext, Classical.choice and Quot.sound occur as axioms in the full closure. No unsafe project roots or aggregate-owned declarations occur. No partial root is filtered or exempted. Exactly the rowSteps companion disappears, all other 31 partial roots remain, and the audit exits 1 with 62 root/recursive findings.

The official resolver selects exactly LightEFTSpanners.StoredWeightLookup and the supervisor repeats resolution under the lock. `leanchecker -v LightEFTSpanners.StoredWeightLookup` passes with exactly one replay line. No aggregate-prefix replay occurs. Audit/replay use isolated current project outputs and pinned packages without historical project fallback. The legacy proof uses separately hash-bound accepted outputs. Singleton replay does not discharge the remaining partials or replace clean final exact-source validation.

## Receipts, failures and preservation

137 unique source-bound receipts contain 628 submitted-source entries and individual persisted preflights/memory admissions. Each invocation records exact argv/options, source snapshots and hashes, lock identity, child PID, UTC/monotonic timing, exit and reaping. Reconciliation checks uniqueness, non-overlap, all children reaped, hashes, closure, inherited provenance and preservation. Zero anchored warning headers occur; hints and option names are not warnings.

The first pilot harness invocation, UUID `766c0da435214bcca8bfe1990cbbb4ab`, failed in metadata checks because a text substitution changed Lean's DefinitionVal.value projection to the nonexistent DefinitionVal.rowSteps. The complete-output fixture evaluation printed success in that failed invocation, but the invocation is not counted as passing. Correcting only the two metadata projections to d.value yielded a fully successful rerun. No production source changed for this repair. The failed harness snapshot and full raw diagnostics are preserved. The other nonzero invocation is the unchanged exhaustive audit. No legacy equality or production compile failed.

All historical checkpoint trees, raw failures and qualifications remain unchanged, including prior legacy error-recovery output, aggregate-prefix OOM/sequencing qualification, statement-count and evidence-writer-label corrections. The preceding additive disk precision correction remains preserved. No canceled workspace, other paper or website is changed.

The complete recursive TSV and 207 ordered row-aligned chunks are retained. audit-export/manifest.json records chunk hashes and the whole-file reconstruction hash; concatenate bytes in order without added headers or separators. evidence-sha256.json seals all checkpoint files except itself. UUID logs are authoritative; semantic-label logs are convenience copies.

reconcile.py regenerates current derived evidence/chunks without running Lean/checker and reads historical manifests without modifying them. Entry points: legacy_compare.py; run.py pilot/build/audit/replay; reconcile.py. Publication reconciliation runs no compiler/checker. Source/evidence commits use [skip ci] and normal push after remote checks. Terminal process/lock/resources and repository-wide CI statuses are recorded. Paused for independent review, with no other target started.

Minimum observed cgroup headroom: 8480940032 bytes; minimum system MemAvailable: 17371652096 bytes.

Current checkpoint observed free disk: initially 17.66 GiB (18965893120 bytes), terminal 17.58 GiB (18874834944 bytes).
