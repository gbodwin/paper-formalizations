# StoredForestHosts.value total-recursor pilot

Tested source: `143d1192bb347426e13f33f88a817eb945f6c554`. Branch: `light-eft-spanners-checkpoints`. Exact source/object binding: `evidence/source-binding.json` and `evidence/source-object-provenance.json`.

This bounded incremental repair awaits independent review. Exactly `LightEFTSpanners.StoredForestHosts.value._unsafe_rec` disappears: **28 → 27 partial roots**, none added. The unchanged exhaustive strict gate still fails with **54 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open.

## Baseline and reconnection

The parent accepted source `5ad25c7ecc138ae1a307c9a266d29bdb838e0438` and evidence `29a3c889eed9445ce4f3fbbcb22b3056505799da`; review had finished. This records source/log/hash reconciliation, not fresh reviewer execution or live-object inspection.

The selected environment initially reported starting. wait_for_environment returned ready, and live commands succeeded before compiler admission. HEAD and tracked source matched the accepted evidence; all 1,137 parent-manifest entries and all 486 live source/object bindings verified. No preceding build was resumed or duplicated. The actual value declaration and its consumers were inspected. No Lean/Lake/checker was active, the common exclusive lock was free, and memory met admission thresholds. Initial and terminal resource bytes/UTC observations are retained; GiB uses 2^30 bytes. No canceled workspace, other paper or website was accessed or changed.

Every invocation has a separate persisted memory admission requiring at least 4 GiB cgroup headroom and 4 GiB system MemAvailable, separately from the supervisor disk gate. These observations are not reservations or peak-use guarantees. MemoryAdmission.py and the common exclusive supervisor remain unchanged. There is no parallel worker or concurrent review.

## Complete ordered record semantics

The replacement uses explicit total List.rec over input edge lists, returning a function of the arbitrary starting forest index. Empty input gives []. A cons maps the current index onto each complete StoredDiscoveredHosts.value record, appends that ordered list to the tail result, and evaluates the tail at index+1. Both equations are proved by rfl. Index advancement occurs per input list, independently of its number of emitted component records. Each component/root, vertex list and host-edge list remains intact and ordered exactly as before.

LegacyEquivalence.lean imports exact hash-bound accepted objects and proves equality of the entire ordered record list for every n, arbitrary starting i and arbitrary list of Fin n edge lists. Induction generalizes i and applies congrArg to prepending the current mapped records, with the hypothesis at i+1. The replacement body is identical to production. The theorem uses only propext, Classical.choice and Quot.sound; no new axiom or mathematical hypothesis is introduced. In particular, no acyclicity, forest-validity, edge-uniqueness, nonempty-input or bounded-start premise is added.

Twenty fixtures compare full literal record lists using a tuple-construction helper, not lengths, projections or recomputation through the implementation. Cases include n=0, empty input, isolated vertices, connected and disconnected components, nonzero/huge starting indices and their successors, multiple records sharing one forest index, repeated input lists, preserved edge orientations/order/duplicates, cyclic lists and loops. The loop fixtures preserve the existing host filter's loop exclusion. Universal equation examples and metadata checks verify safe, total, computable, explicit List.rec, no self-reference and no partial companion. Equality is not a physical-runtime claim about recursor evaluation.

Four production files change. StoredForestHosts.lean changes only value and adds two equations; Record, State, transition and both existing theorem statements and proof bodies remain byte-identical. StoredForestHostsTrace.lean changes three simplification arguments in scan_trace/value_length to use value_cons/value_nil. StoredForestHostsOriginal.lean changes four rewrite/simplification arguments in mem_value. All four trace-file and one original-file theorem headers, their hypotheses and all definitions remain unchanged. These anticipated interface repairs were made before compilation. StoredForestInputEncoding.lean changes two simplification arguments in attachment_encoded to use StoredForestHosts.value_cons and typedInputs_cons after the preserved failed attempt. Both existing headers and execute_encoded remain unchanged. All other 482 closure source files remain unchanged.

## Complete sequential validation

The source-import closure is independently recomputed: 80 fresh affected strict builds, including aggregate compilation, and 406 inherited objects retaining accepted source, direct-import and object hashes. Every affected state entry was removed before rebuilding, so identical intermediate objects cannot bypass compilation. Historical receipts are not counted as fresh execution.

Official Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and all nine dependency pins remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Runners verify all revisions; exact executable, manifest and supervisor hashes are retained. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build, warning suppression, weakening, alternate runtime or blanket noncomputable changes occur.

The exhaustive audit is unchanged except output-directory substitution. It covers 9124 actual-owner project roots, 60543 recursive constants and 48 opaque bodies, including generated declarations, recursive types/bodies, inductive families and recursor rules. Only propext, Classical.choice and Quot.sound occur as axioms in the full closure. No unsafe project roots or aggregate-owned declarations occur. Exactly the value companion disappears, while all other 27 partial roots remain. The strict audit exits 1 with 54 root/recursive findings; no violation is filtered, exempted or allowlisted.

Official resolution selects exactly LightEFTSpanners.StoredForestHosts; the supervisor repeats resolution under the lock. `leanchecker -v LightEFTSpanners.StoredForestHosts` passes with one replay line. No aggregate-prefix replay occurs. Audit/replay use isolated current outputs and pinned packages without historical project fallback; legacy equality uses separately hash-bound accepted objects. Singleton replay does not discharge remaining partials or replace clean final exact-source validation.

## Receipts and preservation

86 unique source-bound receipts contain 576 submitted-source entries and individual persisted preflights/memory admissions. Each records exact argv/options, source snapshots/hashes, lock identity, child PID, UTC/monotonic timing, exit and reaping. Reconciliation verifies hashes, UUID uniqueness, one lock inode, strict non-overlap, all children reaped, complete affected closure, inherited provenance and historical preservation. Zero anchored warning headers occur; hints and option names are not warnings.

One downstream compile failed, UUID 11f0df9f05b144249bf1a433ab680104: attachment_encoded unfolded recursive tails whose rewritten bodies no longer matched the induction hypothesis. Replacing its two unfolding arguments by the existing value_cons and typedInputs_cons equations repaired the proof without changing definitions, hypotheses or statements. The original failed source and full diagnostic are preserved. The other nonzero invocation is the unchanged exhaustive audit rejecting remaining partial roots. Universal legacy equality and all fixtures passed on their first attempts.

All historical checkpoint trees, raw failures and qualifications remain unchanged, including earlier legacy recovery output, metadata-harness failure, aggregate-prefix OOM/sequencing qualification, statement-count correction, evidence-writer-label correction and disk precision correction. UUID logs are authoritative; semantic-label logs are convenience copies.

The full recursive TSV and 207 ordered row-aligned chunks are retained. audit-export/manifest.json gives chunk hashes and the whole-file reconstruction hash; concatenate bytes in order without added headers or separators. evidence-sha256.json seals every checkpoint file except itself.

reconcile.py rewrites current derived evidence/chunks without running Lean/checker and checks historical manifests without modifying them. Entry points: legacy_compare.py; run.py pilot/build/audit/replay; reconcile.py. Publication reconciliation runs no compiler/checker. Additive source/evidence commits use [skip ci], with normal push after remote-state checks. Terminal resource/process/lock and repository-wide CI observations are saved. Paused for independent review; no other target is started.

Minimum observed cgroup headroom: 7601573888 bytes; minimum system MemAvailable: 17366880256 bytes.

Current checkpoint observed free disk: initially 16.89 GiB (18134990848 bytes), terminal 16.81 GiB (18044866560 bytes).
