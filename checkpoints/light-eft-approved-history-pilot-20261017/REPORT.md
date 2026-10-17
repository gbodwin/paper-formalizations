# ApprovedHistory exact-predicate repair

Tested source: `3d1132ee59e4ad4a028f8f707aefb35b444648a1`. Branch: `light-eft-spanners-checkpoints`. This bounded incremental repair awaits independent review. Exactly `LightEFTSpanners.SampledGreedy.ApprovedHistory._unsafe_rec` disappears: **11 → 10 partial roots**, none added. The unchanged exhaustive strict gate still fails with **20 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open.

## Accepted baseline and preservation

The parent reports completed independent review accepting source `e53ca4b078b019d2337277ead954a3ced25198e3` and evidence `50257922657ac34e45e610c78c7c88f11c74b7f6`, with 11 partial roots / 22 findings. This is a record of source/log/hash reconciliation, not fresh independent execution or CI. Review was idle before this sole worker resumed. The live connection, clean branch, all 1,518 accepted-manifest entries, 486 production source/object bindings, resource capacity, compiler processes and universal lock were checked before admission.

Only `VotingAdmissionHistory.lean` changes among the 486 production sources. All three preexisting theorem statements and their full proof bodies remain byte-identical; the prefix before ApprovedHistory and suffix from history_approved onward are unchanged. Other roots and statements, including ValidSchedule, remain untouched. Earlier checkpoint trees, all failed attempts, the original memory refusal and recovery records, historical sequencing qualifications, and the wrong-task correction remain unchanged. This task accessed no deleted workspace, other paper or website.

## Predicate and universal equivalence

ApprovedHistory now uses total List.rec with motive Prop. The empty case remains True. At `(e,A)::rs`, the four conjuncts remain exactly: approval of rs; `A ⊆ eligible e`; `h ≤ A.card`; and, for every j in A, `1/4 ≤ testProbability Q (Q ∪ (rs.map Prod.fst).toFinset) (host j) w t f e`. The tail-derived accepted-edge set, duplicates, arbitrary weights/scale and inclusive probability threshold are unchanged. Nil and cons equations are proved by Iff.rfl.

`HistoryComparison.history_iff_prior` proves equivalence against the actual hash-bound accepted old object for arbitrary types, Q, w, t, f, h, eligible, host and record list. No validity, positivity, distinctness or other premise is added. The proof uses induction on the list and and_congr on the first conjunct. Its axioms are only propext, Classical.choice and Quot.sound. The candidate body is byte-bound to the production replacement. This is propositional equivalence, not a numerical probability or physical-runtime oracle.

Sixteen kernel-checked proposition fixtures cover empty, singleton and two-record histories; necessity and projection of each of the four conjuncts; the exact tail-derived edge state; acceptance at probability equality 1/4; rejection strictly below it; duplicate records with empty voters at threshold zero; rejection of empty voters at positive threshold; and empty vertex type with signed parameters. Metadata confirms safe, total, computable, explicit List.rec, no self-reference and no partial companion.

## Sequential validation

Import analysis and an independent fixed-point computation agree on **37 affected modules / 449 inherited objects**. Every affected state entry was removed before compilation. All 37 affected modules, including aggregate compilation, passed strict rebuilding; 449 inherited objects retain accepted source/object/direct-import provenance. The inherited binding file also records the complete initial 486-object copy; final provenance distinguishes fresh and inherited objects.

Official Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, all nine pins and mathlib `5ed2965256430c3649e86755f9576b54eca72435` remain unchanged. Strict commands use `-j1 -DautoImplicit=false -DwarningAsError=true`. Executable, manifest, source, object and supervisor hashes are retained. Entry points are `python checkpoints/light-eft-approved-history-pilot-20261017/legacy_compare.py` and `run.py pilot`, `build`, `audit`, `replay`. The full argv, cwd, source snapshots, PIDs, timing and exit are preserved per invocation.

The unchanged exhaustive unfiltered audit covers **9010 actual-owner roots**, **60429 recursively visited constants** and **48 opaque bodies**. Types, bodies, generated declarations, inductive families and recursor rules are traversed. Only propext, Classical.choice and Quot.sound occur as axioms. There are no unsafe project roots or aggregate-owned declarations. Exactly ApprovedHistory's companion disappears; all other partial roots remain. The audit exits 1 on the remaining 10 roots / 20 root-and-recursive findings. No finding is filtered, exempted or allowlisted.

Official target resolution and locked supervisor resolution both identify exactly `LightEFTSpanners.VotingAdmissionHistory`. `leanchecker -v LightEFTSpanners.VotingAdmissionHistory` passes with exactly one replay line. Audit and replay use the completed isolated outputs and pinned packages; no historical project fallback or aggregate-prefix replay is used. Legacy equivalence separately uses the accepted old objects. This is incremental validation, not a clean final exact-source gate.

## Resources, receipts and evidence

All 42 invocations have unique source-bound receipts, 532 submitted-source entries, individual memory admissions and locked preflights, one universal exclusive lock inode, non-overlapping execution and reaped children. No receipt is carried forward. Zero anchored warning headers occur. The only nonzero invocation is the unchanged exhaustive audit rejecting the remaining partial roots. All raw logs and source snapshots are preserved. No proof retry, cache recovery, data deletion or admission refusal occurred in this pilot.

The unchanged gate requires at least 4,294,967,296 bytes of observed cgroup headroom and system MemAvailable per invocation. Minimum admission headroom: 4653625344 bytes. Minimum system MemAvailable: 17415012352 bytes. Minimum locked-preflight headroom: 4653330432 bytes. These are distinct observations, not reservations or continuous-headroom guarantees. Earlier memory recovery is preserved solely as accepted recorded evidence and was not repeated.

The full recursive TSV and 207 ordered row-aligned chunks are retained. `audit-export/manifest.json` specifies lengths, hashes and whole-file reconstruction SHA256 `6fe78d0fe12e5d8a999ef57b0ab2b26d0fedda0426658b6deeb9c03913d45144`. Concatenate bytes in manifest order with no extra headers or separators. `evidence-sha256.json` seals every checkpoint file except itself. `reconcile.py` invokes no compiler; it rewrites this checkpoint's derived evidence and verifies historical manifests without modifying them.

Terminal checks show no compiler/checker, a free common lock, 14640713728 bytes free disk and a 17179869184-byte memory limit. Repository-wide CI observations are preserved. Additive commits use [skip ci], with normal push after remote-state verification. Paused for independent review; no whole-paper completion or strict-gate acceptance is claimed.
