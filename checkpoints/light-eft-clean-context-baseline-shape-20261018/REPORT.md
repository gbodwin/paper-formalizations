# Two narrow disabled-preparation checks

Base: **`b74968f3f7c57c1a5768d902bfe1a2e910c8a055`**. Frozen mathematical source remains **`78cb40c7837db049d645d73696f2e0b724ce8a3b`**. This packet adds exactly two guards in `clean_contract.py`, their synthetic regressions and refreshed preparation metadata. No production, Lean/compiler/checker/version-check, retrieval, extraction, cache advice, CI, proof-source or website operation occurred.

The reported preparation review verified the base packet's 91 bindings, 20 unchanged supervisor/production hashes and 80 tests. Before editing, those 91 bindings were checked again and ten files were snapshotted in [preservation.json](preservation.json). All previous test histories, failed attempts, indexes, proof/audit results and the entire previous correction directory remain unchanged. This records source/log/hash review, not new execution or acceptance of this packet.

## Exact guards and regressions

1. `anonymous_preexec_baseline` must equal the complete path-to-`memory_stat.anon` map derived directly from `preexec_admission.nodes`. The existing path/type checks remain. The negative fixture leaves pre-exec accounting unchanged, raises observed anonymous memory by **4 GiB**, and inflates the declared baseline by **2 GiB**, falsely reporting only 2 GiB growth below the 3 GiB stop. The new equality guard rejects this mismatch before it can hide growth.
2. Each runtime sample must be a dictionary **before any `.get` call**. A null sample now raises `Rejected` inside the existing sticky failure handling, rather than escaping as `AttributeError`. Fixtures exercise both stage consumption and finalization. Finalization quarantines all **486 provisional objects and 485 provisional resolutions**; restoring valid samples and retrying cannot promote either ledger.

There is no broader runtime or supervisor redesign. Existing deadline, identity, UTF-8, blank-name, attribution, resource and unknown-ancestor qualifications remain unchanged. The source diff in `clean_contract.py` is exactly two added `require` statements.

## Verification and evidence

- [Targeted regressions](regressions.log): **3 tests passed**.
- [Full suite](full-suite.log): **83 tests passed**, including all previous 80 tests and all original 40 tests.
- [Commands](commands.txt), [validation](validation.json), [complete manifest](manifest.json).

The full suite remains synthetic/static. It checks the frozen 486-source/1,107-edge graph, the 1,457-stage modeled plan with a separate unexecuted version check, and production-disabled entry behavior. The 14 supervisor references and six production/pin files remain byte-identical. The artifact descriptor remains `UNAVAILABLE_REVIEW_REQUIRED`; production stays disabled. The proof source, audit source/results, chain index, dated evidence index and mathematical hypotheses/statuses are unchanged. No new failing test attempt occurred; all prior raw failures remain preserved.

The current preparation report gains only a notice above its preserved prior body. Its bindings and manifest are refreshed; historical reports and logs retain their original bytes and immutable commit references. Publication uses `[skip ci]`, and exact remote state is checked. Independent review of these two guards remains pending. The worker pauses idle with the universal lock free and no compiler/checker process. Authenticated clean execution, exact CI, Theorem 34/runtime qualifications and whole-paper acceptance remain outside this preparation correction.
