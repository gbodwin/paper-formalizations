# Current preparation correction — 2026-10-18

The preparation contracts have been corrected after independent review of packet `83cd543c23fbf7349e82baa61cfccf1b2e27da4d`. The current suite passes **80 tests**. Runtime evidence is nonempty, bound and timestamped; invalid UTF-8 rejection is sticky; blank module/declaration names reject; review attribution is separated. See the [correction report](../light-eft-clean-context-corrections-20261018/REPORT.md) and [final test log](../light-eft-clean-context-corrections-20261018/tests-invocation-02.log). Production remains disabled, the descriptor unavailable, and no Lean or retrieval/extraction/cache advice occurred. This correction awaits review.

The original report below is preserved verbatim as the history of the reviewed base packet; its 46-test count refers to that earlier suite.

---

# Disabled clean-context preparation and dated Light EFT evidence layer

Frozen mathematical source is **`78cb40c7837db049d645d73696f2e0b724ce8a3b`**. Preparation base is **`0769579d242f5c8bcd75f2f6333bb57b8d8fc97b`**, on `light-eft-spanners-checkpoints`. This packet prepares and tests data contracts for a later clean executor. **Production is disabled. No Lean/compiler/checker/version-check process, retrieval, extraction, cache advice, CI or website change occurred.** The preparation fixtures do not establish actual clean validation, capacity, authentication or mathematical acceptance.

The dated [current repository index](../../Light%20Edge%20Fault%20Tolerant%20Graph%20Spanners/verification/current-exact-source-evidence-20261018.json) and [485-chain index](chain-evidence-index.json) reconcile previously reviewed incremental evidence. They do not rerun it. Publication uses `[skip ci]`; the worker pauses for independent review.

## Preservation and demonstrated graph repair

All **nine original draft files**, including the original failing test log, were copied byte-for-byte to [preserved-draft-before-resume](preserved-draft-before-resume/manifest.json) before edits. That log records 33 tests run, 18 passed, 15 test errors and one class-setup error. All 16 errors were `KeyError: 'project_imports'`; seven final-reconciliation tests were blocked by setup. The original files and diagnostics remain intact.

[bind_graph.py](bind_graph.py) repairs the schema from evidence rather than supplying empty imports. It reads all 486 blobs from the frozen Git commit, verifies every SHA256 against the existing graph and current source file, parses their actual import lines, and compares the complete relation to the accepted rows-pilot `affected-closure.json`. [graph-binding.json](graph-binding.json) binds source paths, Git blob IDs, source SHA256 values, exact import lines and edges. There are **1,107 project edges**; every edge precedes its importer, no project import escapes the graph, and the aggregate's transitive closure covers all **486** nodes. No mathematical source or dependency pin changed.

## Finite planned schedule and clean contexts

[PLAN.json](PLAN.json) fixes exactly **1,457 stages**: 486 compilations, 485 exact singleton resolutions, 485 individual kernel replays, and one full audit. The aggregate compiles last and is never resolved or replayed. A single planned `lean --version` check is explicitly **separate** from these 1,457 stages, remains unexecuted, and would require its own future locked owned receipt. No duplicate, automatic retry or aggregate-prefix replay is authorized.

[clean_contract.py](clean_contract.py) models a fresh `/workspace/.lake/light-eft-clean-<run_id>` with distinct source, dependency, toolchain, helper, working, evidence, project-object and resolution paths. Initial object and resolution ledgers are empty. The planned Lean search roots contain only this fresh run's outputs, pinned fresh dependencies and fresh toolchain. Historical project roots, dependency object roots, seeded ledgers and symlinks are rejected. The historical retained paths in the chain index are evidence references only; they never seed the new context or its search path.

Each modeled stage binds source commit/hash, exact argv/environment/cwd, input/output contexts, unique attempt UUID and PID incarnation, common lock, inherited handshake, selected profile, admission/pre-exec accounting, owned terminal wait and reaping, descendant cleanup, ordered timing, runtime guards and complete input-preservation metadata. Compilation produces only a provisional bound object; exact resolution must name that object; replay must emit precisely the singleton target. Failed/partial outputs and failed resolution records are quarantined, not accepted. Final failure also quarantines the provisional ledgers. Promotion occurs only after all 1,457 modeled stages, complete final preservation, the fresh audit and exact chunk reconstruction pass.

[audit_data.py](audit_data.py) independently reconciles the fresh audit's four source-directed outputs plus raw diagnostics. It checks fresh producing receipt/context/paths, file/output budgets, all 486 required modules, actual-owner/private/generated coverage, strict safety flags and findings, types and bodies including modeled recursor/inductive links, exact recursive closure, permitted axioms, derived counts and row-aligned hash-bound chunk reconstruction. Historical root counts or successful old diagnostics cannot satisfy this fresh contract.

These are **synthetic contracts**, not an actual filesystem executor or new compiler receipts. Positive fixtures use explicitly fictional PIDs, hashes and a toy inventory; their output remains `actual_clean_validation_performed=false` and `production_enabled=false`. A later real executor and its authentication/clean-input wiring still require separate review.

## Unchanged lifecycle and bounded accounting

[supervisor-bindings.json](supervisor-bindings.json) binds **14 unchanged source references**: six ordinary supervisor/accounting/preservation sources, seven audit sources and the shared lifecycle source. They are referenced byte-for-byte, not copied into a divergent implementation or invoked by this packet. In particular, approved exit handling remains `1135140dd7dd3d075953d5d621f727a7a7c13796985c27da0c5afba68f95e76a`, and telemetry remains `08ae50f987ba67655e21d504e561ff5a23eda79104f35fe4c0d48e6e59de87fe`.

Ordinary file size limits remain **16 MiB**; audit file size limits remain **64 MiB** with the separate 320 MiB source-output-plus-raw budget. Address-space, CPU, 90-second wall deadline, physical-memory floors, RSS and per-visible-cgroup anonymous-growth stops, disk boundary, and 16 MiB decision log remain separately specified. Unknown ancestors remain unknown: `PARTIAL_VISIBLE_ANCESTORS; unseen limits UNKNOWN`. **No full-ancestor admission gate is introduced.** Synthetic guards are not observed capacity or a physical-runtime theorem.

[unchanged-production-bindings.json](unchanged-production-bindings.json) binds the **six unchanged production/pin files**, including the descriptor, artifact helper, full audit, resolver, Lake manifest and toolchain pin. The descriptor remains `UNAVAILABLE_REVIEW_REQUIRED`; the real reviewed artifact authority is `null`. The metadata positive control proves consistency only under a supplied synthetic authority and performs no authentication. It cannot enable production.

## Tests and entry point

The final synthetic/static suite passes **46 tests**, including all original 40 tests and their seven final-reconciliation cases. Added cases cover frozen source/import bindings, separate version-check accounting, repeated attempt IDs, overlapping receipts, and the dated historical/current evidence separation. Raw logs are retained: [original failed attempt](tests-invocation-01.log), [42-test repair](tests-invocation-02.log), [expanded suite](tests-invocation-03.log), and [final suite](tests-invocation-04.log).

One later packet-metadata check initially assumed every verbose unittest success occupied one line; the describe-only test prints JSON within that line. Its script and traceback are preserved under [failed-packet-validation-01](failed-packet-validation-01/raw.log). The metadata reader was repaired to count test starts and require the passing runner footer. This did not change the tests, proof sources or their outcomes. An earlier ad hoc metadata read used the wrong relative receipt directory; its diagnostic and correction are recorded in `commands.txt`.

Commands used for the preparation are recorded in [commands.txt](commands.txt). The safe entry point is:

```text
python3 -B checkpoints/light-eft-clean-context-preparation-20261018/describe.py --describe
```

It only describes the plan. Every other argument combination, including missing/forged approval, force or artifact overrides, raises `ProductionDisabled` before any execution. The packet has no production execution capability. [implementation-bindings.json](implementation-bindings.json) and the complete [manifest](manifest.json) bind its implementation and evidence.

## Current reviewed incremental evidence

[chain-evidence-index.json](chain-evidence-index.json) links all **485 qualified ordinary chains** in ten readable JSON parts, and the aggregate compile separately. It reconciles **1,456 distinct successful stage receipts**, submitted sources, current retained object bytes, original per-stage object paths, exact resolutions, singleton replay diagnostics and raw-log hashes. It links each batch's immutable publication/result commits. Relocated byte-identical objects are marked explicitly; the index does not call old paths fresh. Eight failed/unqualified historical stage records are listed separately and remain preserved. The final ordinary review authority is **`4bc6d398cee4e65c1550a585fff6778381262bdf`**; this packet records the parent's reported review, not another independent acceptance.

Full-audit binding **`c7f33d7ece117ddc7d20e4f7a5dad2f870e9d41f`** covers 485 ordinary modules plus aggregate, **8,950 project roots**, **60,369 closure constants**, **48 opaque bodies**, zero unsafe/partial/project-axiom findings, and only `propext`, `Classical.choice`, `Quot.sound`. All **244 execution manifest entries** were hash-checked; all **216 ordered chunks** reconstruct their five original outputs exactly. Recursive export SHA256 is `47469d94d75ebb388bad2e9e62f07fd3d58d4e8c5a81af35d8a9c78281cb7bf0`.

The earlier audit's 83,032-binding canonical inventory remains bound by SHA256 `cbd1cf79ad3f136c92585821f317cd1c98a1c1d001fa7468943df652fbceaf4e` and matching initial/final preservation receipts. The parent connector could not independently retrieve the complete 30 MB inventory; that historical review limitation remains explicit. This packet does not assert a new full frozen-input preservation pass or provenance upgrade.

The statement map's five `current_native_coverage` fields now point to this dated evidence. Their original dictionaries, including old 57/56-partial results, are retained verbatim under `historical_native_coverage`. Every other statement field, status and mathematical scope is unchanged. README and proof-coverage files gain only a dated prefix; all original report bytes remain as their suffix and are also preserved in [preserved-index-before-update](preserved-index-before-update). Old headings saying “Current” are explicitly historical.

## Remaining obligations and disposition

Latest access evidence remains **`0769579d`**: exactly one unchanged-route official-cache GET returned HTTP 403 / code 1010. There was no new probe, workaround, network change or demonstrated user-side setting. Local hash agreement does not authenticate all 3,808 official archives, the toolchain distribution or extractor membership. The descriptor remains unavailable.

Authenticated clean validation, the reviewed production clean executor, exact coordinated CI, **Theorem 34 replacement scaling**, the formal-runtime/physical-runtime distinction, website completion and whole-paper acceptance remain separate and pending. No mathematical statement or status was changed. [packet-validation.json](packet-validation.json) records current resource observations, unchanged bindings, preserved drafts, allowed edit scope and idle/free-lock status. No compiler remains active; paused for independent review.
