# Conditional +6: normal-toolchain verification evidence

Status: worker validation completed; independent sequential review pending. This report does not accept the candidate, certify the cited subset-spanner theorem, or claim whole-paper acceptance.

## Exact source and receipt

Tested source commit: `d0f9ee2364bf4a5aaa7e0ca4da48216e42bbc63e`, fetched from `unverified/conditional-plus6-preserved-20261015` in `gbodwin/paper-formalizations`.
Frozen baseline: `dc376e8efac8c1bc236abbe68d296060d7ba4142` on `distance-sparsification-certified`.

All 165 candidate files were checked for byte count, SHA256 and Git blob identity against [SOURCE_TRANSFER_MANIFEST.json](SOURCE_TRANSFER_MANIFEST.json). No baseline path was missing; 159 files were unchanged. Changes comprise four new PlusSix modules, four imports in SlackSparsification.lean, and verification/PlusSixAudit.lean. See [receipt.json](receipt.json) and [aggregate.diff](aggregate.diff). Candidate files were rehashed after validation without any mismatch.

The manifest identifies archive SHA256 `bb7325cdf87e850e8dd5b1a209860abd7924becf5c104d35910a22906818db33` (12,894,298 bytes). Archive-to-checkpoint correspondence is transfer-worker provenance, not an independently verified ZIP hash here: Library and direct-attachment downloads were blocked by proxy 403. Their diagnostics are preserved in [transfer-failures](transfer-failures). No signed URLs or access tokens are included.

Validation used a separate byte-identical source tree at `/workspace/plus-six-verification/checkpoint/candidate`, with freshly produced project objects and the pinned dependency cache. The certified checkout remained clean and unchanged. Historical shim-environment evidence was not used as acceptance evidence.

## Toolchain and commands

Official Lean 4.34.0 release commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, x86_64 Linux; Lake `5.0.0-src+293d5d0`. [toolchain.log](toolchain.log) includes version output and SHA256 of the Lean and leanchecker executables. Setup verified all 17,738 installed regular toolchain files against the saved release archive; this was a local archive comparison, not a fresh external signature check.

All nine dependency checkouts matched lake-manifest.json and were clean, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Official `lake exe cache get` downloaded and decompressed 8,908 files successfully without network-policy changes. See [setup/final-state.log](setup/final-state.log) and [setup/cache-get.log](setup/cache-get.log).

Environment used:

```sh
export ELAN_HOME=/workspace/toolchains/elan
export PATH="$ELAN_HOME/bin:$PATH"
```

Each compile ran sequentially with:

```text
lake env lean -j1 -DautoImplicit=false [ -DwarningAsError=true ] --root=<source-library-directory> -o <fresh-module.olean> <source.lean>
```

`warningAsError=true` was applied to all four new modules and the import-only aggregate. Default linters remained enabled for all 23 inherited modules. No default multi-paper build was run. Exact argument arrays, source hashes, elapsed times and exit codes appear in [compile-results.jsonl](compile-results.jsonl); [order.json](order.json) records topological order. The preserved runner scripts document the original execution, including absolute workspace paths; they are not portable one-command review instructions and must not be run over existing evidence (the compile runner skips recorded successful modules).

## Results and diagnostics

- 23 inherited modules: exit 0, with 36 preserved default-linter warnings.
- Four new modules plus import-only aggregate: exit 0, no diagnostics under warningAsError=true.
- 27 individual modules: official kernel replay exit 0, one target per invocation, with exactly one `replaying <module>` line each.
- Recursive axiom audit: exit 0 under autoImplicit=false and warningAsError=true.

[Raw compile logs](.) are named `compile-<module>.log`; zero-byte files mean no output. [inherited-warnings.json](inherited-warnings.json) preserves each complete diagnostic and classification:

| Linter | Count |
| --- | ---: |
| unusedSectionVars | 21 |
| unusedSimpArgs | 5 |
| unnecessarySimpa | 2 |
| unusedVariables | 1 |
| style.haveILetI | 5 |
| unnecessarySeqFocus | 2 |

These are unused-binding or proof-style diagnostics in byte-identical inherited sources. None was suppressed, and no Lean source was edited to remove them. There were no proof/type errors. [attempt-notes.txt](attempt-notes.txt), the initial failed output-write log, and the malformed initial Python runner preserve setup failures and diagnostic-classification pauses. Some failures were only captured in tool output at the time; their descriptions in attempt-notes.txt are retrospective notes, not purported original raw logs.

## Individual kernel replay and object identity

Exact command for each of 27 leaf modules:

```text
lake env leanchecker -v <exact.module.name>
```

Lean 4.34.0 leanchecker normally matches module-name prefixes. The runner checked that each requested leaf had exactly one matching project object; every raw log confirms exactly one replay. The aggregate `SlackSparsification` prefix was never invoked. No --fresh all-import replay or independent external proof checker was claimed.

See [checker-results.jsonl](checker-results.jsonl), `checker-<module>.log`, and [compiled-object-hashes.json](compiled-object-hashes.json). All 28 generated .olean objects, including the import-only aggregate, are hashed. Objects remain locally available in the validation tree; binaries are not included in this evidence-only commit. Official leanchecker checks new declarations against their imported environment; the imported third-party cache was not independently kernel-replayed in full.

## Declaration and recursive axiom coverage

The unchanged preserved `verification/PlusSixAudit.lean` was run as:

```text
lake env lean -j1 -DautoImplicit=false -DwarningAsError=true "A Note on Distance-Preserving Graph Sparsification/verification/PlusSixAudit.lean"
```

[recursive-audit.log](recursive-audit.log) and [audit-result.json](audit-result.json) record success. Coverage: 241 actual-owner project declarations, including 16 declarations in the four new modules (generated declarations included); 19,215 recursively visited constants; 14 opaque bodies. Ownership selection covers all SlackSparsification modules and the imported LinearDistancePreservers.InducedMatchings and LazyTreeSelection modules.

The traversal inspects declaration types, definition/theorem/opaque bodies, and inductive constructors, rejects unsafe or partial recursive dependencies and disallowed axioms, and does not rely on cached collectAxioms results. Exactly `propext`, `Classical.choice`, and `Quot.sound` were found. No new axiom was allowed.

See [actual-owner-inventory.tsv](actual-owner-inventory.tsv), [recursive-dependencies.tsv](recursive-dependencies.tsv) (large; download raw), and [import-closure-loaded.txt](import-closure-loaded.txt). This audit and kernel replay are implementation evidence; an independent reviewer must still evaluate statement fidelity and mathematical scope.

## Remaining mathematical hypotheses

The graph-level +6 endpoints explicitly require a finite simple graph G, a real constant C with `0 < C`, and `UniformSubsetPlusTwo G C`. That premise says the same constant C works for every finite vertex subset S: there exists a subgraph K of G with at most `C * |V| * sqrt(|S|)` edges and additive +2 distances for every pair in S. This premise is neither proved nor replaced with an axiom here.

Path-level statements additionally require actual shortest walks (with length equal to graph distance); slack statements require a nonempty finite demand set and their stated integer-parameter conditions. The graph-level complete endpoint handles empty demand sets and disconnected graphs, retaining the uniform subset premise. Its edge bound is

```text
((10 + 6*C) * |V| / (1 - (3/4)^(1/4))) * |P|^(1/4).
```

Independent review must assess the supplied subset theorem/interface and its uniform constant, the conditional endpoint statements, and their correspondence to the intended paper results. Unconditional +6 and whole-paper acceptance remain unclaimed.

## Fresh sequential review handoff

1. Fetch the evidence commit and verify the tested source commit separately. Check manifest hashes and evidence hashes before using the files.
2. Use official pinned Lean/dependencies, fresh project outputs, and a separate evidence directory; never reuse logged success as a fresh review result.
3. Compile the 23 inherited modules in order with default linters, then the four new modules and aggregate with warningAsError=true. Preserve diagnostics.
4. Replay each exact leaf module separately, verifying a singleton target. Never invoke the aggregate prefix. Run the recursive audit after compilation/replay, with its relative evidence destination set up in the isolated review tree.
5. Evaluate mathematical premises and statement fidelity independently. Keep the candidate unaccepted until that review is coordinated.

No source changes, certified-branch changes, website changes, or compiler reruns were made while preparing this evidence. The worker is idle after publication with no compiler/checker process running. [evidence-sha256.json](evidence-sha256.json) covers every evidence file except itself; the Git commit anchors that hash manifest.
