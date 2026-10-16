# Pairwise +6 integration checkpoint — pending independent review

Tested source commit: **c189a4e93786b47c7dbc23146c6b44a5b9cc75dc**.
Parent: **d199b99c6d3902e2b827a2b5c3efef072c2fa88a**.

The new theorem `SlackSparsification.exists_plus_six_complete_unconditional` applies the accepted conditional theorem `exists_plus_six_complete` with `C = 16`, proves its positivity, and supplies `SubsetPlusTwo.uniform_subset_plus_two G`. The resulting bound is

```text
∃ H, IsAdditiveSpanner G H P 6 ∧
  (H.edgeFinset.card : ℝ) ≤
    (106 * Fintype.card V / (1 - (3/4 : ℝ)^(1/4 : ℝ))) *
      (P.card : ℝ)^(1/4 : ℝ)
```

The only graph hypotheses are a finite vertex type with decidable equality and a simple graph; `P` is any finite ordered-pair demand set. No uniform subset-spanner premise, connectivity assumption, or nonempty-vertex assumption remains. Empty graphs, empty demands, and disconnected graphs are inherited from the accepted conditional theorem. This is an existence result, not a running-time claim or whole-paper completion.

## Scope and preservation

One mathematical file is added: `SlackSparsification/PlusSixIntegration.lean`. The aggregate `SlackSparsification.lean` gains eleven imports (the ten subset +2 modules and the integration module). Its 36 imports exactly match the 36 library modules, with no missing, extra, or duplicate entries; see [module-index check](evidence/module-index.json).

A separate `verification/PlusSixIntegrationAudit.lean` extends coverage without rewriting any prior audit file. All accepted mathematical leaf sources and previous evidence remain unchanged. The aggregate source/object change is intentional and authorized. The certified checkout remains clean at `dc376e8efac8c1bc236abbe68d296060d7ba4142`. No website or workflow was changed.

[Prior review record](REVIEW.md) attributes acceptance of subset +2 source `3479c6c51ddf7e970f13cb263128fba8fdd36000` and evidence `d199b99c6d3902e2b827a2b5c3efef072c2fa88a` to the parent's independent source/log/hash reconciliation. That review was not fresh execution or CI. The new integration is awaiting independent review.

## Fresh sequential validation

Environment connected successfully: 23 GiB free disk; 16 GiB cgroup RAM limit; four CPU quota cores. No Lean/compiler/checker process was active at entry. Only one worker was used.

Official Lean **4.34.0**, commit **293d5d0c0c3f3dded4688b3ccd6a33939ac5102b**, and Lake **5.0.0-src+293d5d0**. Mathlib remains **5ed2965256430c3649e86755f9576b54eca72435**. All nine dependency checkouts match `lake-manifest.json` and remain clean. Fresh version/executable hash checks are recorded; official release-archive provenance remains the previously preserved evidence, not a new archive comparison this turn.

Both new-module and aggregate compilations ran sequentially with the official binary:

```text
lean -j1 -DautoImplicit=false -DwarningAsError=true --root=<paper-root> -o <object> <source>
```

| Operation | Result | Raw evidence |
| --- | --- | --- |
| Integration compilation | exit 0, zero diagnostics/warnings | `attempt-001.*` |
| Aggregate compilation | exit 0, zero diagnostics/warnings | `attempt-002.*` |
| Exact leaf kernel replay | exit 0 | `replay-Integration.*` |
| Combined recursive audit | exit 0 | `replay-Audit.*` |

Exact replay: `lake env leanchecker -v SlackSparsification.PlusSixIntegration`. Its selected module name was checked to match exactly one leaf; raw output is exactly `replaying SlackSparsification.PlusSixIntegration`. The import-only aggregate was strictly compiled, not replayed as a namespace prefix (which would select many modules). Previously accepted leaf modules were not rebuilt or freshly replayed in this turn.

Exact audit:

```text
lake env lean -j1 -DautoImplicit=false -DwarningAsError=true "A Note on Distance-Preserving Graph Sparsification/verification/PlusSixIntegrationAudit.lean"
```

Audit PASS: **373 actual-owner project declarations**, **19,646 recursive constants**, **14 opaque bodies**. Coverage includes the full imported SlackSparsification project and its two existing imported distance-preserver support modules; no other paper was developed or compiled. Recursive type/body traversal includes private declarations and opaque bodies and rejects unsafe/partial constants and disallowed axioms. The only axioms are **`propext`, `Classical.choice`, `Quot.sound`**.

The audit's “148 new declarations” label refers to its selected set of four +6 modules, ten subset +2 modules, and the integration module; **only one declaration is newly introduced by this integration**. Per-owner counts are in [audit coverage](audit-coverage.json). Prior warnings retain their earlier classification; the two fresh compilations have no warnings.

There were no failed compiler, kernel, or audit attempts. One evidence-collection attempt failed because it initially required the intentionally rebuilt aggregate object to match the previous hash. Its script snapshot and failure diagnostic are preserved as `collector-attempt-001.*`; the corrected collector excludes that intentional replacement from unchanged-object comparisons and succeeds. No compiler retry or source correction was needed.

## Review evidence

- [Source/object SHA256 hashes](source-object-hashes.json): final source snapshots match the exact tested commit.
- [Raw compilation/replay/audit evidence](evidence/): exact commands/options, `LEAN_PATH`, elapsed times, exit codes, full source snapshots, and raw diagnostics.
- [Recursive dependency chunk manifest](evidence/dependency-chunk-manifest.json): concatenation in manifest order exactly reconstructs the raw TSV and SHA256.
- [Preservation checks](preservation.json), [dependency pins](dependencies.json), [runtime hashes](toolchain-binary-hashes.json), and [resource/process/version diagnostics](environment.json).
- `checkpoint-evidence-hashes.json` hashes every other checkpoint file.

All compiler/checker processes have exited. Source and evidence are separate additive commits on `checkpoint/subset-plus2-cgk13-20261015`, both with `[skip ci]`. Existing workflow guards exclude this branch from the multi-paper job, and the dedicated gate listens on the integration branch. No CI trigger was requested. Independent review is the next step before any coordinated CI; there is no remaining local validation blocker.
