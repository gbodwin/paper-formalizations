# Preserved SCC connector endpoint: review handoff

Tested source: **`b2f6cbd033c8aa87597f09d11aa7f3655f1e245d`**. Original proof evidence: **`5b6873aa7061149b187bb5e8e7999181fff5b40d`**. The requested construction was already implemented and published when this session connected. This supplement verifies existing source, logs and hashes; it makes **zero fresh compiler/checker/Lean audit/CI invocations**. Independent review of this endpoint remains pending. It does not grant acceptance or claim whole-paper completion.

The accepted predecessor `b3ea492e33df053dd186d0fe1d7c7499909c2fb0`, evidence `11690f560db73f1f05ef121d5687a1e088168482`, and all subsequent proofs/evidence remain unchanged. User-reported predecessor acceptance is recorded as independent source/log/hash reconciliation, not fresh execution.

## Mathematical endpoint

[SCCInternal.lean](../../A%20Note%20on%20Distance-Preserving%20Graph%20Sparsification/SlackSparsification/SCCInternal.lean) uses the induced graph on each SCC vertex subtype. `support_same_component` restricts allowed paths to that subtype. `exists_component_connector` chooses a representative root, applies `exists_root_preserver` with zero weights, derives actual allowed walks from finite preserved distance, filters to induced input arcs, and maps arcs back to original vertices.

`component_fiber_card_sum` proves the exact sum of component cardinalities equals `n`. `exists_internal_connector` unions the connectors with at most **`2*n` arcs total**, including the empty graph. `sourcewise_bound_uniform` discharges the connector premise with **C = 4** for arbitrary orientations; `bidirectional_sourcewise_uniform` also handles reversal. `exists_reachability_preserver` applies HalfCover and amplification to obtain actual input arcs and demanded reachability equivalence, with bound

`8*n + 25*n^(2/3)*p^(2/3)/(1-(1/2)^(2/3))`.

No connector, sourcewise, DAG, supplied-path or hitting-set premise remains in this finite reachability endpoint. Assumptions remain a finite vertex type, ambient simple graph, arbitrary directed allowed relation, and finite ordered demand set; paths use ambient adjacency. Same-SCC demands, coincident endpoints and unreachable demands are included. This is an existence theorem, with no runtime or stronger weighted-distance claim.

## Preserved verification and present reconciliation

Official toolchain: **Lean 4.34.0**, mathlib **`5ed2965256430c3649e86755f9576b54eca72435`**; all nine installed dependency revisions match the manifest.

- Source SHA256: `07755149fd36fc495bc55900e98bf4358ee098aba1b2f0b21f459e367e8323ed` (6669 bytes).
- Object SHA256: `e3dfed85bece82d6906c7a0179841f9cb263b86a9dd6d067c6c28bfc2f802750`.
- Successful compile: official `lean -j1 -DautoImplicit=false -DwarningAsError=true --root=… -o …/SlackSparsification/SCCInternal.olean …/SCCInternal.lean`, exit 0, **zero actual warnings**.
- Individual replay: official `leanchecker -v SlackSparsification.SCCInternal`, exit 0.
- Recursive audit: official `lean -j1 -DautoImplicit=false -DwarningAsError=true …/verification/SCCInternalAudit.lean`, exit 0; **223 actual-owner roots**, nine owned by SCCInternal, **18,871 reachable constants**, 14 opaque values; only `propext`, `Classical.choice`, `Quot.sound` are axioms.

Audit coverage is the preserved algorithm: all root and recursive constant types, definition/theorem/opaque values, and inductive constructor links. Unsafe/partial declarations and unapproved axioms are rejected. This supplement does not assert additional traversal beyond that implementation.

The one failed compile is preserved with its exact submitted source and raw diagnostics. It was a subtype/Fintype cardinality elaboration mismatch, repaired using an explicit fiber-cardinality equivalence; no mathematical counterexample was found. All four UUID source-bound historical receipts reconcile, with one historical lock inode, strict non-overlap and reaped children. The checks were incremental using their recorded object paths and candidate fallback, **not a clean rebuild**.

Reconciliation verifies **69 manifest entries**, **41 ordered chunks**, an 8,060,122-byte reconstruction with SHA256 `d9da57d42a480b549aa251e304782c970fce44067d964072bc9870721bdb0829`, exact recursive closure, every recorded current source/object/executable binding, dependency pins, and preservation of prior reconciliation manifests.

Exact historical commands/options/environment and all receipts: [commands.jsonl](../scc-internal-20261016/evidence/commands.jsonl). [Raw evidence and report](../scc-internal-20261016/REPORT.md), [hash bindings](../scc-internal-20261016/evidence/source-toolchain-object-hashes.json), [chunk reconstruction manifest](../scc-internal-20261016/audit-export/manifest.json). Current [machine-readable reconciliation](reconciliation.json), [raw output](reconciliation.log), [script](reconcile.py), and [invocation](invocation.txt) are additive. No historical file was rewritten.

## Current environment and disposition

At reconciliation, disk free was 3850915840 bytes, host MemAvailable 17380300 KiB, and cgroup memory limit 17179869184 bytes. No Lean/Lake/checker was active. The common lock path exists at device 33/inode 3258, mode 0600, with no matching `/proc/locks` entry; it was observed read-only, never acquired or replaced. Historical executions used device 33/inode 3849. **No historical lock-inode continuity is asserted.** Any future compiler work must use the common exclusive protocol with new source-bound receipts.

The existing remote checkpoint branch was verified at `6a786af41fd10a74a0ca642338161442d1791738` before this supplement. Publish this additive evidence only to `checkpoint/scc-internal-20261016` with `[skip ci]`; no proof source, certified branch, workflow, website or other paper is changed. Pause for independent review. No compiler process remains running.
