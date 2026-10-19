# SCC internal connector: independent-review handoff

Tested source: **`b2f6cbd033c8aa87597f09d11aa7f3655f1e245d`**. Original execution evidence: **`5b6873aa7061149b187bb5e8e7999181fff5b40d`**. The requested construction was already present when this session connected. This additive handoff freshly reconciles preserved source, logs and hashes; it performs **zero fresh compiler/checker/audit/CI invocations**. Independent review of this later endpoint remains pending. The accepted predecessor remains source `b3ea492e33df053dd186d0fe1d7c7499909c2fb0`, evidence `11690f560db73f1f05ef121d5687a1e088168482`; its reported review is source/log/hash reconciliation, not fresh execution.

## Mathematical result

[SCCInternal.lean](../../A%20Note%20on%20Distance-Preserving%20Graph%20Sparsification/SlackSparsification/SCCInternal.lean) constructs the induced graph on each SCC vertex subtype. `component_induced_reachable` restricts allowed paths using `support_same_component`. `exists_component_connector` chooses a representative root, applies `exists_root_preserver` with zero weights, obtains actual allowed walks from finite preserved distance, filters to induced input arcs, and maps those arcs back to the original vertices.

`component_fiber_card_sum` proves that the sum of component sizes equals the original vertex count. The finite union in `exists_internal_connector` therefore uses at most **`2*n` arcs total**. The fiber identity handles empty vertex types; the local construction connects all same-component pairs, including coincident endpoints.

`sourcewise_bound_uniform` discharges the connector premise and proves `SourcewiseBound K A 4` for arbitrary orientations. `bidirectional_sourcewise_uniform` instantiates it for A and its reversal. `exists_reachability_preserver` applies the existing HalfCover/amplification theorem to produce actual input arcs preserving every demanded reachability equivalence, with cardinality bound

`8*n + 25*n^(2/3)*p^(2/3)/(1-(1/2)^(2/3))`.

No connector, sourcewise, acyclicity, supplied-path or hitting-set premise remains in this endpoint. Its domain is a finite vertex type, an ambient simple graph, an arbitrary directed allowed relation, and a finite ordered demand set. Same-SCC, coincident, empty and unreachable cases are included. This is a finite reachability existence result, without a stronger weighted-distance or runtime claim. No whole-paper completion or acceptance is claimed.

## Preserved execution evidence

Official Lean **4.34.0**, mathlib **`5ed2965256430c3649e86755f9576b54eca72435`**; all nine installed dependency revisions still match the manifest. Exact executable, source and object hashes, options, paths, environments, lock/PID/timing records and submitted-source snapshots remain in the original evidence.

- Source SHA256: `07755149fd36fc495bc55900e98bf4358ee098aba1b2f0b21f459e367e8323ed`, 6669 bytes.
- Object SHA256: `e3dfed85bece82d6906c7a0179841f9cb263b86a9dd6d067c6c28bfc2f802750`.
- Successful compile: official `lean -j1 -DautoImplicit=false -DwarningAsError=true --root=… -o …/SlackSparsification/SCCInternal.olean …/SCCInternal.lean`, exit 0, zero actual warnings.
- Individual kernel replay: official `leanchecker -v SlackSparsification.SCCInternal`, exit 0.
- Recursive audit: official `lean -j1 -DautoImplicit=false -DwarningAsError=true …/verification/SCCInternalAudit.lean`, exit 0, 223 actual-owner roots (nine new), 18,871 constants and 14 opaque values. Only `propext`, `Classical.choice`, and `Quot.sound` occur as axioms.

The audit follows constant types, definition/theorem/opaque values and inductive constructor links, rejecting unsafe/partial dependencies and other axioms. This handoff does not assert coverage beyond the preserved audit implementation. Historical validation was incremental with recorded local objects and candidate fallback, not a clean rebuild.

All four unique source-bound receipts reconcile: one failed compile, one successful compile, one replay, one audit, with historical lock identity, strict non-overlap and reaped children. The failed subtype/Fintype cardinality elaboration attempt and its raw diagnostics remain immutable; the explicit fiber-cardinality equivalence repaired that proof. No mathematical counterexample was found.

## Current reconciliation and disposition

The [read-only reconciliation](reconcile.py), [exact invocation](invocation.txt), [raw output](reconciliation.log), and [machine-readable findings](reconciliation.json) verify all **69 original manifest entries**, all **41 ordered chunks**, the exact 8,060,122-byte reconstruction (SHA256 `d9da57d42a480b549aa251e304782c970fce44067d964072bc9870721bdb0829`), recursive closure, original receipts, all recorded current source/object/executable bindings, dependency pins, and prior reconciliation manifests. No original evidence or proof was rewritten.

At 2026-10-19 16:22:17 UTC: disk free 3,260,833,792 bytes; host MemAvailable 17,374,004 KiB; cgroup memory limit 17,179,869,184 bytes. No Lean/Lake/checker process was active. The common lock was observed without acquisition: device 33/inode 3258, mode 0600, no matching `/proc/locks` entry. Historical executions used device 33/inode 3849; no cross-session inode continuity is asserted. Any future compiler operation requires the common exclusive lock and a new source-bound receipt.

Remote branch `checkpoint/scc-internal-20261016` matched local HEAD `faf098201e9929894befa53d28c579587c9c2b38` before this additive publication. Only this handoff directory is published with `[skip ci]`. Proof source, accepted evidence, certified branch, workflows, websites and other papers remain unchanged. Pause for independent review; no compiler/checker remains running.

Reviewer entry points: [original report](../scc-internal-20261016/REPORT.md), [exact commands and receipts](../scc-internal-20261016/evidence/commands.jsonl), [source/toolchain/object bindings](../scc-internal-20261016/evidence/source-toolchain-object-hashes.json), [chunk reconstruction manifest](../scc-internal-20261016/audit-export/manifest.json).
