# SCC connector checkpoint: resumed-session reconciliation

The requested construction is already preserved at tested source **`b2f6cbd033c8aa87597f09d11aa7f3655f1e245d`**, with original evidence **`5b6873aa7061149b187bb5e8e7999181fff5b40d`**. Published reconciliation `aef53ce74e3e50943dc78e28293af8103e8aec2e` was present when this session connected. This additive supplement changes no proof or earlier evidence and performs **no fresh Lean execution, kernel replay, Lean axiom audit, or CI**. Independent review of this endpoint remains pending.

The user's acceptance of predecessor source `b3ea492e33df053dd186d0fe1d7c7499909c2fb0` / evidence `11690f560db73f1f05ef121d5687a1e088168482` is recorded as independent source/log/hash reconciliation, not execution.

## Mathematical result preserved

[SCCInternal.lean](../../A%20Note%20on%20Distance-Preserving%20Graph%20Sparsification/SlackSparsification/SCCInternal.lean) restricts each SCC to its vertex subtype and induced ambient graph using `support_same_component`. It applies `exists_root_preserver` with zero weights, obtains actual paths from finite preserved distances, filters to induced input arcs and maps them back. The exact fiber identity sums component sizes to `n`, so their union costs at most `2*n` total, including empty inputs.

`sourcewise_bound_uniform` discharges the connector premise and proves `SourcewiseBound K A 4` for arbitrary orientations. `bidirectional_sourcewise_uniform` covers reversal. `exists_reachability_preserver` combines this with HalfCover/amplification, producing actual input arcs with demanded reachability equivalence and bound

`8*n + 25*n^(2/3)*p^(2/3)/(1-(1/2)^(2/3))`.

No connector, sourcewise, DAG or supplied-path premise remains in this finite reachability endpoint. Same-component endpoints and unreachable demands are included. This is an existence result in the existing finite ambient-simple-graph/oriented-arcs model; no runtime, stronger weighted-distance, or whole-paper completion claim is made.

## Evidence checked in this session

The read-only reconciliation verifies all **69** original manifest entries, **41** ordered chunks reconstructing **8,060,122 bytes**, **four** source-bound locked receipts with non-overlap and reaped children, and unchanged source/toolchain/object hashes. The recorded audit has **223 roots**, an exactly reachable **18,871-constant closure**, 14 opaque bodies, and only `propext`, `Classical.choice`, `Quot.sound` as axioms. The nine dependency commits match the manifest. These are reconciled historical results, not fresh proof checks.

Source SHA256: `07755149fd36fc495bc55900e98bf4358ee098aba1b2f0b21f459e367e8323ed`.
Object SHA256: `e3dfed85bece82d6906c7a0179841f9cb263b86a9dd6d067c6c28bfc2f802750`.
Official toolchain: Lean 4.34.0; mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

The preserved successful compile used `-j1 -DautoImplicit=false -DwarningAsError=true` and emitted zero warnings. Individual `leanchecker -v SlackSparsification.SCCInternal` and the strict recursive audit exited zero. One failed compile, caused by a subtype/Fintype cardinality elaboration mismatch, and its submitted source remain preserved. Full [commands/receipts](../scc-internal-20261016/evidence/commands.jsonl), [original report](../scc-internal-20261016/REPORT.md), [hash bindings](../scc-internal-20261016/evidence/source-toolchain-object-hashes.json), and [chunk manifest](../scc-internal-20261016/audit-export/manifest.json) are unchanged. Original checks were incremental with their recorded object paths, not a clean rebuild.

## Current environment qualification

The historical lock path `/tmp/distance-sparsification-single-compiler.lock` is **absent in this session**. The old reconciliation script therefore fails on its runtime lock-inode check; [raw diagnostic](failed-historical-lock-check.log) is retained. The resumed reconciliation changes only that current-environment observation, retaining verification of the four historical receipts and their common device 33/inode 3849. It does not create a replacement lock or assert inode continuity.

No compiler/checker was invoked. Current process inspection found none active; approximately **4.68 GiB disk** and **16.66 GiB available host RAM** were reported. Fresh compiler work would require re-establishing the common lock across participants first. The mathematical endpoint and preserved verification evidence are available for independent review now.

Reproduce only the evidence reconciliation with `python3 -B checkpoints/scc-internal-resume-20261018/reconcile.py`. [Machine-readable results](reconciliation.json) include source bindings, historical receipts and current resources. The worker pauses for review; no site or certified branch was changed. Publish this evidence-only supplement with `[skip ci]`.
