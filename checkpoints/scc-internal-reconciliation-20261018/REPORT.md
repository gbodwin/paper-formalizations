# SCC internal connector: preserved proof checkpoint ready for review

Tested mathematical source: **`b2f6cbd033c8aa87597f09d11aa7f3655f1e245d`**.
Original evidence: **`5b6873aa7061149b187bb5e8e7999181fff5b40d`**.
This dated supplement reconciles an already completed, already published checkpoint. It performs no fresh Lean compilation, kernel replay, recursive Lean audit, CI, dependency retrieval or proof modification. Independent review of this endpoint remains pending. No whole-paper completion is claimed.

The user's acceptance of predecessor source `b3ea492e33df053dd186d0fe1d7c7499909c2fb0` and evidence `11690f560db73f1f05ef121d5687a1e088168482` is recorded as source/log/hash review, not execution or CI. The predecessor retained the internal-connector premise. All predecessor proofs, conditional source and evidence remain unchanged.

## Result and scope

The preserved [SCCInternal source](../../A%20Note%20on%20Distance-Preserving%20Graph%20Sparsification/SlackSparsification/SCCInternal.lean) implements the requested construction:

- Restrict each SCC to its vertex subtype and induced ambient graph; `support_same_component` justifies allowed reachability inside it.
- Choose a root and apply `exists_root_preserver` with zero weights. Finite preserved distances give actual allowed paths into and out of the root.
- Filter to induced input arcs and map back to original arcs.
- Prove the exact component-fiber cardinality sum equals `n`; union connectors with total budget at most `2*n`, including empty graphs.
- Discharge the connector premise in `sourcewise_bound_uniform`, proving sourcewise `C = 4` for arbitrary orientations. Instantiate the same theorem for reversal in `bidirectional_sourcewise_uniform`.
- Apply HalfCover and amplification in `exists_reachability_preserver`, with actual input arcs, preservation equivalence for each demanded pair, and bound
  `8*n + 25*n^(2/3)*p^(2/3)/(1-(1/2)^(2/3))`.

The endpoint assumes a finite vertex type, an ambient simple graph, an arbitrary directed allowed relation supported along ambient walks, and a finite ordered demand set. It has no sourcewise, connector or acyclicity premise. Unreachable demands, coincident endpoints and same-component demands are covered. This is a finite reachability existence theorem; no stronger weighted-distance or runtime theorem is asserted.

## Reconciled verification evidence

The original [report](../scc-internal-20261016/REPORT.md), [commands and options](../scc-internal-20261016/evidence/commands.jsonl), [source/object/toolchain hashes](../scc-internal-20261016/evidence/source-toolchain-object-hashes.json), and [ordered audit chunks](../scc-internal-20261016/audit-export/manifest.json) remain unchanged.

Official toolchain pin is Lean `4.34.0`; mathlib is `5ed2965256430c3649e86755f9576b54eca72435`. The nine installed dependency commits match `lake-manifest.json`. Source SHA256 is `07755149fd36fc495bc55900e98bf4358ee098aba1b2f0b21f459e367e8323ed`; object SHA256 is `e3dfed85bece82d6906c7a0179841f9cb263b86a9dd6d067c6c28bfc2f802750`. All recorded source, object and executable bindings still match available files.

The preserved successful commands used strict compile options `-j1 -DautoImplicit=false -DwarningAsError=true`, individual `leanchecker -v SlackSparsification.SCCInternal`, and the strict SCCInternal audit. All three exited zero. There were **zero warnings** in the final compile. The one failed compiler attempt is a subtype/Fintype cardinality elaboration mismatch, repaired by an explicit fiber cardinality equivalence; its complete source and diagnostics are preserved. This is a proof repair, with no mathematical counterexample reported.

Reconciliation verified all **69 manifest entries**, **41 chunks**, **four unique source-bound locked receipts**, non-overlap and child reaping. The recursive export reconstructs **8,060,122 bytes**, SHA256 `d9da57d42a480b549aa251e304782c970fce44067d964072bc9870721bdb0829`. It has **223 actual-owner roots**, including nine from SCCInternal, and an exactly reachable **18,871-constant closure**, with 14 opaque values and only `propext`, `Classical.choice`, and `Quot.sound` as axioms. Audit traversal covers constant types, definition/theorem/opaque values and inductive constructor links as implemented in the preserved audit source; this supplement does not claim a new or stronger audit algorithm.

This is incremental evidence: original checks used recorded local object search paths and the original candidate fallback. It is not a clean rebuild. The current supplement merely reads and hashes those artifacts and reconstructs their dependency export.

## Reproduction and disposition

Run `python3 -B checkpoints/scc-internal-reconciliation-20261018/reconcile.py` from this checkout to repeat this non-compiler reconciliation. Its exact invocation and two failed script attempts are preserved. The first incorrectly treated evidence source snapshots as changed project sources; the second compared against the predecessor source rather than its evidence commit. Both were corrected only in the reconciliation script, and neither invoked Lean. See [reconciliation.json](reconciliation.json) for receipts, current bindings and resources.

At reconciliation, disk free was approximately 4.69 GiB, available host memory approximately 16.6 GiB. No Lean/Lake/checker process was active; universal lock `/tmp/distance-sparsification-single-compiler.lock`, device 33/inode 3849, was free. This additive evidence-only supplement is published with `[skip ci]`, with no workflow trigger or website change. The worker remains idle for independent review.
