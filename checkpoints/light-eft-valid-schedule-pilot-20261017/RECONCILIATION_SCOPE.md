# Reconciliation writes derived evidence

`reconcile.py` does not execute Lean or leanchecker. It is **not filesystem-read-only**: it rewrites the current checkpoint's derived diagnostic classification, source/object provenance, owner delta, remaining partial-root inventory, preservation summary, reconciliation summary, ordered audit chunks and chunk manifest.

Its new module docstring states that behavior. Historical versions used “Read-only” to mean no compiler/checker execution; that label was misleading. The historical scripts, reports, manifests and outputs remain byte-identical. This is an additive correction, including for the accepted rounds checkpoint's label.

The script reads historical checkpoint data to verify hashes but never writes those historical directories. Run it before sealing the new evidence manifest. Re-executing it after publication is an evidence regeneration operation, even when the resulting bytes are identical. An independent read-only reviewer should instead verify the saved manifests, receipts, snapshots, hashes and chunks without invoking this writer.
