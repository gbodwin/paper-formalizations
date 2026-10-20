# Same-run staged artifact transfer and retained inputs

Use RUNNER_TEMP roots derived from the authenticated ordinary CI identity:
paid = light-eft-paid-focused-RUN-ATTEMPT; decoder = light-eft-staged-RUN-ATTEMPT;
new bridge = light-eft-paid-joint-bridge-RUN-ATTEMPT. Require exact SHA, run ID,
attempt, event, job and runner context, with immutable current Git source/spec
bindings. Do not accept user-provided archive paths or old run/attempt roots.

1. Reuse accepted ci_handoff.indexed_evidence to authenticate each complete prior
   evidence index: every indexed file has its exact bytes/hash/identity, every
   actual file is indexed, no symlink or nonregular member exists, and the index
   itself is bound. Treat all prior result, lease, plans, owner/claim documents,
   source snapshots, objects, journals, resolutions, audit exports, chunks and raw
   logs as immutable inputs. Reject missing or additional files. Do not write
   anything into either completed gate's root.

2. Reuse accepted ci_handoff.verify_decoder unchanged for the decoder gate's
   exact four receipts, source fingerprint, 43 observed owner declarations,
   boot/namespaces, clean released lease/ECHILD, singleton resolution/replay,
   emitted parts, audit scope and retained input journal. Its historical frozen
   tag is preserved as a qualification, not substituted for current event SHA.

3. Authenticate the paid gate's exact nine planned children from its current
   bound source. Reuse verify_receipts unchanged for each four-stage module and
   verify_singleton_receipt unchanged for the fixture. Require the paid result's
   accepted flag, exact source/harness SHA and CI identity, all nine distinct
   attempt IDs in strict order, successful states, and its clean released lease.
   Inspect the current CILease schema: verify its boot_id, namespace, lock path,
   lock device/inode and directory identity against current kernel observations.
   Do not invent a paid fresh-CI-owner document that its producer does not emit.
   Retain its exact import contracts: serialization13/14 and composition17/18
   (excluding/including each target), with all16 ordinary dependencies still
   bound. The fixture receipt uses those16 plus both completed paid modules.

4. Reconcile the paid result's output ledger with all eight module receipts and
   actual complete shared object root. Each module's own outputs_after ledger is
   taken from the relevant stage's complete current union: the first object must
   remain identical through the second module and fixtures. Require both exact
   primary objects, their actual regular singly linked companions, legal suffix
   families, and .ir.sig implying .ir. Accept only a complete legacy primary or
   complete primary/server/private module parts. No borrowed partial family,
   duplicate primary, foreign sibling, dangling link or target-prefix extension.

5. Use original paid work/objects and decoder work/objects as immutable search
   roots, between the fresh bridge output root and the normal build roots. Their
   top-level package markers are disjoint from the bridge marker. Verify selected
   first-package paths for all 80 imports, exact singleton bridge target selection
   and no shadowing/prefix modules. Never split the paid package root or fall back
   past a package marker. Bind the full prior directories and companion sets,
   not only the three .olean primary paths.

6. Retain the complete paid and decoder input journals. Reuse the semantics of
   accepted retained_context: compare prior rows with already computed fresh
   exact inputs, and require equal semantic membership in both directions for
   each original normal-build/package/toolchain root. Reject changes, added or
   removed companions, metadata/runtime inputs and source/helper inputs. Merge
   all prior critical source/control rows into the new sealed input inventory;
   do not silently drop earlier inputs absent from the new target's direct set.
   The new bridge output root is fresh and outside prior retained roots.

7. Require every paid child to precede every decoder child and every decoder
   child to precede the first bridge child. The earlier gates' leases must be
   released before the new lease is acquired. Verify no duplicate child attempt
   ID and no active local compiler/checker/tracer immediately before claim and
   each spawn. The parent coordinates the repository-wide exclusive publication
   window; workflow concurrency serializes jobs. Do not describe per-root leases
   as a cross-host kernel lock.

This is an authenticated same-run handoff of preserved artifacts at their original
paths. The final and immediate GitHub uploads are evidence retention only, not
runtime object downloads. The accepted older artifact 12294271061 and its Library
transport are review evidence and must never supply a new run's dependencies.
