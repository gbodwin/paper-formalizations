# Light EFT collision fixture: reviewed source transfer

This checkpoint contains source for a bounded runtime fixture and a narrowly scoped supervisor timing patch. The Lean fixture has not been elaborated or executed. Source inspection and earlier Python model checks do not establish Lean runtime lifetime correctness or a successful paper audit.

## Source identity

CollisionNativeFixtures.lean is self-contained and imports only Lean. It embeds OwnedCollisionScan.inc.lean exactly once. The helper copies declaration-name keys into independent scalar bytes and releases only its own newly read module regions in reverse dependency order. The fixture exercises same-module repetitions, cross-module and extra-name collisions, missing required parts, and key use after region release.

The manifest binds the exact files by relative path, byte length and SHA256. The source files are unchanged from the independently reviewed source-only preparation.

## Supervisor recovery

The public baseline is commit c66b8f879008262139f6d09f7130b3a6e055a866 in gbodwin/paper-formalizations:

checkpoints/light-eft-joint-flag-assignment-corrected-adapter-20261018/child_runner.py

preflight-timing.patch is a zero-context unified patch against that exact file. It adds the previously reviewed 300-second prespawn validation bound and invokes that validation before child creation. The baseline's portable HERE expression is retained. The 90-second child deadline and existing resource, telemetry and termination controls are unchanged. The manifest records both baseline and reconstructed supervisor hashes; verify both rather than applying the patch to an unbound version.

Other supervisor and lifecycle dependencies are available at the same pinned repository commit. This transfer is not a standalone launcher. Prepare and independently review a fixture-only launch plan for the current environment before execution, with fresh exclusive ownership, exact input bindings, unchanged limits, a fresh synthetic output directory, complete raw logs and owned cleanup.

No private runtime receipts, historical leases, machine identities, inventory, accepted objects or credentials are included. This checkpoint confers no execution authorization and makes no new mathematical, audit, clean-build or whole-paper completion claim.
