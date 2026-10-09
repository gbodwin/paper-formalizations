# Unverified source preservation snapshots

These working proof drafts are not compiled by CI and carry no verification
claim. They may contain unfinished proofs or compilation errors. They are
preserved as `.lean.txt` so they cannot be mistaken for included library modules.

The newest snapshot is 20261009T1331Z (26 source files). Its per-file
hashes are recorded in that directory's source-manifest.json. Earlier dated
snapshots and the first root-level snapshot remain available.

The separate checked partial checkpoint contains 153 modules and 9,789 unique
owned declarations:
https://github.com/gbodwin/paper-formalizations/commit/46f5a5777c70f1c03f09c5d026fb67239e802b8d
Its local compilation, axiom, index, kernel and independent component gates passed.
Exact-commit CI run37931631063 also passed, including every project module’s
isolated kernel replay.

The CI on this draft branch checks its older 90-module baseline only. A green
result does not verify any draft in this directory. These latest drafts refer
to the newer checked source tree above. The full paper remains incomplete.
