# Unverified source preservation snapshots

These working proof drafts are not compiled by CI and carry no verification
claim. They may contain unfinished proofs or compilation errors. They are
preserved as `.lean.txt` so they cannot be mistaken for included library modules.

The newest snapshot is 20261009T1638Z (21 source files). Its per-file
hashes are recorded in that directory's source-manifest.json. Earlier dated
snapshots and the first root-level snapshot remain available.

The separate checked partial checkpoint contains 162 modules and 10,328 unique
owned declarations:
https://github.com/gbodwin/paper-formalizations/commit/2f3c83e2f3988e75a8800132004c9650a425368f
Its local compilation, axiom, index, kernel and independent component gates passed.
Exact-commit CI run 37960050945 was still in progress when this snapshot was
prepared. The preceding checked 153-module commit passed run 37931631063.
The current CI result must be checked separately at its exact commit.

The CI on this draft branch checks its older 90-module baseline only. A green
result does not verify any draft in this directory. These latest drafts refer
to the newer checked source tree above. The full paper remains incomplete.
