# Unverified source preservation snapshots

These working proof drafts are not compiled by CI and carry no verification
claim. They may contain unfinished proofs or compilation errors. They are
preserved as `.lean.txt` so they cannot be mistaken for included library modules.

The newest snapshot is 20261009T0947Z (27 source files). Its
per-file hashes are recorded in that directory's source-manifest.json.

The separately checked partial checkpoint contains 112 modules:
https://github.com/gbodwin/paper-formalizations/commit/c7241492b8444075b22f86fb68ec781e730a2f4b
Its local gates passed; its own remote CI must be checked separately.

Root-level `.lean.txt` files preserve the earlier 08:52 UTC draft snapshot.
The CI on this draft branch checks its older 90-module baseline only; a green
result does not verify any draft in this directory. The full paper remains
incomplete.
