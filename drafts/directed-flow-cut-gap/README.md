# Unverified source preservation snapshots

These working proof drafts are not compiled by CI and carry no verification
claim. They may contain unfinished proofs or compilation errors. They are
preserved as `.lean.txt` so they cannot be mistaken for included library modules.

The newest complete draft-state manifest is
[20261009T2127Z/source-manifest.json](20261009T2127Z/source-manifest.json). It records
44 source files by exact SHA-256 and repository snapshot path.
This incremental snapshot adds 4 changed source files; unchanged
files remain at their earlier dated paths listed in the manifest. Earlier
snapshots and the first root-level snapshot remain available.

The separate checked partial checkpoint contains 162 modules and 10,328 unique
owned declarations:
https://github.com/gbodwin/paper-formalizations/commit/2f3c83e2f3988e75a8800132004c9650a425368f
Its local compilation, axiom, index, kernel and independent component gates passed.
Exact-commit CI run 37960050945 passed every stage on 2026-10-09 at 17:06 UTC.
The complete paper remains unfinished.

Source-only snapshot commits intentionally skip CI. These `.lean.txt` files are
excluded from library imports and compilation. Older CI runs on this draft
branch check only its older 90-module baseline; a green result does not verify
these drafts. Verified source checkpoints continue to run all CI gates.
