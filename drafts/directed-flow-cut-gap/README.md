# Unverified source preservation snapshots

These working proof drafts are not compiled by CI and carry no verification
claim. They may contain unfinished proofs or compilation errors. They are
preserved as `.lean.txt` so they cannot be mistaken for included library modules.

The newest snapshot is 20261009T1905Z (41 source files). Its per-file
hashes are recorded in that directory's source-manifest.json. Earlier dated
snapshots and the first root-level snapshot remain available.

The separate checked partial checkpoint contains 162 modules and 10,328 unique
owned declarations:
https://github.com/gbodwin/paper-formalizations/commit/2f3c83e2f3988e75a8800132004c9650a425368f
Its local compilation, axiom, index, kernel and independent component gates passed.
Exact-commit CI run 37960050945 passed all stages on 2026-10-09 at 17:06 UTC,
including the full library build, module indexes, exhaustive declaration audits
and isolated kernel replay of every project module.

Source-only snapshot commits intentionally skip CI: these .lean.txt files are
excluded from library imports and compilation. Older CI runs on this draft
branch check only its older 90-module baseline; a green result does not verify
any draft in this directory. Verified source checkpoints continue to run the
full CI gates. These drafts refer to the checked source tree above. The full
paper remains incomplete.
