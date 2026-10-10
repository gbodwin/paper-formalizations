# Unverified source preservation snapshots

These working proof sources are stored as `.lean.txt` files and excluded from
library imports and CI compilation. They may contain unfinished proofs or
compilation errors. This backup makes no verification claim.

The newest complete source-state manifest is
[20261010T1043Z/source-manifest.json](20261010T1043Z/source-manifest.json).
It records 103 files by exact SHA-256 and snapshot path. This update
adds 63 changed source files; unchanged files retain the earlier
paths listed in the manifest. Earlier backups remain available.

The separate verified partial checkpoint contains 174 components and 11,053
owned declarations:
https://github.com/gbodwin/paper-formalizations/commit/fc11ede6a4c581c35163dba0698128057895c34d
Its exact-commit CI passed the library build, module index, axiom audit,
execution regressions and project-module kernel replay:
https://github.com/gbodwin/paper-formalizations/actions/runs/38011321856

A newer 193-component integration candidate is pending its own full checks:
https://github.com/gbodwin/paper-formalizations/commit/2e19b3be2fa66095b2d77b80943514d47ccfde3e
That candidate and this larger source backup are distinct. The complete paper,
including its full algorithm/runtime proof and companion reading site, remains
unfinished.

Source-backup commits intentionally skip CI. A green build of this branch's
older baseline would not verify these `.lean.txt` drafts. Verified integration
checkpoints continue to run the full checks.
