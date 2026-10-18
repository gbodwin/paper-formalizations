# Focused wrapper corrections — Python-only delta

Base implementation: **506a136c64a35126002330e804a476ccdda8dc36**. This additive checkpoint copies its 14 Python files, changes exactly three, and adds a focused test file. The original checkpoint, all historical receipts, accepted sources/pins and staged Lean drafts remain unchanged. For future production review, use this revised checkpoint rather than the preserved historical wrapper.

**No Lean, fixture/production workload child, production entry, lock acquisition, kernel-limit change or resource probe was run.** Normal local Git metadata reads and authorized publication are separate from these fixtures. Compilation and production validation remain pending independent delta review and fresh coordinated ownership.

## Three source changes

[focused_audit.py](focused_audit.py) retains the raw dependency columns, rejects empty names and dangling references, and deduplicates combined type/body edges only for traversal. The positive fixture uses verbatim preserved And.rec, Nat.rec and List.rec rows and their complete 11-constant closure. And.rec's body field remains exactly And,And.intro,And,And.intro. The synthetic new-module root produces a 12-constant test closure; this is a parser test, not a new Lean audit.

The same file now checks actual chunk boundaries: every non-final part must end in LF, and empty parts are rejected. Valid hashes and row_aligned=true cannot hide a mid-row split. A final partial raw-log row remains permitted; table validators independently require final LF. Complete reconstruction, order/path/hash/size and other existing checks remain in place.

[output_guards.py](output_guards.py) now inspects active output metadata only: allowed file/directory paths, regular files, single links and existing size budgets. It does not read/hash active contents or demand stable size/mtime/ctime during growth. Completed object/resolution/input signatures remain independently protected. Stable content hashing is still performed by the unchanged completed-output binders and post-owned-termination scope hooks. Tests reject unexpected files/directories, symlink roots/files, hardlinks, FIFOs and oversized object/audit outputs.

[child_runner.py](child_runner.py) selects stage-specific FSIZE before constructing the receipt. Its memory-policy summary therefore records 16 MiB for compile/resolve/replay and 64 MiB for audit, matching the unchanged launcher configuration. The fixture repeatedly transitions audit-to-compile to expose stale summaries and compares receipts with mocked launcher limit readbacks, stopping before admission or launch.

[delta.diff](delta.diff) is the exact three-file diff against the reviewed base. Eleven copied Python files are byte-identical. Ownership, inherited FD checks, reaping, admission/resource values, first-failure stopping, source/object bindings and the scope of the proposed four Lean stages are unchanged. No full graph reconciler, rebuild or broader runtime redesign was added.

## Focused evidence

Final command:

    python3 -B checkpoints/light-eft-supplied-forest-wrapper-delta-20261018/test_delta.py

Result: **15 tests passed**, zero failures/errors, with child-launch and resource-probe functions patched to raise if invoked.

- [Final raw log](tests-02.log)
- [Final test results](test-evidence/b9a0b0a1ad504a6694b7253c369972d6/test-results.json)
- [Fixture provenance](fixtures/provenance.json)
- [Verbatim recursor rows](fixtures/faithful-recursors.tsv)
- [Preservation and source-delta summary](preservation.json)

Both focused runs and their source snapshots remain preserved. The first run passed; the final run clarifies fixture code and tests link/nonregular rejection for both compile and audit outputs. FSIZE fixtures preserve initial receipt construction only: they intentionally stop before admission and have no launched child, so they are not execution receipts. Oversize fixtures use sparse test files, record their logical sizes/rejections, then remove only those new test files. No accepted or historical artifact is removed.

The previous 506a136c manifest and every one of its 2,640 evidence bindings were rechecked without altering them. This checkpoint's manifest preserves rejected-input fixtures as test data and hashes symlink target text without following it. No new mathematical acceptance, kernel execution, CI result or whole-paper completion is claimed.

Published only on light-eft-spanners-checkpoints with [skip ci]; exact remote verification is required before handoff. The worker remains idle for independent delta review before any Lean execution.
