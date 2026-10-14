# Unverified Flow reconstruction backup

This is a source backup, not a verified formalization release.

The base is published Flow722, commit `ea1dfba989c89eb8ceed693cdad42ba8d96584f5`.
All 1,994 base files, the 722-source selection, existing proof bodies, verification
gates and workflow timeout are unchanged. The published checkpoint branch is
unchanged. This separate branch stores only additional draft files here.

After an executor replacement, the original unpublished final-dispatch draft
bytes, compiled objects and local verification receipts were unavailable. These
are newly reconstructed source drafts. Prior local results do not transfer to
them. The intended mathematical statements still need fresh strict compilation,
kernel replay, closure audits, numerical checks and independent review.

- `dispatcher/`: nine new program, composition and physical-simulation proof drafts
- `envelope/`: fixed-polynomial proof draft, fourteen-root audit source and seven
  numerical-only regression cases
- `STATUS.json`: exact snapshot hashes and explicit pending checks

No Lean check or physical fixture has been run on these new drafts. In particular,
there is no positive physical whole-program execution fixture. Represented input
roots, demand encoding, dense cursor and initial H/B remain explicit premises.
The covers result encodes the ordered state projection of high-level records.

The commit uses GitHub's `[skip ci]` marker solely to avoid triggering a duplicate
full workflow for an unverified source backup. No verification gate is weakened.
A skipped check is not a successful check. See [GitHub's documented behavior](https://docs.github.com/en/actions/how-tos/manage-workflow-runs/skip-workflow-runs).
