# Verification record

Prepared on 7 October 2026 against GitHub `main` commit
`f8ca8d97b4266d1fa704bbc261e14061921b6b59` of
`gbodwin/paper-formalizations`. The remote was reread before preparing the
review patch and still pointed to this commit. No GitHub branch, commit,
pull request, or website change was made during preparation.

## Checks performed

| Check | Result |
| --- | --- |
| Lean | 4.34.0, release commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` |
| mathlib | `5ed2965256430c3649e86755f9576b54eca72435` |
| Dependency checkouts | All nine match the unchanged lockfile |
| Full repository `lake build` | Passed, both libraries; 3,208 jobs in the reported build graph |
| New module index | Generated with `mk_all`; all eight proof modules imported |
| Both module-index checks | Passed |
| Module-origin axiom audit, new library | All 210 declarations passed |
| Module-origin axiom audit, existing VFT library | All 195 declarations passed |
| Exported theorem axiom dependencies | Only `propext`, `Classical.choice`, `Quot.sound`, or a subset thereof |
| Sequential Lean kernel replay | All 21 proof modules passed: 13 VFT and 8 new modules |
| Source review | No admitted proofs, custom axiom declarations, unsafe declarations, or native-decision proof shortcuts in the new proof modules |
| Whitespace check | `git diff --check` passed |

The standalone audit now imports both libraries and audits each by its
**defining module**, not its declaration namespace. It rejects any unapproved
axiom dependency and separately requires a nonzero declaration count for
each library. The existing CI action retains its VFT audit; the mandatory
standalone audit covers both libraries. Both module indexes are checked.

Kernel replay is Lean's own kernel rechecking the compiled declarations,
using imported mathlib environments. It is not an independent implementation
of the kernel or a rebuild of every dependency. Checks ran locally; no new
GitHub Actions run has occurred because the changes have not been pushed.

## Mathematical scope

The [coverage table](README.md#coverage) is part of the verification claim.
In particular `theorem_one_of_consistent_selection` has explicit selection
and consistency hypotheses. The axiom audit does not prove those inputs
exist for every graph. Theorem 2 is represented by its deterministic
induced-matching step; Theorems 3–4 are not proved end to end.

The counterexample and the replacement modular construction are checked
mathematical results. The replacement is explicitly distinguished from the
arXiv v4 construction. The proof covers backtracking walks, and equality
identifies the entire vertex sequence. The finite counting declarations
include path incidence, distinct paths when there are at least two layers,
and injective indexing of both oriented and undirected edges.

## Local reproduction detail

The standard Lean release needed the same executable-path compatibility
adjustment documented for the earlier VFT reproduction: process-specific
`/proc/.../exe` lookups were redirected to `/proc/self/exe`. This affects
executable location discovery, not Lean's kernel or proof terms. The helper
and downloaded runtime are temporary environment files and are not included
in the repository changes. GitHub CI uses its normal runner.
