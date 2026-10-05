# Verification record

Checked locally on 5 October 2026.

| Item | Version or result |
| --- | --- |
| Lean | 4.34.0, release commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` |
| mathlib | release v4.34.0, commit `5ed2965256430c3649e86755f9576b54eca72435` |
| Dependency lock | `lake-manifest.json`, nine resolved packages |
| `lake build` | Passed, both project modules compiled |
| `lake exe mk_all --check --lib BodwinPapers` | Passed, no missing imports |
| `lake env lean scripts/AxiomAudit.lean` | Passed, all five exported declarations inspected |
| `lake env leanchecker BodwinPapers` | Passed, compiled environment rechecked |
| Source scan | No proof-hole commands or new axiom declarations in project source |
| GitHub Actions | Workflow prepared; no remote run has occurred |

The axiom output for both proved theorems is exactly
`[propext, Classical.choice, Quot.sound]`. The blocking-set definition has the
same dependencies; the graph and inclusion constructions depend only on
`Quot.sound`. All are standard Lean axioms. The CI audit permits only those
three axioms, including when dependencies are reached through imports.

The local environment needed a temporary filesystem-path compatibility shim:
Lean's executable-path discovery used a process ID inconsistent with the
container's mounted `/proc`. The shim redirects only that process's
`/proc/<pid>/exe` lookup to `/proc/self/exe`. It does not modify Lean's proof
checker, sources, or proof terms, and is excluded from this repository.
Standard installations do not need it.

Compilation and axiom inspection establish the encoded result. The exact
mapping to the paper is documented in `statement-map.md`; the quantitative
parts of Lemma 4 and the paper's main theorem remain unformalized.
