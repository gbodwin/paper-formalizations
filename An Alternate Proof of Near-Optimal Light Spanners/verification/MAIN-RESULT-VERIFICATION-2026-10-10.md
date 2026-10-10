# Main-result verification checkpoint — 2026-10-10

## Scope

The connected-MST-domain main result is now assembled from the actual sorted
greedy output, MST construction, unit-cycle reduction, bucket dispersion,
hiker squads, useful padded families, deletion induction and finite independent
sampling. See `STATEMENT-COVERAGE.md` and `statement-coverage.json` for all 52
source blocks, omitted unused exposition and repaired source statements.

The terminal declarations are `near_optimal_greedy_spanner`,
`near_optimal_greedy_lightness` and `exists_near_optimal_spanner`.
Their fixed-epsilon lightness coefficient is 8+2048/epsilon, independent of n,k.
The finite-uniform unit-cycle weight statement retains +n; epsilon<=1 is needed
only to remove that baseline with a uniform 1/epsilon coefficient.

## Exact local checks

- Lean 4.34.0; mathlib 5ed2965256430c3649e86755f9576b54eca72435.
- All 59 project modules and the aggregate compile with autoImplicit=false.
- All project module indexes pass.
- All 795 declarations, including private/generated declarations, pass the
  audit allowing only propext, Classical.choice and Quot.sound.
- Selected main theorem and counting axiom reports contain only those axioms.
- All 59 project modules pass separate official kernel replay. The work was
  split into bounded shared-compiler windows; interrupted modules were replayed
  to successful completion, and the final unique pass set equals the module index.
- Harmless linter warnings remain; there are no proof errors or admitted proofs.

`main-result-source-hashes.json` pins every project Lean source and build inputs.
`main-result-2026-10-10-build-audit.txt` records the successful aggregate gate.
The separate kernel log records each module's completed replay.

## Semantic review, CI and final audit

The new mathematical constructions have received bounded independent read-only
semantic reviews, retained in the JSON reports. Older reports pin pre-elaboration
versions; the consolidated final report pins the exact final changed sources.
These reviews are not the fresh skeptical end-to-end audit requested by the user.

At this immutable checkpoint’s creation, exact-commit repository CI and the
fresh independent skeptical end-to-end audit are pending. The CI run is created
after the commit exists; consult its GitHub checks and the companion for later
terminal results. These later results do not change the frozen proof hashes.
Public personal research-site completion link: not yet authorized by a passing
final audit. The existing private PaperLab may show verified progress.

The prior certified checkpoint is 03fcbd7a4f9241935a520699679081a5247570c2,
42 modules and 672 declarations, with successful full repository CI:
https://github.com/gbodwin/paper-formalizations/actions/runs/38066461206.
