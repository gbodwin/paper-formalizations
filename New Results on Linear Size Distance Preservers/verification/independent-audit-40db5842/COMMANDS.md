# Commands and verification boundary

All source paths refer to the immutable archive under `../audit-updated-40db5842/repo`. The read-only shared package cache and verified working-source artifacts supply imports. Fresh selected module artifacts live only under this audit's `compiled/` directory. `env.sh` records the exact toolchain and search path. It is an overlay containing only the 112 frozen paper module names, not the two later working modules.

The nonblocking lock used for every compiler invocation is `/workspace/shared/formalization-compiler.lock`. Each source/replay batch records UTC acquisition, individual commands, result codes and release. Source elaborations use `lean -j1 -DautoImplicit=false`; source modules' pinned lakefile also specifies autoImplicit=false. Official leanchecker replays are one module per invocation (their extra frontend-style flags are not used to change source elaboration).

- `python prepare.py`: initial audit-file preparation and source/artifact hashing. The complete overlay symlink population step was added manually after initial preparation, before compilation; do not assume this preparation helper alone recreates the overlay.
- `source env.sh; lean -j1 -DautoImplicit=false AuditFrozen.lean`: exactly 112 imports, all 1937 defining-module declarations, cached axiom inventory plus an independent traversal of checked types and bodies. Run under the nonblocking lock with a 55-second timeout. `raw/closure-audit-4.log` is the first fully successful run. Its `#check` outputs independently elaborate the 12 final theorem types.
- `./run-fresh-batch.sh TheoremOne TheoremTwo TheoremThreeExact UniformDimension`: successful first source batch.
- `./run-fresh-batch.sh InducedMatchingRemoval WeightedConstruction QuadraticRepair QuarterRootTheorem TheoremSix WeightedPerturbation WeightedSuperquadratic`: successful second source batch. Both shell drivers acquire/release the lock internally and share a 55-second budget.
- `./run-replay-batch.sh TheoremOne TheoremTwo TheoremThreeExact UniformDimension TheoremSix WeightedPerturbation`: official module kernel replays, each starting from that module's imported environment. These are not fresh replays of every dependency.
- Supplementary `lean -j1 -DautoImplicit=false --run ReplayClosure.lean MODULE ROOT`: traverses the specified root's checked type/body dependencies, rejects unsafe/partial/unapproved-axiom dependencies, then feeds the closure into the official `Lean.Kernel.Environment.replay` with an EMPTY kernel environment. The script also closes mutual inductive blocks. Successful root/count diagnostics are recorded separately.
- Supplementary `lean -j1 -DautoImplicit=false Nonvacuity.lean`: independent audit-only nonvacuity lemmas. They are outside the frozen source and cannot extend that commit's formal theorem list.
- `python finalize.py`: assembles `verdict.json` from real logs and rechecks all frozen manifest entries. No result is inferred solely from a component review.

## Initial harness diagnostics

Raw failures are retained, rather than hidden:

1. `closure-audit.log`: an initially incomplete overlay shadowed the complete imported module namespace; Lean reported missing BalancedCoefficient.olean. No target source was changed. The overlay was populated with read-only symlinks to all frozen artifacts.
2. `closure-audit-2.log`: a quoted-name/field-notation parsing error in the new audit script, corrected with an explicit parenthesized Name.
3. `closure-audit-3.log`: the initial extra-strict union guard rejected two automatically generated partial recursors. The full inventory includes these compiler auxiliaries, but each of the 12 theorem-specific checked closures excludes them. The final audit records them explicitly and still rejects unsafe constants and every disallowed axiom. They are not sorry/admit/custom axioms. Official Lean replay itself omits partial/unsafe declarations, so the theorem-specific dependency check is important.

No frozen mathematical source failed its fresh selected elaboration. No source, archive, original PDF/TeX, working proof file or shared mathlib cache was changed by the auditor. The only owner's proposed fix inspected was the separately hash-bound README patch, applied to an audit-owned copy for comparison.
