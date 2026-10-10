# Sharp planar continuation — 10 October 2026

This checkpoint continues `codex/theorem4-planar-chains` at
`38d933d5d6b78659ba4dfa9f524225b74f9d154b`, whose GitHub Actions run
[37926611758](https://github.com/gbodwin/paper-formalizations/actions/runs/37926611758)
passed the build, axiom audit, and project kernel replay.

## New source and intended scope

- `PrimitiveDirections.lean`: elementary coprime-pair count; injective slopes;
  sorted convex chain; sharp planar exponent; arbitrary-side rounding.
- `PlanarProduct.lean`: existing Behrend outer ports and exact-size padding
  instantiated with the new planar direction family.

The primitive count is `R² ≤ 4 |primitive(R)|`. Every bad pair is covered
by a common divisor at least two. The reciprocal-square estimate is proved
by induction with a telescoping remainder. There is no imported density
axiom or unproved sharp-lattice assumption.

The resulting graph statement still has explicit numerical parameter and
port-capacity hypotheses. It does not settle the optimization for arbitrary
prescribed graph/terminal sizes or supply sharp lattice families in dimension
three and above. Full Theorem 4 remains incomplete.

## Completed source verification

The complete source at
[`034620ea79740a0efa4ba3bc4706c37dff773f67`](https://github.com/gbodwin/paper-formalizations/commit/034620ea79740a0efa4ba3bc4706c37dff773f67)
passed [GitHub Actions run 38052458003](https://github.com/gbodwin/paper-formalizations/actions/runs/38052458003),
completed successfully on 10 October 2026 at 12:51 UTC:

- Full build: 3,413 jobs, passed.
- Module indexes: all four included libraries, passed.
- Module-origin axiom audit: 1,040 distance-preserver declarations, plus
  195 VFT, 48 light-spanner, and 440 degree-fault-spanner declarations.
  Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
- Sequential native kernel replay: all 85 project modules passed,
  including all 51 distance-preserver modules. `PlanarProduct` replayed
  at 12:45:48 UTC and `PrimitiveDirections` at 12:46:14 UTC.
- Lean 4.34.0 and the pinned mathlib revision are unchanged.

The initial commit message and earlier draft record said verification was
pending. The linked completed run resolves that status. This record adds
no Lean changes to that checked source.

An independent read-only semantic review matched the source files to their
remote Git blobs and found no mathematical blocker in the common-divisor
cover, reciprocal-square bound, reduced-slope injectivity, exposed-chain
construction, no-wrap use of average rigidity, factor-4096 rounding, or
numeric-capacity graph/padding bridge. That reviewer did not run a separate
compiler or checker; it is a semantic review, not a second implementation
of Lean's kernel.

The local counting/slopes core also compiled successfully. The interrupted
full local rebuild is not reported as a pass; full-source verification above
comes from the exact-commit CI run. Kernel replay imports the pinned
mathlib environments, rather than independently rebuilding every dependency.

## Scope

The family may contain the zero vector. It satisfies ordinary convex-position
average rigidity, which the actual graph proof requires, rather than the
paper's stronger coefficient-sum-at-most-one convention. The final finite
graph bridge assumes only numerical construction-capacity and padding
inequalities. Satisfying and optimizing them for the full printed Theorem 4
range remains separate work, as do sharp higher-dimensional direction sets.
