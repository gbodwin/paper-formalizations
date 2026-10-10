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

## Checkpoint verification state

- Local Lean 4.34.0 and all nine dependency revisions match the lockfile.
- Counting and slope-injectivity core compiled without errors in an isolated
  import-only check. This check does not certify later declarations.
- Full geometric bridge, project-module build, axiom audit, native kernel
  replay, and independent skeptical review are pending at this draft.
- Fresh exact-commit CI is required; historical success is not attributed
  to this new checkpoint.
