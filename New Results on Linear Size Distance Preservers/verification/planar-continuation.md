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

The initial graph statement has explicit numerical parameter and port-capacity
hypotheses. The subsequent extension below removes all of them in d=2.
Sharp lattice families and general-dimensional optimization in dimensions
three and above remain; full Theorem 4 remains incomplete.

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
pending. The linked completed run resolves that status. The documentation-only
successor `2055c1c67c5f15f4a3e89c77319098d582bd8a5a` changed no Lean source
and also passed [run 38053709049](https://github.com/gbodwin/paper-formalizations/actions/runs/38053709049).

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
inequalities. The subsequent d=2 extension below satisfies and optimizes them.
Higher-dimensional optimization and sharp direction sets remain separate work.

## Uniform planar capacity selection — verified

The next continuation adds `PlanarParameters`, `UnweightedPath`, and
`TheoremFourPlanar.capacity_lower_bound`. It selects all inner parameters
for arbitrary prescribed N,T from scalar inputs
`0 < M`, `3R ≤ M`, `Q ≤ M`, `Q ≤ rothNumberNat R`, `2M ≤ T ≤ N`.
The finite conclusion is
`M² Q³ N⁴ ≤ 16777216⁶ E⁶` for every subset preserver.

Sixth- and fourth-root integer scales handle the middle regime; exact-size
unweighted paths and cliques handle the two extremes. The separate arithmetic
lemmas compiled locally. The complete case assembly and graph wrapper at
`565feff53142b90e50ee2d7229b67c62400e2d27` passed
[CI run 38054778459](https://github.com/gbodwin/paper-formalizations/actions/runs/38054778459)
at 13:26 UTC, including all 88 project-module kernel replays and an audit of
1,079 distance-preserver declarations. An independent read-only review found
no gap in the exhaustive regimes, rounding losses, or native graph semantics.
Its integer boundary/random tests were diagnostic, not a replacement for Lean.

## Unconditional d=2 Behrend substitution — verified

`PlanarBehrend.lean` now removes the scalar capacity inputs. For T≥6 it
sets R=floor(T/6), M=3R, and Q=rothNumberNat R; Behrend gives
`T exp(-4 sqrt(log T)) ≤ 12Q`, and the rounding gives `T ≤ 4M`.
The cases 2≤T<6 use an unweighted path. The exact-size result is

```
N^(2/3) T^(5/6) exp(-2 sqrt(log N)) ≤ 100663296 E.
```

Here every N,T with 2≤T≤N is covered; G has exactly N vertices, S exactly
T terminals, and E is the edge count of any subgraph preserving every
native unweighted S×S distance. The separate Behrend, small-T, and real
sixth-root conversion lemmas compiled locally. The complete source at
`837c383a678020a1aaf0dfef1e99debb6c0cebfd` passed
[CI run 38055342165](https://github.com/gbodwin/paper-formalizations/actions/runs/38055342165),
completed at 13:34 UTC: 3,417 build jobs, complete module-index checking,
1,093 distance-preserver declarations audited, and all 89 project modules
replayed through the native kernel (55 for this paper). `PlanarBehrend` replayed
at 13:29 UTC. Only the same three standard axioms were allowed.

An independent reviewer checked the Behrend substitution, small-T branch,
constant 100663296, sixth-root conversion, and weakening from log T to log N.
No mathematical gap was found. This was a source review, not a separate Lean
run. The previous draft commit messages and pending notes are resolved by the
linked successful runs.

This completes the displayed d=2 rate only. “Planar” refers to the direction
construction, not a planar-graph restriction. Higher-dimensional Theorem 4
and the previously documented printed-corollary issue remain separate.
See the [higher-dimensional roadmap](higher-dimensional-plan.md).
