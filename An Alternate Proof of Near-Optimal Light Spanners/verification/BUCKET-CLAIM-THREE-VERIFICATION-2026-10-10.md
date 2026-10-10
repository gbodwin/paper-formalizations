# Actual bucket walks and Claim 3 — 2026-10-10

This extends commit `68bb4189ae4cd86cbc82d8cd35c84dc55d3c8f5a`, whose full
repository compilation, all module indexes, complete axiom audit, and kernel
replay passed in https://github.com/gbodwin/paper-formalizations/actions/runs/38060761128.
Lean 4.34.0 and the mathlib pin are unchanged.

## Exact scope

`BucketPaths.lean` implements Definitions 5.2 and 5.4 using actual graph walks.
`cycleDarts` filters actual oriented darts of the chosen Hamiltonian cycle;
`BucketWalk` requires equal forward/backward counts, all forward cycle steps
before all backward cycle steps, non-backtracking within the block, and chord
weights in the half-open interval `[2^i,2^(i+1))`. Extra-safety divides the real
budget by two, including index zero. Empty blocks are allowed. The inductive
bucket-monotone predicate concatenates the actual walks and imposes no
non-backtracking condition across block boundaries.

`BucketCycles.lean` proves Claim 3 for these definitions:
`UnitSpanningCycle.BucketMonotoneKPath.chordEdges_nodup` says the k non-cycle
edges are distinct. Assumptions are `ε>0`, integer `k≥1`, a unit spanning-cycle
certificate (including graph weights at least one), and weighted girth above
`(1+4ε)2k`. No dispersion, global simplicity, favorable path count, or hiker
protocol is a premise.

## Proof

A stronger within-bucket theorem proves that a nonempty-in-chords safe block
with at most k chords is a simple path. The chord-weight bound gives fewer
than n cycle steps, excluding any supported base-only cycle. Every remaining
supported cycle contains a bucket chord of weight at least `2^i` and weighs
at most the ambient walk. The actual walk-weight budget is at most
`(2+2ε)k·2^i`, contradicting the weighted-girth threshold `(2+8ε)k`.

Thus the support graph is acyclic. Mathlib's equivalence between non-backtracking
and being a path in an acyclic graph gives simplicity of the block. Empty-chord
blocks are handled separately. Disjoint half-open dyadic intervals prevent
repeated chords in different blocks. The concatenated walk itself is not
claimed to be globally simple.

## Checks

- Aggregate build: passed, 27 source modules plus aggregate, 1402 jobs including cache.
- All-declarations permitted-axiom audit: passed, 435 declarations including generated/private.
- Selected axiom audit: passed, including the final Claim 3 statement.
- All four repository module indexes: passed.
- Independent sequential kernel replay: passed for all 27 source modules.
- Independent read-only semantic review: passed, compared with arXiv v6;
  source hashes and exact scope are in `bucket-claim-three-semantic-review-20261010.json`.
- `git diff --check`: passed before publication.

The local gate is recorded in `bucket-claim-three-2026-10-10-gate.txt`.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Exact-commit
repository-wide CI is monitored separately after publication; focused local
checks are not described as a repository-wide compilation.

## Still open

Claim 2's endpoint/chord-word uniqueness, last-differing-bucket cycle extraction,
dispersion, hiker construction with small-bucket rounding handled, truncation
and deletion, independent edge sampling, and the final lightness theorem.
The complete preceding Lemma 3.5 graph reduction remains certified separately.
