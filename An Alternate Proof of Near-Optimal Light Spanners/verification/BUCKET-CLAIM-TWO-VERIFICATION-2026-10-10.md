# Actual chord-word endpoint uniqueness: Claim 2 — 2026-10-10

This extends commit `0e29d002723cbc861f2aeaf0cea319caac8b58c9`, whose complete
repository compilation, all module indexes, complete axiom audit, and independent
kernel replay passed in https://github.com/gbodwin/paper-formalizations/actions/runs/38062078307.
Lean 4.34.0 and the mathlib pin are unchanged.

## Exact scope

`UnitSpanningCycle.BucketSafe.unique_of_chordDarts` proves Claim 2 in its
common-terminal-vertex form. Two actual bucket-safe walks ending at the same
vertex and having the same ordered oriented chord word are heterogeneously equal.
The initial vertices and bucket indices may differ. Assumptions are a finite
unit-spanning-cycle graph, positive ε, integer k ≥ 1, and actual weighted girth
above `(1+4ε)2k`. No simplicity assumption, chord-count bound, supplied arc
uniqueness, or hypothetical dispersion lemma occurs in the statement.

The chord word consists of actual graph darts, matching the ordered pairs
`((u₁,v₁),…,(uⱼ,vⱼ))` in the paper's proof. It is not an unordered edge set.

## Actual construction and proof

- `CycleOrder.lean` identifies positions of the actual Hamiltonian cycle with
  the vertex type. Conjugating modular successor yields the actual cycle-step
  permutation, with precisely the forward cycle darts. Actual forward and
  backward walks of every prescribed length are constructed.
- `CycleSegments.lean` proves that a chord-free balanced non-backtracking bucket
  block is nil: a nonempty forward/backward turnaround would repeat an edge.
  It also proves uniqueness of two simple base arcs of combined length below n
  by extracting an actual cycle if they differ.
- `CycleBalance.lean` defines the actual oriented chord filter. Displacements in
  the cycle's cyclic position group telescope across an actual graph walk.
  Equal forward and backward counts cancel, so its terminal vertex and oriented
  chord word already determine its initial vertex. This part needs no girth.
- `ChordWords.lean` splits an actual walk at its first chord. Induction on chord
  count proves that two non-backtracking walks with the same endpoints and
  oriented chord word coincide if their combined number of base steps is below n.
  Each intervening base arc is proved simple; the whole walk need not be simple.
- `BucketUniqueness.lean` derives fewer than n/2 base steps for every safe block.
  A single chord bounds its bucket scale using the existing chord-weight bound;
  chord-free blocks are nil. This gives the strict combined bound needed above
  and completes Claim 2.

## Checks

- Aggregate build passed: 32 source modules plus aggregate; 1407 jobs including cache.
- All-declarations permitted-axiom audit passed: 521 declarations, including generated/private.
- Selected axiom audit passed, including the final endpoint-uniqueness theorem.
- All four repository module indexes passed.
- Independent sequential kernel replay passed for all 32 source modules.
- Independent read-only semantic review passed against source Claim 2 v6;
  exact hashes and verdict are in `bucket-claim-two-semantic-review-20261010.json`.
- `git diff --check` passed before publication.

The complete local gate is `bucket-claim-two-2026-10-10-gate.txt`.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Repository-wide
CI for the new exact commit is monitored separately after publication.

## Remaining

Last-differing-bucket marked-cycle extraction, dispersion Lemma 5.5, the hiker
construction with small-bucket rounding, truncation/deletion, actual independent
edge sampling, and final lightness remain open. No full-paper completion is claimed.
