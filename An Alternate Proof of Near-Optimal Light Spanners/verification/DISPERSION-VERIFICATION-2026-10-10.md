# Actual bucket-path dispersion: Lemma 5.5 — 2026-10-10

This extends Claim 2 checkpoint `1339416bbe84021ea0658e4532e96a7a55a69db3`.
Its exact-commit repository CI is running separately at
https://github.com/gbodwin/paper-formalizations/actions/runs/38064176197.
The preceding Claim 3 checkpoint `0e29d002` already passed all repository gates.
Lean 4.34.0 and the mathlib pin are unchanged.

## Exact theorem

`UnitSpanningCycle.BucketMonotoneKPath.unique` proves Lemma 5.5 for the actual
walk predicates: two bucket-monotone safe k-walks with the same endpoints are
equal. It covers both ordinary and extra-safe modes. Assumptions are a finite
unit-spanning-cycle graph, positive ε, natural k ≥ 1, and weighted girth above
`(1+4ε)2k`. Distinct decomposition lengths, empty blocks, and boundary backtracking
are allowed. The statement supplies no hypothetical cycle, dispersion condition,
global simplicity, or unique decomposition.

## New graph arguments

`BridgeWords.lean` proves that marked edges which are bridges have identical
ordered oriented words in any two endpoint walks, provided each walk uses each
marked undirected edge at most once. No restriction is imposed on repetition
of unmarked edges. A first-crossing argument forces the occurrence and orientation
of each bridge. Contraposition extracts an actual cycle containing a marked edge.
Applying this to the union support graph ensures every cycle edge occurs in one
of the two input walks.

`BucketBudgets.lean` derives the actual prefix cycle-step bound
`2εk(2^j−1)`. The extracted simple cycle's distinct chord and base edges are counted
against the two ambient walks. At most 2k chords contribute at most 2k times the
cycle's actual maximum edge weight, while the base contribution is strictly less
than `8εk2^j`. A top-bucket edge ensures that maximum is at least `2^j`; the resulting
weight contradicts the supplied weighted-girth threshold.

`BucketDispersion.lean` inducts over the terminal bucket. Marking non-cycle edges
at or above its scale removes every earlier bucket and gives exactly the last
block's oriented chord word. Equal words invoke Claim 2 and identify the blocks;
unequal words give the support-local marked cycle and weight contradiction.
Previously proved Claim 3 supplies individual marked-edge distinctness. Empty
blocks pad the two decompositions to a common length internally.

## Checks

- Aggregate build passed: 35 source modules plus aggregate; 1410 jobs including cache.
- All-declarations permitted-axiom audit passed: 564 declarations, including private/generated.
- Selected axiom audit passed, including actual endpoint uniqueness and marked-cycle extraction.
- All four repository module indexes passed.
- All 35 source modules passed independent sequential kernel replay.
- Independent read-only semantic review passed against source Lemma 5.5;
  source hashes are recorded in `dispersion-semantic-review-20261010.json`.
- `git diff --check` passed before publication.

The gate log is `dispersion-2026-10-10-gate.txt`. Only `propext`, `Classical.choice`,
and `Quot.sound` are permitted. Exact-commit repository CI is monitored separately
from these focused local checks.

## Remaining

Hiker construction and its small-bucket rounding repair, truncation/extension/deletion,
actual independent edge sampling, and final lightness remain open. The complete
Lemma 3.5 graph reduction and Claims 2/3 remain proved. No full-paper completion
is claimed by this checkpoint.
