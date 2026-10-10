# Actual hiker construction and weak counting — 10 October 2026

## Scope

This checkpoint completes Lemma 5.8 for an actual finite graph with a supplied
unit spanning cycle. The explicit numerical assumptions are epsilon > 0,
integer k > 0, and off-cycle weight at least 4n/epsilon. No girth premise is
needed for this weak counting theorem.

`UnitSpanningCycle.weak_counting` constructs an actual graph walk with at least
k chords and an actual increasing-bucket extra-safe decomposition. The safety
budget stays at the original k, even if the walk contains more chords.

## New proof components

- `HikerSquads`: actual graph walks with a permutation of endpoints; endpoint
  transpositions; additivity of total traversals and exact averaging.
- `HikerLayers`: distinct-chord layers, actual forward steps and non-backtracking;
  t forward steps and t+1 chord layers give exactly 2(t+1)|B_i| traversals.
- `HikerCompletion`: backward completion after cancelling only the terminal
  forward-cycle suffix, preserving the entire chord word and actual endpoint.
- `HikerDay`: chosen completed walks still form a permutation squad; their
  forward/backward budgets are at most t, and all chord counts survive.
- `HikerTour`: actual composition of all bucket days, exact count, numerical
  weight lower bound and an at-least-k-chord hiker.
- `DyadicEnumeration`: actual off-cycle graph edges, one chosen orientation,
  dyadic intervals, finite index bound, no duplicate edge per bucket, complete
  coverage, and exact summed weight equal to total graph weight minus n.
- `WeakCounting`: removes the finite-family premise and states the source-style
  graph-weight threshold.

The extra zero-shuttle chord layer repairs the displayed floor estimate for
subunit budgets. It changes neither the number of shuttle steps nor the
extra-safety budget. See `SOURCE-CORRECTIONS.md`.

## Verification

The local aggregate build, all four repository module indexes, permitted-axiom
audit of every LightSpanners declaration, selected theorem axiom checks, and
independent kernel replay of every paper module are recorded in
`hiker-2026-10-10-gate.txt`. The library contains 42 modules and 672 declarations.
Allowed axioms are only propext, Classical.choice and Quot.sound. No sorry,
project axiom or theorem-shaped substitute for the hiker process is introduced.

Independent read-only semantic review of all seven new modules passed;
`hiker-squads-semantic-review-20261010.json` pins the reviewed source hashes.
This review is separate from the compiler and kernel checks.

Repository-wide exact-commit CI is pending publication of this checkpoint.
The preceding dispersion checkpoint 4b574df7 passed its full exact-commit CI:
https://github.com/gbodwin/paper-formalizations/actions/runs/38064725204

## Remaining paper gaps

Lemma 5.10's actual truncation/extension/deletion count, Lemma 5.13's independent
edge sampling and survival calculation, and Theorem 5.1's final lightness bound
remain unproved. This is a substantial intermediate checkpoint, not an
end-to-end verification of the entire paper.
