# Global MST rounding repair — 2026-10-10

This extends `c836da0b8996ef1a7a6f20a76204bc8acbcad88b`, the locally
verified tree/MST/lightness subdivision checkpoint. Toolchain and mathlib
pins are unchanged.

## New proved statements

`RoundingTree.lean` proves that a spanning tree whose edges weigh at most one
becomes a unit-weight MST when every graph edge is rounded up to one. Its
exact weight is `card(V)−1`. Using a global cardinality/weight bound, it proves
that lightness decreases by at most a factor of two. The normalized version
takes `totalWeight T w = n−1` and `card(V) ≤ 2n−1` as hypotheses.

This avoids a false pointwise claim about the lower weight of old tree edges
in the paper's Section 3.2. See `SOURCE-CORRECTIONS.md` for a concrete example
and the corrected argument. The theorem proves the rounding transfer; it
does not yet construct the iterated subdivision supplying its cardinality
hypothesis.

## Checks

- Targeted package build: passed, 18 source modules plus aggregate, 1351 jobs.
- Complete permitted-axiom audit: passed, 252 declarations including
  private/generated declarations. Only `propext`, `Classical.choice`, and
  `Quot.sound` are permitted.
- Selected axiom checks include all four rounding theorems: passed.
- Independent sequential `leanchecker -v` replay: passed for all 18 source modules.
- Source import-index equality: 18 sources, 18 imports.
- `git diff --check`: passed before checkpoint publication.

Logs prefixed `rounding-2026-10-10-` record the local gate. Exact-commit
repository-wide CI is a separate check after publication. The full paper,
including repeated subdivision, Euler-tour vertex copying, bucket-path
combinatorics, sampling, and final lightness assembly, remains incomplete.
