# Measured selection on original sparsest-cut inputs

`MeasuredGraphBudgetGrid` computes the original ordered budget pairs with
binary comparisons, products, sums, exact division, and canonical bit widths.
Its model includes price and mass limits and the binary arithmetic of the
doubling entries. The measured edge and vertex routines feed those raw pairs
into the same repriced covering computation and preserve each original
candidate's canonical numerator and denominator bits.

`MeasuredOriginalBudgetSelection` computes the original price, mass and
harmonic sum, then compares the exact sixth-power scores. The mass mode wins
a tie within a plan. The first plan wins a tie among different candidates.
The bound starts from the original typed prices and includes grid arithmetic,
repricing, covering, canonical conversion, searches, pivot comparisons and
score selection. It covers the modeled operations, with graph structure,
storage and path projection still separate from the charge.

`MeasuredBudgetedSparsestRound` supplies the same plan to the existing
threshold and amplified tape routines. The original edge and vertex results,
including failure and the unread suffix, are preserved for every tape. The
reported charge covers the optimizer on the branch that uses it. Detecting
free resources, computing the threshold, and running the tape routines require
additional cost bounds. The remaining bit-time obligations include modeling
physical storage access and the charge counters themselves.

## Rational family with the original factor bound

`RationalPositiveArcEdgeFamily` computes the rational instance factor on
the original graph, then builds the family at the scale given by the positive
arc count, with a minimum of one. A zero instance factor returns one empty cut.
Each cut is valid for the original demands. Its marginal is bounded by eight
times the original edge weight times the least global factor at the original
weight. The family length is also bounded by the rational horizon at that
global factor. The program uses the exhaustive instance search. This gives
an executable construction and leaves an efficient exact global calibration
open. Bounded fair-bit rejection retains the original cut on a successful
sample and returns the exact unread suffix. The dense positive-weight
vertex-count horizon remains open.
