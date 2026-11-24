# A rational sampler with an exact demand-preservation test

`RationalTrimmedEdgeFamily.keepsDemands` checks the complete original and trimmed threshold-demand lists. Trimming sets weights at or below `1/(2n)` to zero. The check passes exactly when every original threshold demand still has distance at least one. The distance-margin hypothesis from `THRESHOLD_SLACK_EDGE_FAMILY_20261124.md` implies a passing check.

On a passing check, `RationalTrimmedEdgeFamily.family` uses the trimmed weights to build a uniform family on the same graph. It computes the least integer factor for the trimmed instance by exhaustive search. The trimmed total is at most the original `W`. Lean bounds the computed instance factor by `efg n W` and the family length by the rational vertex-count horizon at `efg n W` and the original total. On a failed check, the sampler uses the positive-weight arc-count family on the unchanged weights.

For either branch and `n > 0`, every returned cut satisfies the original threshold demands. The deletion marginal is at most `8 * efg n W * w(e)` for each original arc. `RationalTrimmedEdgeFamilyTape.draw_used` tracks the literal unread suffix, `draw_valid` proves original cut validity, and `draw_law` states the exact bounded-rejection failure probability and the original marginal bound.

The native dense example gives positive weights to all four arcs. It returns 25 valid cuts and uses five bits to draw the required original arc. A separate path of original length exactly one demonstrates that the guard rejects trimming when it loses a demand. The general dense vertex-count horizon and an efficient exact factor search remain open.
