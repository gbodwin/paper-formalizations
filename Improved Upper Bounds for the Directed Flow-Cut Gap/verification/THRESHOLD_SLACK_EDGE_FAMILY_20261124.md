# A uniform edge family at the original factor under a distance margin

Let `n > 0`, let `W` be the original edge weight, and let `α = efg n W`. For the cutoff `1/(2n)`, let `Δ` be the sum over vertices of the largest outgoing arc weight at or below the cutoff, using zero when the vertex has no such arc.

`ExactFlowCutGap.edge_uniform_of_threshold_slack` assumes that every original distance-one demand has original distance at least `1 + Δ`. A simple path loses at most `Δ` when the light arcs get weight zero. Thus all original threshold demands survive at threshold one. The trimmed total is at most `W`, so the exact factor at the original total applies by the proved weight-padding lemma.

Lean gives a positive uniform horizon at most `edgeHorizon n W = ⌈2n log(n(2W+n))⌉ + 1`. Every cut is valid for the original demands. Each arc's deletion frequency is at most `4αw(e)`. The proof includes the zero-factor case.

`ExactFlowCutGap.edge_uniform_of_half_threshold_slack` gives the simpler sufficient hypothesis that every original distance-one demand has distance at least `3/2`. Both statements allow any arc density and retain the original cost comparison. The unrestricted near-linear edge horizon at the original factor remains open for graphs without a suitable margin or another proved sufficient condition.
