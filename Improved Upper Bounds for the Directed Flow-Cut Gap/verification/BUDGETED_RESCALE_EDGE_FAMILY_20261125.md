# Budgeted rescaling for the rational edge family

For $n>0$, the sampler sets lengths at most $1/(2n)$ to zero while keeping those arcs in the graph. It reserves length one for each retained arc whose length is already at least one. It then multiplies the subunit lengths by the largest affordable common multiplier up to two. The modified total is at most the original $W$, and each modified arc length is at most twice its original length.

The sampler checks that every original pair at distance at least one still has distance at least one with the modified lengths. The check also accepts every input accepted by the unscaled trimming guard. If the check fails, the program uses the arc-by-arc pruning family.

For $n>0$, every returned cut separates every original threshold demand. The cut family and literal fair-tape sampler have arc marginals at most $16\,\mathrm{efg}(n,W)w(e)$. The vertex-count horizon applies if the rescaling guard succeeds or if the pruning fallback retains at most $n$ positive arcs. The exact factor search remains exhaustive on its positive support.

The native fixture exercises four cases. The original path of total length one stays a demand after its retained length increases to one. The literal sample cuts that arc and keeps the exact unread suffix. On five vertices, a tight path coexists with six unit-length arcs. All eight positive arcs survive arc-by-arc pruning, while the rescaling guard recovers the tight path within the original total of seven. A shared light arc on a separate input leaves both rescaled legs below threshold, so the guard uses the pruning fallback. The empty graph returns the singleton empty cut.
