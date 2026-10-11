# Actual polylogarithmic density witness and sparsity upper bound

Frozen185-module manifest: checkpoint28-source-hashes.json. All174 predecessor
mathematical bodies are byte-unchanged. Eleven new sources,677 lines; their
exact hashes are in polylog-sparsity-freeze.json. Production and draft bytes
are identical. All draft checks pass; production/root/audit/replay gates follow.
Workflow, existing audit/checker steps and60-minute cap are unchanged.

Please review the entire actual construction chain, especially:
1. SharpIncrementParameters and SharpRealBipartiteIncrement use the ceiling
   of the literal real left-degree floor. Because host degrees are integral,
   ceil(floor) <= degree is valid; no degree rounding is assumed. The actual
   width floor(k/4)+1 is retained, with gain m*(1-16/k).
2. SharpSelectedScaleIncrement and SharpGeneralGraphIncrement retain that
   width (k/4<=m<=k). A too-dense selected core itself supplies an actual
   singleton-branch minor bounded by k. All outputs are on the original host.
3. BalancedDensityEscalation iterates actual minors, multiplying their actual
   branch-width bounds W. Density is alpha^j*W*d, alpha=1-16/k, and grows by
   at least2 per stage. The sequence is constructed internally by induction.
4. BalancedCliqueWitness applies actual clique-minor exclusion to every
   stage, forcing termination at a purely numerical horizon. Bernoulli and
   32t<=k give alpha^j>=1/2. Pullback uses actual branch unions and retained
   host edges, obtaining |T|d<=1600000k^7*C² and <=1600000k^7*E(T),
   where C=6*cliqueDensityScale(h). No pullback/count premise is supplied.
5. LogarithmicDensityWitness chooses t=log₂(C)+1 and k=32(t+1) internally.
6. PolylogarithmicDensityWitness proves k<=131104(log₂h+2) and translates
   C² to h² with a literal degree-nine logarithmic coefficient.
7. FullDensityWitness handles all positive d below the k³ threshold by
   selecting a literal actual host edge. It proves the full loss is bounded
   by an explicit constant times(log₂h+2)^9, independent of stretch.
8. GirthMinorFreeUpper maps actual cycles into the host, applies the already
   verified Moore theorem on the constructed induced witness, and closes
   the previous conditional density algebra without a supplied witness.
9. GreedyMinorFreeSparsity applies this to the actual ordered greedy output,
   proving its2r-1 stretch and edge bound2L(h)h^(2/(r+1))*|V|.

Domains: finite simple undirected graph; h>0 and integer r>=1; positive real
weight on every Sym2 value for the existing greedy interface. Empty hosts and
edgeless graphs are handled. No graph-density, family, cleaning, sequence,
hierarchy, or Moore witness is an extra premise in the final sparsity theorem.
Classical finite selection is used; a construction runtime is not proved.

This closes the proof chain for the sparsity half of source Theorem6 and
Theorem13, with explicit but deliberately large constants. Weighted lightness,
the geometric hierarchy, runtime and the final whole-paper skeptical audit
remain open. Full exact-commit CI is still separate from these local gates.
