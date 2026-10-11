# Original-density general graph increment: five-source component review

Frozen source manifest: checkpoint27-source-hashes.json (175 entries, 174 modules).
Freeze and exact five source hashes: general-increment-freeze.json. Production
files and *Draft.lean copies are identical. All 169 old library bodies are unchanged.

Please check the concrete parameter choices and actual same-host witnesses,
not only the numerical theorem statements. There are 276 new lines.

- GeneralIncrementParameters uses D=ceil(d/2), ell=k/4 to turn the literal
  degree floor d-(2+3k)d/k² into a natural degree lower bound. k>=16,d>=k³.
- RealBipartiteIncrement applies the established, internally constructed
  bipartite increment at those natural parameters, retaining actual witness
  subsets and genuine bounded minor models.
- GeneralInverseParameters discharges K=4k²,eps1=1/k²,eps2=1/k growth premises
  and converts the absolute edge witness into an explicit density ratio.
- SelectedScaleDensityIncrement invokes the actual densest-core trichotomy,
  discharges the real-degree bipartite branch, and lifts both possible outputs
  to the original host. It retains the selected original core U with E(U)=d|U|.
- GeneralGraphDensityIncrement removes the selected-scale discrepancy: if
  d>=(k/16)d0 the selected core itself is a singleton-branch minor; otherwise
  the original dense witness has size bounded using d<k*d0.

Final domain: finite simple G, 0<|V|, natural k>=32, real d0>=k³,
E(G)>=d0|V|. No initial family, minimum-degree, core, cleaning, coverage,
bipartite subgraph or minor witness is supplied. Output either:
  0<E(G[S]), |S|<=12k⁵d0, E(G[S])>=d0|S|/(800000k⁷),
or a positive genuine k-bounded minor Q of G with E(Q)>=(k/16)d0|Q|.
Thus the minor branch at least doubles density.

These constants are explicit verified choices, not an assertion of identity
with the source paper's sharper parameterization. Iteration, density hierarchy,
runtime and the final main spanner upper theorem remain open. Workflow and
all old proof/audit/checker gates are unchanged from the 60-minute parent.
