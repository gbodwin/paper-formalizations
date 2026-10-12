# Frozen four-arm path-phase packet

Parent bd2fc308 (217 modules), proposed successor227. Ten sources,717 lines.
All production and draft hashes are in four-arm-phase-freeze.json and
checkpoint32-source-hashes.json (228 source/root entries).

This constructs a genuine disjoint four-arm phase rather than assuming a
packing, decomposition or credit inequality. It begins with the actual
residual forest degree-two spanning-path theorem. For a given simple path and
an interior vertex whose two actual affixes have mass at least L, recursion
selects two threshold prefixes with mass in [L,L+D+1), intersecting only at the
center. Four arms at two centers are eligible only when their two carrier
sets are disjoint and an actual original B edge links the two old branches.
The finite maximum ranges over witnessed finite carriers inside the supplied
residual vertex set R. Empty candidates are allowed; maximality excludes
every remaining eligible disjoint original far-endpoint path pair.

Original unit-edge connectors and the supplied old intrinsic path certificates
lift each arm to its center at cost at most L+D. The original heavy edge is
traversed at most once in a cross-center path. The constructed union has
intrinsic diameter certificate 2(L+D)+M. Four arms give total effective node
mass at least4L-2(D+1). Seven eighths of old credits plus actual internal unit
connector credits pay the diameter; one eighth pays qM per vertex. The exact
proved numerical conditions are8qM<=cb and15D+4M+15+2b<=6L. The output retains
cb/2 in addition to the diameter reserve.

Check especially:
- Actual endpoint/subpath domains and disjointness; no duplicated center mass.
- Conversion of connected-set vertex counts to distinct internal edge credit.
- Correct direction of the internal-edge subset and original connector map.
- Every incident original B edge is covered using the explicit full old-family
  covering hypothesis. The weighted-girth assumptions prove no loops/parallel
  heavy fibers; these properties are not assumed as an oracle.
- The final forest H is the supplied actual coarse subgraph of C.graph T,
  suitable for the previous phase's output. It need not be reselected, and
  no acyclicity hypothesis is hidden in the four-arm credit argument.
- Original credits and quantitative bounds are explicit input invariants.

The earlier branching/initialization outputs are independently certified
components; global hierarchy iteration is not newly claimed here. The residual
condition is exactly no eligible four-arm carrier, with a concrete original-
path consequence, not a claim that all remaining heavy edges are paid.
The same-path short-cycle case, endpoint absorption/deferred edges, global
multilevel lightness and runtime remain open. No full-paper claim.

Local strict production builds, aggregate/index/axiom audit and ten independent
kernel replays are separate gates. An independent exact-source review and its
remote binding remain required before a published component claim. No helper
or additional worker is authorized during the DP completion audit.
