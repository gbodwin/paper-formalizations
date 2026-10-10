# Eight-module contraction/neighborhood component review

Frozen checkpoint:50 own modules,498 defining-module declarations. The previous42 proof files remain byte-identical to exact-CI-certified c062eeeecfed00beabb4cd5754c601edc5045d34. Source manifest verification/checkpoint8-source-hashes.json has51 entries including the root; SHA256 b421e9936af479b61b7e34c0c58832c00bf35b4d4c2182800b2bdc3c0d502a7a. The owner will start the review only after both final kernel-replay groups pass. Check their logs independently; do not infer a gate result from this brief.

Local gate logs: neighborhood-build-gates.log, neighborhood-replay1.log and neighborhood-replay2.log. The full root/index/axiom audit passed19:57:39; first four replays passed19:58:39. Exact-commit CI for these eight additions remains a separate forthcoming checkpoint gate. No whole-paper final audit is claimed.

Targets: PostleBipartiteTrim, PostleSubgraphUnmated, MateFreeSets, EdgeContraction, EdgeContractionCount, MinimalDenseMinor, DenseMinorNeighborhood, RobustCommonNeighbors.

Semantic checks:
- Bipartite trimming constructs an actual symmetric subgraph with exactly the requested integer left degrees, with no false assumption that global unmatedness is hereditary.
- The subgraph dichotomy reapplies the proved graph theorem, and pulls an actual dense induced witness back to the host by edge inclusion.
- Mate-freeness is literal common-neighbor control; graph/vertex deletion preserve it. Opposite bipartite sides have zero common neighbors.
- Edge contraction deletes one endpoint, removes loops and merges parallel edges in a genuine simple graph. Branch sets witness an actual width-two minor. Exact edge loss is one plus the number of common neighbors, not the degree of the removed endpoint.
- Minor-minimal selection is over actual nonempty finite minor models. The empty graph must not satisfy the density premise vacuously. Integer density is explicit. Edge trimming proves equality, rather than assuming it.
- The neighborhood extraction uses contraction and minimality to force at least d common neighbors on each edge; uses vertex deletion to exclude low-degree vertices; and extracts an actual induced neighborhood with at most2d vertices and minimum degree at least d. All needed host/minor compositions and cardinality transfers must be present.
- Robustness is actual preconnectedness after every smaller deletion set, proved using surviving common neighbors and explicit two-edge walks.

Primary source for the last route: Alon, Krivelevich and Sudakov, Complete minors and average degree — a short proof, https://www.math.tau.ac.il/~krivelev/KT-minors.pdf, proof of Theorem1 on page2. Local original PDF and text retained. This batch formalizes only the deterministic local-neighborhood step and an elementary robustness lemma. It does not prove their probabilistic lemma or their sharp clique-minor threshold. A possible weaker O(h log h) deterministic continuation remains only a plan.

Main paper upper bounds, full Postle density increment, actual cluster hierarchy and charging all remain open. Prior full fixed-k conditional connected lower bounds remain certified separately. This is component review only, not the final whole-paper skeptical audit.
