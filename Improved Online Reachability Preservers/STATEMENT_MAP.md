# Statement map

Greg Bodwin and Tuong Le, *Improved Online Reachability Preservers*.
The reference is [arXiv:2410.20471v1](https://arxiv.org/abs/2410.20471v1), dated
October 27, 2024. The [versioned PDF](https://arxiv.org/pdf/2410.20471v1) and
[unversioned PDF](https://arxiv.org/pdf/2410.20471) have SHA-256
`9a32d8314cf4f0ab9e00e62577fde0928a58839696aae836c2d40fb1800a1abb`.
The [SODA 2025 record](https://doi.org/10.1137/1.9781611978322.149), pp. 4375–4404,
confirms the rounded online pairwise, restricted, and Steiner rates in its abstract.
The proceedings PDF endpoint returned HTTP 403. The comparison to SODA covers
its abstract and bibliographic record. All section and result numbers below refer to arXiv v1.

## Scope and conventions

- The input is a fixed finite directed graph, with spanning edge subsets as preservers.
  Reachability is reflexive. A zero-length walk answers self-demands. The path-growth search ignores
  unreachable demands. The condensed algorithm can add fixed internal SCC
  connectors at the first request. An edge subset cannot create original reachability.
- An online guarantee is for every prefix. State and choices can use the input and
  demands already seen, with no access to the future trace or its length. The source
  or sink promise is used in the analysis and need not be given to the adaptive algorithm.
  The paper takes demands to be a set. The Lean trace accepts repetitions and
  counts each arrival. For a list of distinct requests, its length is the paper's
  demand cardinality. The index-sensitive rule uses zero-based arrival indices.
- The auxiliary path system is an indexed family of ordered, vertex-simple sequences.
  Its size counts vertices with multiplicity across paths. Its degree counts paths
  containing a vertex. A bridge has distinct path indices, with a river and a chain
  of arcs. A 2-bridge can occur when two distinct paths contain the same ordered pair.
  In an acyclic system all path orders extend a common strict vertex order.
  The [literal exact-count obstruction](OnlineReachabilityPreservers/DistinctPathBudgets.lean)
  shows that a set of distinct nonempty simple paths with half-bridge cutoff
  at least three cannot have exactly \(n^2\) paths when \(n\ge3\).
  Keeping the nontrivial rows gives a distinct set within the budget and
  loses at most one incidence per original row. If repetition within a row
  is allowed, the displayed sequence definition gives an unbounded maximum.
- A growth algorithm uses computable reachability queries and deterministic tie-breaking.
  Correctness, the size bound, and polynomial work are distinct claims. For uniform
  asymptotic bounds the constants are fixed before the input, and for the subpolynomial
  factors every fixed exponent slack has a uniform constant.
- The Steiner application uses a fixed unweighted graph and reachable demands.
  Its optimum is the offline minimum edge count for the original demands. Counting
  nontrivial demands excludes self-pairs and repetitions. Randomized claims need the
  success and cost guarantees and the adversary model of the invoked algorithms.

## Main and background results

| Source | Scope and dependencies | Lean coverage |
| --- | --- | --- |
| Definition 1 | For each demand, equivalence of input and preserver reachability. | [Preserves](OnlineReachabilityPreservers/Online.lean) and prefix correctness. |
| Theorem 1 | Adaptive deterministic polynomial-time pairwise online bound. The sharp terms are \(n^{(2+\alpha)/(3+\alpha)+o(1)}p^{2/(3+\alpha)}\) and \(n^{2-2\alpha+o(1)}p^\alpha\), with \(+n\) and \(\alpha\in(0.700,0.701)\) the middle root of the printed cubic. The rounded upper bound is \(O(n^{.72}p^{.56}+n^{.6}p^{.7}+n)\). Uses Theorem 9, Lemma 10, and Appendix A through Theorem 38. | [Both edge bounds](OnlineReachabilityPreservers/OnlineSharp.lean) hold at every prefix on general digraphs. A single function of the vertex count with limit zero supplies the unrounded slack uniformly over demand counts. The list evaluator has a polynomial source-level tally across all prefixes. |
| Theorem 2 | One of the two endpoint promises \(P\subseteq S\times V\) and \(P\subseteq V\times S\). Adaptive deterministic bound \(O(\sqrt{np\lvert S\rvert}+n)\) on general digraphs, including prefixes, with no advance knowledge of \(S,p\). Uses Theorems 9 and 11. | [Both orientations](OnlineReachabilityPreservers/DagReduction.lean) proved on general digraphs with an explicit finite edge bound. Both list evaluators have polynomial source-level tallies across all prefixes. |
| Theorem 3, cited [8] | Lower bound \(\Omega((np)^{2/3}+n)\) against the stronger adversary that starts with an empty graph and inserts edges before each demand. Definition 18 of [8](https://arxiv.org/pdf/2212.11944v4) gives the game, Theorem 29 gives the lattice, and Lemma 45 states a general transfer. | [Checked](OnlineReachabilityPreservers/StrongAdversary.lean) for exact counts \(n\ge2\) and \(1\le p\le n^2\), with distinct feasible demands and constant 576. The proof forces every edge of each revealed line directly from its slope. |
| Theorem 4 | Offline deterministic polynomial-time pairwise bound \(O(n^{3/4}p^{1/2}+n^{2-\sqrt2+o(1)}p^{1/\sqrt2}+n)\), also rounded to \(O(n^{.75}p^{.5}+n^{.59}p^{.71}+n)\). Uses the independence construction in Lemma 14 and the Appendix B extremal estimate, with degeneracies and the additive \(p\) handled in the graph bound. | [Both edge bounds](OnlineReachabilityPreservers/OfflineSharp.lean) hold for the constructed preserver on general digraphs. The limiting bound holds with zero exponent slack. The exact greedy deletion evaluator has a polynomial source-level tally. |
| Theorem 5 | Both Theorems 1 and 2 transfer to preassigned simple paths, either with the total \(p\) known or with the arrival index \(i\) as a path-selection input. In the restricted case \(S\) is given. Uses Theorems 15 and 16. Fully non-adaptive path selection with neither parameter is left open. | The [pairwise rates](OnlineReachabilityPreservers/PairwiseNonAdaptive.lean) and [both endpoint promises](OnlineReachabilityPreservers/RestrictedNonAdaptive.lean) are checked for both models on general digraphs. The [path lift](OnlineReachabilityPreservers/PathAssignments.lean) uses a subset of the shared connectors in each simple path. The [pairwise selectors](OnlineReachabilityPreservers/AssignmentListPairwiseWork.lean) and [restricted selectors](OnlineReachabilityPreservers/AssignmentListRestrictedWork.lean) have polynomial source-level tallies per query. Exact all-prefix edge sets and polynomial source-level bounds in both models are checked for the pairwise and both restricted selectors. |
| Theorems 6 and 7, cited [1,15,21] | Prior offline approximation with \(\min(n^{4/7+\varepsilon},p^{1/2+\varepsilon})\) and online competitive ratio \(\widetilde O(p^{1/2+\varepsilon})\) from [21]. | Cited background |
| Theorems 8 and 21 | Same new online unit-cost directed Steiner forest result, randomized polynomial time and competitive ratio \(O(n^{3/5+\varepsilon})\). Theorem 21 uses the early-pair algorithm of [21], all-pairs thick-demand hitting, the thin-pair online rounding from the [24] framework, the two orientations of Theorem 2, and Lemmas 20 and 22. | [The full online algorithm](OnlineReachabilityPreservers/SteinerComplete.lean) checks the expected \(O(n^{3/5+\varepsilon})\) rate against any feasible offline solution on a fixed demand trace, including zero optimum and repeated requests. The first block of distinct non-self requests is chosen independently of the random seeds. Correctness and monotonicity hold on every realization. The [sampled arrival implementation](OnlineReachabilityPreservers/SteinerBinaryArrivals.lean#L329) computes the exact bit budget, draws the seed once before the first arrival, and bounds total recorded work by a polynomial in the input sizes at fixed height. The [guarded binary entry](OnlineReachabilityPreservers/SteinerBinaryWordGuarantee.lean#L126) adds exact word decoding and its polynomial input tally, with the same correctness, prefix and expectation guarantees. A native execution bound remains open. |
| Theorem 9 | A DAG algorithm lifts to general digraphs by SCC contraction, adding at most \(2n\) edges via one in-tree and one out-tree per component. Needs online composition, representative edges, and a budget monotone in demand and endpoint counts. Keeping isolated labels preserves the vertex count. | [SCC lift with exact overhead](OnlineReachabilityPreservers/DagReduction.lean) and prefix monotonicity proved for a DAG algorithm on arbitrary lists. The distinct-demand lift keeps first occurrences after SCC projection. Lean checks preservation of every original request, prefix monotonicity, and the same budget with the \(2n\) overhead when the bound is monotone in the projected demand and endpoint counts. A [separately metered reference](OnlineReachabilityPreservers/AlgorithmSearchWork.lean) returns the same stable deduplication result using at most \(p^2\) pair-equality tests on one \(p\)-entry projected trace. |
| Algorithms 1 and 2, Lemma 10 | Forward and backward growth prefer a previously bought feasible edge at every vertex. Ordered compression keeps new-edge tails and the terminal in the forward case, or the origin and new-edge heads in the backward case. The family is acyclic, its size is exactly \(m+p\) on reachable processed requests starting with an empty preserver, and it excludes bridges with the first or last arc earlier than the river, respectively. | [Growth](OnlineReachabilityPreservers/Growth.lean) and [ordered compression](OnlineReachabilityPreservers/Bridges.lean) checked. |
| Theorem 11 | DAG upper bound for both endpoint promises. The printed proof uses Lemmas 12 and 13 when the average degree is large. | [Both orientations](OnlineReachabilityPreservers/Restricted.lean) use a direct count of collisions between new-edge tails, which uses the same earlier-edge conflicts as the forbidden-bridge proof and handles shared endpoints. The exact bound also covers small average degree. |
| Lemma 12 | Reverse-arrival insertion has a path with at least \(\ell/4\) vertices of degree at least \(d/4\) at insertion. | [Checked](OnlineReachabilityPreservers/RestrictedIncidence.lean) for any positive-mass finite family. The degree counts the current path and all previously inserted paths. The statement uses exact integer inequalities with denominators cleared. |
| Lemma 13 | For distinct sink-restricted requests and sufficiently large average degree, the compressed size satisfies \(\ell d\le O(\lvert S\rvert)\). | [Checked](OnlineReachabilityPreservers/RestrictedIncidence.lean) with constant 24 and \(d\ge2\), by combining the exact new-edge-tail estimate with \(p\le n\lvert S\rvert\). The checked argument uses the compressed mass including the terminal of each request. |
| Lemma 14, cited [8] | Independence lemma connects bridge-free path systems to extremal offline preserver size. The constructive direction uses minimally necessary edges and shortcutting, with tightness in the extremal sense. | The [DAG upper direction](OnlineReachabilityPreservers/OfflineIndependence.lean) and [exact acyclic lower construction](OnlineReachabilityPreservers/AcyclicOverlay.lean) are checked. The [general upper direction](OnlineReachabilityPreservers/OfflineBridgeExtremalUpper.lean#L56) bounds the actual lifted preserver by \(3M\) for positive budgets, with \(|E(H)|+p\le M+2n\) and \(M\) the unrestricted fully bridge-free maximum in the indexed simple-path convention. The [acyclic extremal lower bound](OnlineReachabilityPreservers/OfflineDemandLower.lean) uses exactly the original vertex and distinct-demand counts. The exact-count DAG lower constructions use Definition 1, which permits padding with unreachable pairs. The [unrestricted converse](OnlineReachabilityPreservers/OfflineBridgeConverse.lean#L315) gives a single DAG on exactly \(n\ge2\) vertices with exactly \(0\le p\le n^2\) distinct demands whose every preserver has at least \(M/24\) edges. Here \(M\) is the maximum over all fully bridge-free indexed simple path systems. The [consecutive-chain bound](OnlineReachabilityPreservers/OfflineConsecutiveEndpoint.lean#L197) applies after each vertex restriction. The [common-order subsequences](OnlineReachabilityPreservers/OfflineBridgeConverse.lean#L209) lose at most two incidences per vertex and keep every original last vertex. The [ordered-block reduction](OnlineReachabilityPreservers/OfflineOrderedBlocks.lean) gives an exact-count DAG lower bound within factor \(12b\) of the mass of any simple nonempty full-bridge-free family whose paths each have at most \(b\) increasing blocks in one order. One common numbering with at most one descent per path gives factor 24. If that numbering exists after pruning opposite intersections, the original mass is bounded within factor 48. [Coordinate triangles](OnlineReachabilityPreservers/TriangularCoordinatePaths.lean#L485) give fully bridge-free families requiring arbitrarily many blocks in any common numbering after pruning. The [subsequence reduction](OnlineReachabilityPreservers/OfflineOrderedBlocks.lean#L69) also uses the total mass retained by arbitrary increasing subsequences in a common order. The [component-visit construction](OnlineReachabilityPreservers/OfflineOrderedBlocks.lean#L184) keeps one vertex per strongly connected component of the precedence graph on each path. If each path meets each component in at most \(b\) vertices, it gives factor \(12b\), with the exact original vertex and distinct-demand counts. One vertex per visit can lose an arbitrarily large factor even after opposite pruning. If the incidence mass satisfies \(M\le C(n+J)\), where \(J\) counts all path-component visits, the [aggregate lower construction](OnlineReachabilityPreservers/OfflineComponentOrders.lean#L246) gives factor \(14C\) for \(n\ge 2\) and \(1\le p\le n^2\). It selects either the spanning path or the component-visit graph. The bound follows by summing [linear incidence caps](OnlineReachabilityPreservers/OfflineComponentOrders.lean#L276) in the separate components and gives [factor \(28C\)](OnlineReachabilityPreservers/OfflineComponentOrders.lean#L314) when the caps are applied after opposite pruning. A [lattice family with private return paths](OnlineReachabilityPreservers/OverlayLowerAudit.lean#L509) gives arbitrarily large \(M/(n+J)\) even after pruning, with every path in one precedence component. A uniform bound on the mass retained by independently ordered subsequences within each component would extend to the whole family. [Component proofs](OnlineReachabilityPreservers/OfflineComponentOrders.lean) The [converse in two demand regimes](OnlineReachabilityPreservers/OfflineConverseRegimes.lean) allows cyclic simple path systems with no full bridge through size four and proves the bound when \(p^2\le K n\) or \(n^2\le Kp\), with factor \(C K\). It combines Theorem 43 with linear lower constructions. The overlay uniqueness step fails [even with unique intersections](OnlineReachabilityPreservers/UniqueSplitAudit.lean). The [unbounded gap for the cited overlay](OnlineReachabilityPreservers/OverlayLowerAudit.lean) shows that even a constant-factor edge lower bound can fail for that graph and those endpoint demands. The [acyclic lattice family](OnlineReachabilityPreservers/OverlayLowerAudit.lean) forces \(L^7\) edges on \(4(L+1)L^5\) vertices with exactly \(L^6\) distinct feasible demands for \(L\ge1\). The [all-sizes lattice lower bound](OnlineReachabilityPreservers/OfflineLatticeLower.lean) gives a DAG forcing \(\Omega(n+p+n^{2/3}p^{1/2})\) edges at every exact count \(n\ge 2\), \(1\le p\le n^2\). A [multidimensional lattice](OnlineReachabilityPreservers/OverlayLowerAudit.lean) uses one coordinate for the squared norm of the slope vector. For any positive number of free slope coordinates, Lean fits the grid to the exact vertex and demand budgets. With \(d-1\) slope coordinates the [lower rate](OnlineReachabilityPreservers/OfflineLatticeLower.lean) is \(n^{2/(d+1)}p^{(d-1)/d}\) for \(d\ge2\), with a constant depending on \(d\). The [all-range comparison with a polynomial loss](OnlineReachabilityPreservers/OfflineConverseRegimes.lean) combines three lattice rates with Theorem 43. Its loss factor is \(C n^{(7-8/\sqrt{2})/10}\). At \(p=n^{6/5}\), the unrestricted collection of normalized lattice powers is bounded by \(n^{13/10}\), which is attained by the two- and three-coordinate rates. |
| Algorithm 3 and Theorem 15 | For a deterministic current-state path rule with a uniform prefix budget \(F\) at \(p>0\), buy paths with more than \(F/p\) missing edges before assigning the remaining paths against the frozen graph. Fewer than \(p\) such purchases, and any \(p\) preassigned paths have union size at most \(2F\). Use the allowed demand domain for the restricted case. | [Checked](OnlineReachabilityPreservers/KnownBudget.lean), with strict integer comparison and preservation of the rule's paths. |
| Algorithms 4–5 and Theorem 16 | Precompute Algorithm 3 at positive dyadic budgets \(q\) starting at a linear-cost threshold. The arrival index chooses its first covering budget. Footnote 4 requires the sum of dyadic bounds to be dominated by the final term and bounded doubling of the bound. For \(p\) below the starting threshold, use the linear term directly. Domains and planned budgets can be capped by the finite pair population or the number of distinct arrivals. | [Checked](OnlineReachabilityPreservers/IndexSensitive.lean) under the two growth inequalities specified by footnote 4, with explicit constants and executable dyadic selection. |
| Theorem 17, cited [24] | Randomized polynomial-time online UDSF with competitive ratio \(O(n^{2/3+\varepsilon})\). | The expected rate follows from the stronger [Theorem 21](OnlineReachabilityPreservers/SteinerComplete.lean). The original implementation from [24] is cited. End-to-end runtime remains open. |
| Theorem 18, cited [21] | Early-pair algorithm. The printed \(T^{1/2-\varepsilon}\) conflicts with the \(T^{1/2+\varepsilon}\) exponent used later in Section 5. The cited result [21] gives the latter exponent with graph polylogarithms. | A replacement [unit-cost algorithm](OnlineReachabilityPreservers/SteinerEarlyRound.lean) on fixed feasible traces of distinct non-self requests has an [explicit mean cost](OnlineReachabilityPreservers/SteinerOnlineRounding.lean) and a [standalone expected rate](OnlineReachabilityPreservers/SteinerCompetitive.lean) of \(K(1+\log n)^{h+4}T^{1/2+\varepsilon}\,\mathrm{OPT}\), with one fixed positive height \(h\) and constant \(K\) for each \(\varepsilon>0\). The demand-dependent bound holds for every prefix. The proof uses the [rooted-tree comparison](OnlineReachabilityPreservers/SteinerJunction.lean), [height-reduction intervals](OnlineReachabilityPreservers/SteinerHeightIntervals.lean) and [fractional forest](OnlineReachabilityPreservers/SteinerForestNetwork.lean). It supplies the early phase of Theorems 8 and 21. The original buy-at-bulk algorithm and runtime remain separate items. |
| Theorem 19, cited [6] | Randomized polynomial-time online thin-demand algorithm with expected cost \(\widetilde O(\tau)\,\mathrm{OPT}\). | The replacement [cut-cover algorithm](OnlineReachabilityPreservers/SteinerThinCover.lean) and [fixed-threshold rounding](OnlineReachabilityPreservers/SteinerThinRound.lean) check irrevocable feasibility for every realization and the expected edge cost on fixed traces of distinct non-self thin requests. The [separator](OnlineReachabilityPreservers/SteinerCutFlow.lean) uses bounded unit augmentations. End-to-end runtime remains open. |
| Lemma 20, cited [24] | Terminal incidences give \(\mathrm{OPT}\ge\sqrt p\) for distinct non-self demands. | [Checked](OnlineReachabilityPreservers/SteinerCounting.lean) as \(p\le\mathrm{OPT}^2\) for sets and nontrivial online traces. |
| Lemma 22 | Among \(p'\) nontrivial demands hit by the sampled hubs, each creates at least one previously unsatisfied terminal–hub connection. This implies \(p'\le 2\lvert S\rvert\,\mathrm{OPT}\) using oriented terminal incidence. | [Checked](OnlineReachabilityPreservers/SteinerCounting.lean) for every offline solution, with a monotone preserver and both hub subrequests served. |

The [weighted fractional cover](OnlineReachabilityPreservers/SteinerWeightedCover.lean)
provides a capacity-update routine for explicitly listed binary cuts.
It covers every revealed batch and bounds the update count
and objective by a logarithmic factor times an integral hitting solution,
with an additive baseline of at most one in the normalized objective.
The [integer capacity comparison](OnlineReachabilityPreservers/SteinerRoundedCapacities.lean)
checks an extra normalized cost of at most one. The
[general cut separator](OnlineReachabilityPreservers/SteinerCutFlow.lean)
supports the integer cutoff used for that comparison.
Its `ValidArcFlow.decompose_capacity` extracts a list of simple unit routes
whose incidence on every arc is bounded by that arc's capacity.
The [weighted network run](OnlineReachabilityPreservers/SteinerWeightedNetwork.lean)
uses actual separating cuts and certifies flow in the graph of each request
with its own free attachments. The rounded normalized objective pays an
additive baseline of at most two and a logarithmic factor times the
chosen integral solution.
The [height-block proof](OnlineReachabilityPreservers/SteinerHeightBlocks.lean)
constructs the shortened segments on the original rooted routes, checks
their concatenation, and bounds their weighted cost. The
[inward metric tree](OnlineReachabilityPreservers/SteinerHeightTree.lean)
has depth at most the given limit. Any selected links expand to original
edges at cost at most their weights. The
[forward height reduction](OnlineReachabilityPreservers/SteinerHeightEmbedding.lean)
embeds any inward arborescence with at most \(k\) designated terminals
into the fixed template. The selected links preserve the terminal labels
and cost at most \(4h k^{1/h}\) times the original unit-cost tree size.
The [paired forest](OnlineReachabilityPreservers/SteinerHeightForest.lean)
keeps every group path within one root. A feasible original solution
of size \(M\) gives a forest solution of cost at most
\(12h p^{1/h}(\lfloor\sqrt p\rfloor+1)M\). The
[forest network](OnlineReachabilityPreservers/SteinerForestNetwork.lean)
uses those links to prove feasibility and the cost bound for the actual
fractional online run. Zero-cost metric links are always free. Leaf
attachments are local to the current source and sink groups. The
[flow decomposition on this forest](OnlineReachabilityPreservers/SteinerForestFlow.lean)
assigns each unit path to the same root on both sides. It supplies equal
terminal mass on the two sides of each root, bounded by the capacities
on all ancestor links. With \(H\)
denoting the template vertex set, the capacity scale is at most
\(\max(1,n|H|^2)\). The [tree rounding probability](OnlineReachabilityPreservers/SteinerTreeRounding.lean)
gives a one-sided success probability of at least \(1/(h+1)\) when
the ancestor marginals dominate a unit terminal flow. Its proof uses
independent finite thresholds and the common-prefix second moment.
The [dyadic threshold construction](OnlineReachabilityPreservers/SteinerDyadicRounding.lean)
makes these marginals computable from integer capacities. It caps them
at the active root's scale and takes ancestor minima. The thresholds
give the exact normalized marginals and preserve the one-sided
probability bound when the integer terminal mass fits.
The [paired rounding trial](OnlineReachabilityPreservers/SteinerForestRounding.lean)
selects actual metric links using shared root gates and independent
thresholds within each side of a root. If the fractional state covers
a request, one trial misses it with probability at most
\(\exp(-1/(4(h+1)^2))\). A [fixed-tier cost bound](OnlineReachabilityPreservers/SteinerOnlineRounding.lean)
controls the chance that a paid link is ever selected across prefixes.
The proof counts ancestor capacity profiles and uses the final monotone
capacities. The [early integral algorithm](OnlineReachabilityPreservers/SteinerEarlyRound.lean)
uses independent trials to amplify success, keeps all prior purchases, and falls back to the
input graph on a miss. For a fixed feasible sequence of distinct
requests with positive height, the expected fallback cost is at most
two edges. The [explicit early cost theorem](OnlineReachabilityPreservers/SteinerOnlineRounding.lean)
then adds the expected original expansion cost, using the total paid
fractional capacity and the number of trials, tiers and profiles.
The [early rate](OnlineReachabilityPreservers/SteinerCompetitive.lean)
chooses one height for each positive exponent slack and absorbs the
polylogarithmic loss. The [complete construction](OnlineReachabilityPreservers/SteinerComplete.lean)
uses the first \(T\) distinct non-self arrivals, so the early cost proof
applies to a fixed input trace. Lemma 20 still supplies the offline
lower bound when the late phase starts. The
[sampled arrival implementation](OnlineReachabilityPreservers/SteinerBinaryArrivals.lean#L329)
has polynomial total recorded work at fixed height, including computing
and drawing the prescribed number of fair bits.
A native execution bound remains open.

## Search and sampling work

The [search counters](OnlineReachabilityPreservers/SearchWork.lean)
return the ordinary search outputs, including failed searches. The
[distinct-demand counter](OnlineReachabilityPreservers/AlgorithmSearchWork.lean)
returns the projected first occurrences with at most one pair comparison per
entry of the original list for each processed request.
Reverse search inspects at most \(n|E|\) arcs, and greedy path
growth tests at most \(2n^2\) successor candidates. One weighted
fractional run on the paired height forest \(H\) with \(p\)
requests makes at most \(p((B+1)B+1)\) separator calls for
\(B=\max(1,n|V(H)|^2)\).
Each integer augmentation loop makes at most its supplied number
of path searches. The [separator work](OnlineReachabilityPreservers/SeparatorWork.lean)
bounds residual pair inspections and route tests within each augmentation,
accounts for the final reachability search on a failed flow, and composes
the work over a full weighted fractional run on the paired forest. The
thin separator shares its reachability interval across capacity tests.
Its interval count covers the search inspections and filter, with graph
container construction outside that term. The [thin run counter](OnlineReachabilityPreservers/ThinSearchWork.lean)
also covers reconstruction of the cut to update loads, caching the interval
before its edge filter. Across a feasible
trace it charges at most one separator budget per request plus one per
unit of total load increase, which is at most \(|E|(\lfloor\log_2|E|\rfloor+1)\).
The [thin rounding counter](OnlineReachabilityPreservers/SteinerThinReplay.lean)
composes that budget with the rounded-arc scan and reachability test at
every prefix, including the final evaluation if there is no miss.
The [early rounding counter](OnlineReachabilityPreservers/SteinerEarlyReplay.lean)
shares each prefix's weighted fractional evaluation between its miss test
and the union of metric purchases. It bounds the original-graph route
expansions and reachability checks, including the optional final expansion.
The [distance table](OnlineReachabilityPreservers/SteinerDistanceTable.lean)
records all original hop distances before constructing the paired forest.
The table-backed prefix evaluator uses those values for both orientations
of the template, for arc weights in separation, and for rounding decisions.
It returns the ordinary graph and adds one charge for building the table.
Each stored lookup takes at most \(n^2\) key comparisons.
The [late search counter](OnlineReachabilityPreservers/SteinerLateReplay.lean)
bounds request classification, both projected hub runs, and thin rounding.
The [complete search counter](OnlineReachabilityPreservers/SteinerCompleteReplay.lean)
returns the ordinary seeded algorithm's graph at every prefix of a feasible
trace. Its measured operations have an explicit polynomial bound at fixed
height, including when the whole list of prefixes is evaluated.
The [shared-table replay](OnlineReachabilityPreservers/SteinerDistanceReplay.lean)
adds one distance-table preparation to this bound for the whole list.
The prepared evaluator also shares the paired template, priced and free
links, scale, and separator fuel with every early prefix. The weighted
network loop passes the same scale and fuel through each request update.
The [template work bound](OnlineReachabilityPreservers/SteinerTemplateWork.lean)
counts comparisons in both orientations while checking successive labels
in every candidate history. With \(H\) candidates per root and height \(h\), the
one-time template cost is at most \(2n^3Hh\) table key comparisons.
The replay reports that cost separately from the table's arc inspections.
The [rounding counter](OnlineReachabilityPreservers/SteinerRoundingWork.lean)
counts the original weight reads in a set of integral rounding trials.
It returns the same link union and bounds key comparisons by
\(t|E_F|n^2(1+2(\lfloor\log_2 S\rfloor+1)(h+1)^2)\) for \(t\) trials
at scale \(S\) on the prepared forest \(E_F\). The two ancestor minima per
cutoff use at most \(h+1\) ancestors each. This count is for one rounded
fractional state.
The [rounding replay](OnlineReachabilityPreservers/SteinerDistanceReplay.lean)
includes those comparisons along with the measured searches at every
prefix. Its output graphs agree with the ordinary seeded evaluator.
With \(p\) arrivals, it adds at most \((p+1)^2\) calls' worth of rounding
comparisons to the search budget and reports the preparations separately.
The [route counters](OnlineReachabilityPreservers/RouteWork.lean)
bound arc inspections for SCC labels and shortest routes, and
sum the search work over greedy forwards growth. They also bound
SCC projection and lift calls and the number of thin-flow separators.
The [prune counter](OnlineReachabilityPreservers/OfflineIndependence.lean)
bounds reachability calls by \(2|E|p\). The
[quota counter](OnlineReachabilityPreservers/KnownBudget.lean)
bounds the number of base path-rule calls at each candidate budget
and shares each evaluated candidate across selection and counting.
The [deterministic search budgets](OnlineReachabilityPreservers/AlgorithmSearchWork.lean)
compose the SCC and connector searches with the forward and reverse online
runs and the offline pruning algorithm. The forward budget also covers
evaluating the whole list of arrival prefixes.
The [sample coordinates](OnlineReachabilityPreservers/SteinerSeedCoordinates.lean)
are in bijection with the nested early seed and preserve the
uniform finite probability. The [bit sampling bound](OnlineReachabilityPreservers/SteinerSamplingWork.lean)
represents the early coordinates by fixed-width fair bit words. It proves
the exact uniform target probabilities for independent rejection proposals
for hub and thin draws, with at most two proposals in expectation per
coordinate. The expected number of bits for all three seeds has an explicit
polynomial bound for each fixed height.
The [retry evaluator](OnlineReachabilityPreservers/SteinerRetry.lean)
reads finite fair-bit proposals until the first accepted word. Its checked
first-success events give the uniform coordinate law and the expected
number of bits. The probability of each finite joint attempt event factors,
and the product of the resulting laws is uniform on the complete algorithm's
three seed types. This model takes its fair bits as input.
The [consecutive decoder](OnlineReachabilityPreservers/SteinerBitSeed.lean)
uses a single finite bit list for those choices. It returns the seed, the
individual rejection counts, and the unread suffix when the supplied list
contains a complete sample. The [graph-based replay](OnlineReachabilityPreservers/SteinerBitOrders.lean)
constructs the required bijections for early coordinates, vertices, and arcs.
The [raw-prefix law](OnlineReachabilityPreservers/SteinerBitReplay.lean)
identifies the event for a specified seed and joint rejection counts on
a uniform raw prefix of the corresponding length. Its probability factors
into the early grid probability and the coordinate first-success probabilities.
Additional bits leave a completed result unchanged and remain in the returned
suffix. Successful consumed inputs are prefix-free. The
[joint sum](OnlineReachabilityPreservers/SteinerBitLaw.lean) over all rejection
profiles has the uniform seed law, and the weights over all outcomes sum to
one. The resulting expected edge count agrees with the finite-seed mean in
Theorem 21 for every fixed trace and gives its competitive bound.
The [weighted joint sum](OnlineReachabilityPreservers/SteinerBitLaw.lean)
gives the exact expectation of the lengths of those successful prefixes.
The [product measure](OnlineReachabilityPreservers/SteinerBitMeasure.lean)
assigns those same probabilities to the disjoint first-success events on
infinite fair-bit streams. The decoder succeeds on a finite prefix almost
surely. Its consumed bit count has the fixed-height polynomial bound in
expectation, and the edge integral gives the finite-seed mean on every fixed
trace. A successful decoding feeds the same seed and graph sequence to the
weighted prefix evaluator. The [fixed-budget run and replay](OnlineReachabilityPreservers/SteinerBitBudget.lean)
use a graph-dependent bit budget equal to a bound on the expected number of
bits consumed multiplied by the arc count. Lean bounds this tighter budget
by the preceding polynomial. Exhausting a fixed prefix is almost surely
exactly the event that the consumed length exceeds its budget. Markov's
inequality bounds this probability by the expected consumed length divided
by one plus the budget. The fallback buys the input graph at the first
non-self request, adding at most one edge in expectation. This gives the same
competitive exponent for a uniform finite bit word, with prefix preservation
and zero cost when the offline optimum is zero. The cached replay shares
one distance table and forest plan across budget calculation, decoding,
and prefix evaluation. Its bound on measured searches and table operations
includes preparation on both branches. The fallback computes the prefix
graphs with one scan. The [arithmetic history index](OnlineReachabilityPreservers/SteinerBitOrders.lean)
keeps the canonical seed-coordinate order. The empty history occupies the
first slot. Every first label starts a block of shorter histories with a size
computed by recurrence. Ranking within these blocks avoids listing and sorting
the history space. The cached replay uses sorted vertex and arc arrays.
A [separate comparison counter](OnlineReachabilityPreservers/SteinerSortWork.lean)
follows Lean's native merge schedule for any list representing a set. It
returns the canonical sorted order. The [combined bound](OnlineReachabilityPreservers/SteinerBitOrders.lean)
covers one sort of `m` entries and `q` binary rank lookups by at most
`(m+q)*m.size` key comparisons, where `m.size` is the bit length. Inverse
ranks read the corresponding stored position.
The [bit cursor](OnlineReachabilityPreservers/SteinerBitCursor.lean) reads
the requested positions directly, with a tail-recursive word accumulator. The
[cursor decoder](OnlineReachabilityPreservers/SteinerBitSeed.lean) agrees with
the list decoder on the sampled seed, rejection counts, unread suffix,
and failure. The cursor advances by the exact number of proposal bits read on success. The [replay proof](OnlineReachabilityPreservers/SteinerBitReplay.lean) shows that changing bits outside the consumed interval preserves the seed, rejection counts, and final cursor. A separate reference decoder also reports
the position after the last complete word on exhaustion. Lean checks exact
agreement with the established result and that the reported position stays
within the supplied prefix. A failed positive-width rejection phase consumes
all complete proposals it can read. The cached replay starts at position zero. Integer
arithmetic, finite container operations, and full execution time still
require certification.
The [list-backed forward run](OnlineReachabilityPreservers/DeterministicListWork.lean)
returns the ordinary forward run's edge set on every prefix. It counts vertex
equality tests, minimum comparisons and arc-pair equality tests in reverse
reachability, the two successor scans, the walk, and each edge purchase. For
\(n\) vertices, an input arc list of length \(m\), and \(p\) requests, its
explicit comparison bound is
\[
p\bigl(2n^2m+(n+1)(1+n(m+n^2+2))+n^3\bigr).
\]
The preserver list stays duplicate-free. The forward-run bound measures key
operations in this representation. Each pair equality or minimum call is
one charged operation. General-digraph SCC preprocessing, the implementation
cost of each key operation, other list operations, and arithmetic time are
separate costs.
The [list-backed SCC preparation](OnlineReachabilityPreservers/SccListWork.lean)
builds the exact least-vertex labels using two bounded reverse searches per
vertex. The evaluator shares one transpose and one label table. Projection
looks up each endpoint in that table. The resulting condensation is
exact and duplicate-free. With a complete duplicate-free vertex list,
its comparison count is at most
\[
n\bigl(4n^2m+n(n+1)\bigr)+m(2n+1+n^2).
\]
The same table supplies the demand projection. The condensed forward run
adds at most \(p(2n+B(n,m))\) comparisons, with \(B\) the list-backed
per-arrival forward budget. These counts cover the input condensation and
the forward computation in the quotient. Lifting the selected arcs and
building the internal connectors are separate operations.
The [list-backed lift](OnlineReachabilityPreservers/SccLiftListWork.lean)
chooses the original lexicographically least arc for every selected quotient
arc in the chosen orientation. The source evaluator reverses the input
and reverses its output back. The lift also builds both ordinary shortest-hop
connector trees using the cached labels. One merge of connectors and
representatives yields the exact duplicate-free preserver edge sets. Each nonempty
call uses one label table, charges a second raw-arc projection for the lift,
and charges the comparison work of both connector orientations. Both
all-prefix replay theorems include the cost of rerunning the preparation and
lift at each prefix. The [greedy deletion evaluator](OnlineReachabilityPreservers/OfflineListWork.lean)
sorts the duplicate-free quotient arcs in the same order as the ordinary
offline preserver. It charges the sort, edge filters, and bounded
reachability checks, and the common lift gives the exact offline preserver
with a polynomial key-comparison bound on general digraphs. The original
raw arc list may contain duplicates. These comparison theorems count abstract
key tests in supplied list representations.

The [reverse-search tally](OnlineReachabilityPreservers/DeterministicListWork.lean#L622)
also charges list-cell inspection and construction and loop control. The
[SCC preparation tally](OnlineReachabilityPreservers/SccListWork.lean#L405)
extends this model to the transpose, component labels, and exact
duplicate-free quotient.

The [forward-run tally](OnlineReachabilityPreservers/DeterministicListWork.lean#L753)
adds successor selection and purchases. The
[sink](OnlineReachabilityPreservers/SccLiftListWork.lean#L976) and
[source](OnlineReachabilityPreservers/SccLiftListWork.lean#L999) prefix theorems
return the exact edge set at every reveal. They charge both connector directions,
the lift, and materializing and recomputing all prefixes. The
[offline tally](OnlineReachabilityPreservers/SccLiftListWork.lean#L1021)
includes sorting into the same lexicographic order, all tested greedy deletions,
and the final lift. The model starts from the supplied arc and vertex lists,
counts each composite key operation as one unit, and excludes counter maintenance.
Each bound is an explicit polynomial in the vertex, raw arc, and request counts.
For graphs with vertex keys in `Fin n`, the enumerator constructs a complete
duplicate-free vertex list in exactly \(8n+1\) units of this tally. Both
prefix algorithms and the offline algorithm have bounds that include
constructing this list once. Conversion from other vertex representations,
machine allocation and comparison costs, and bit arithmetic remain open.
The preassigned paths and Steiner algorithm have the separate bounds below.
[Vertex enumeration](OnlineReachabilityPreservers/DeterministicEnumerationWork.lean#L46)
· [Sink prefixes](OnlineReachabilityPreservers/DeterministicEnumerationWork.lean#L69)
· [Source prefixes](OnlineReachabilityPreservers/DeterministicEnumerationWork.lean#L84)
· [Offline deletion and lift](OnlineReachabilityPreservers/DeterministicEnumerationWork.lean#L99).

The [preassigned-path counter](OnlineReachabilityPreservers/AssignmentSearchWork.lean)
combines the calls made by quota certification and path selection with the
arc inspections and successor tests in each base rule and lifted path.
This covers known totals and arrival indices in all three endpoint scopes.
The indexed pairwise evaluator returns the ordinary union of all assigned
paths in one prefix and sums their search work. The quota count is bounded
by a polynomial in the graph sizes and the known total or current index.

The list-backed pairwise selectors return the exact path option for a
[known total](OnlineReachabilityPreservers/AssignmentListPairwiseWork.lean#L28)
or an [arrival index](OnlineReachabilityPreservers/AssignmentListPairwiseWork.lean#L104).
They build the all-pairs candidate list, scan the candidates in each
quota simulation, choose the least successful certificate up to the quotient
arc count with that count as a fallback, and replay the selected trace.
The count includes SCC preparation, both
connector directions, the lift, and the final hop-decreasing route.
The indexed selector also charges the square-root scan and dyadic search.
The bounds are explicit polynomials in the input list lengths and the total
or index, with a complete duplicate-free vertex list and the same unit
charges for key operations and natural-number arithmetic.

The [one-arrival update](OnlineReachabilityPreservers/AssignmentPrefixesWork.lean#L47)
selects the current demand's assigned path and inserts its edges into the
accumulated list. It uses the current demand and index and does not consume
any later demand. The all-prefix evaluator applies this update once per
arrival and returns a duplicate-free list representing the exact
assigned-path union at every prefix, including the empty prefix.
The bounds include one complete enumeration when vertex keys are in
`Fin n`. Native execution and bit costs have separate proof obligations.
[Known-total prefixes](OnlineReachabilityPreservers/AssignmentPrefixesWork.lean#L181)
· [Arrival-index prefixes](OnlineReachabilityPreservers/AssignmentPrefixesWork.lean#L197)
· [Known-total with enumeration](OnlineReachabilityPreservers/AssignmentPrefixesWork.lean#L214)
· [Arrival-index with enumeration](OnlineReachabilityPreservers/AssignmentPrefixesWork.lean#L229).

The endpoint-restricted list selectors use a complete duplicate-free vertex
list and a duplicate-free list of allowed sources or sinks. They charge
the projection of allowed endpoints, construction of the quotient candidate
domain, the integer square-root budget, and the prescribed-budget
simulation and replay. The indexed selectors also charge finding the
dyadic quota. The source variants include reversal of the original graph
and the selected path. The path option agrees exactly with the ordinary
selector, including for an empty allowed set.
[Known-total sinks](OnlineReachabilityPreservers/AssignmentListRestrictedWork.lean#L85)
· [Indexed sinks](OnlineReachabilityPreservers/AssignmentListRestrictedWork.lean#L149)
· [Known-total sources](OnlineReachabilityPreservers/AssignmentListRestrictedWork.lean#L213)
· [Indexed sources](OnlineReachabilityPreservers/AssignmentListRestrictedWork.lean#L230).

All four restricted prefix bounds include the endpoint list traversals,
the selected paths, and the insertion at every arrival.
[Known-total sink prefixes](OnlineReachabilityPreservers/RestrictedAssignmentPrefixesWork.lean#L18)
· [Known-total sink prefixes with enumeration](OnlineReachabilityPreservers/RestrictedAssignmentPrefixesWork.lean#L33)
· [Known-total source prefixes](OnlineReachabilityPreservers/RestrictedAssignmentPrefixesWork.lean#L81)
· [Known-total source prefixes with enumeration](OnlineReachabilityPreservers/RestrictedAssignmentPrefixesWork.lean#L98)
· [Arrival-index sink prefixes](OnlineReachabilityPreservers/RestrictedAssignmentPrefixesWork.lean#L48)
· [Arrival-index sink prefixes with enumeration](OnlineReachabilityPreservers/RestrictedAssignmentPrefixesWork.lean#L66)
· [Arrival-index source prefixes](OnlineReachabilityPreservers/RestrictedAssignmentPrefixesWork.lean#L113)
· [Arrival-index source prefixes with enumeration](OnlineReachabilityPreservers/RestrictedAssignmentPrefixesWork.lean#L133).

The [weighted capacity counter](OnlineReachabilityPreservers/SteinerCapacityWork.lean)
prepares one capacity row per ordered pair before a separator call.
Each residual graph scans the stored values directly. Lean checks that
the scan gives the same graph and pair-visit count, including when the
last search recovers the cut. The keys are unique, so the residual graph
is constructed without a deduplication pass. The cut and fractional updates agree with
the ordinary run. With \(N\) network vertices, \(q\) requests, separator
fuel \(f\), \(m_F\) priced arcs, and at most \(B\) comparisons per weight
read, preparation adds at most \(qf(N^2+m_F B)\) to the measured search work. The
[capacity replay](OnlineReachabilityPreservers/SteinerDistanceReplay.lean)
applies this at every early fractional state with weights from the original
distance table. It additionally charges at most \(p(p+1)^2\) times the
per-request capacity comparison polynomial for \(p\) arrivals. The prefix
graphs and one-time preparation charges agree with the rounding replay.
The [complete weight-read replay](OnlineReachabilityPreservers/SteinerDistanceReplay.lean)
also charges the original table reads for the weighted link classes,
scale, and fuel. One shared row per link suffices, so setup adds at most
\(|E_F|n^2\) key comparisons. One fixed-height polynomial covers the
reported searches, capacity table visits, and original table reads across
the whole replay. Finite container operations, arithmetic bit costs, and
construction and application of the finite index enumerations remain separate
runtime costs. The ordinary graph-based bit entry point evaluates the forest
scale and the counts of finite seed coordinates before the measured replay.
The cached bit entry point shares the measured preparation and uses an
arithmetic coordinate count. Index enumeration, allocation, arithmetic in
lookups, and the cost of other container operations still need time bounds.
The [bounded-history rank](OnlineReachabilityPreservers/SteinerHeightIndexWork.lean#L63)
and [unrank](OnlineReachabilityPreservers/SteinerHeightIndexWork.lean#L111)
agree exactly with the lexicographic history index used in the early
coordinate order. With a supplied label converter of tally at most
\(C\), either direction at height \(h\) charges at most
\(6h^2+(C+24)h+7\) source-level operations. The tally includes each
block calculation, list step, and arithmetic operation, with division
and remainder charged as unit operations. For \(n\) vertex labels,
the [block sizes](OnlineReachabilityPreservers/SteinerHeightIndexWork.lean#L38)
fit in \(h\operatorname{bits}(n+1)+1\) bits. These bounds cover
one history conversion with the given label converter.

The [shared history enumeration](OnlineReachabilityPreservers/SteinerHistoryEnumerationWork.lean)
constructs every bounded history once in that same order, with no duplicate
histories. The [paired forest builder](OnlineReachabilityPreservers/SteinerPairedTemplateListWork.lean)
scans this list at each root for both orientations, builds the valid parent
arcs and root links, and produces a duplicate-free list of exactly the
standard forest arcs. The [distance-table instance](OnlineReachabilityPreservers/SteinerTemplatePreparationWork.lean)
uses one supplied original-hop table for both directions. For vertices
indexed by `Fin n`, its fixed-height polynomial covers generating the
roots, enumerating the histories, the table lookups, and the arc list.
The model treats arithmetic and original-key comparisons as unit
operations. Building the supplied distance table has a separate tally.

The [metered decoder](OnlineReachabilityPreservers/SteinerBitSeed.lean)
returns the exact three seed arrays and rejection counts on success and the
same end cursor on both outcomes. It fills a reserved array for each reached
stage. If \(b\) bits are consumed and \(q\) is the sum of the three requested
array lengths, its tally is at most \(24b+29q+55\) after parameter setup. Complete rejected
proposals count toward \(b\), and an incomplete proposal is left unread.
The [fixed-budget decoder](OnlineReachabilityPreservers/SteinerSeedDecoderWork.lean)
also charges calculation of the sizes, proposal widths, and total bit budget.
It has a deterministic polynomial tally for every supplied bit word at fixed
height. The [cached prefix replay](OnlineReachabilityPreservers/SteinerSeedDecoderWork.lean)
performs that decode once, charges the word width from the prepared forest
scale, and returns exactly the ordinary graph and measured search costs at
every prefix. The model charges indexed bit access and natural arithmetic at
unit cost. Constructing and applying the key-index maps and the other unmetered
container, native arithmetic, and allocation costs still require bounds.

The [list-backed initial preparation](OnlineReachabilityPreservers/SteinerFinPreparationWork.lean)
builds the hop rows directly from the input arc list with the checked
list-backed search. It shares the increasing vertex enumeration between
the table and both forest orientations. The rows match the ordinary hop
table in values and order. The duplicate-free forest list enters the
weighted plan without a deduplication pass. The
[fixed-budget prefix evaluator with that preparation](OnlineReachabilityPreservers/SteinerFinReplayWork.lean)
returns the same graph at every prefix for every bit word, including
exhaustion, and preserves the original weight-read and decoder tallies.
It bounds both list constructions together with the previously measured
operations by a single fixed-height polynomial in the vertex, arc, and
demand counts. The evaluator takes the graph, an input arc list with the
same arc set, and the graph's distinct arc count. The arc-list count
includes duplicate input records. Constructing the supplied graph and
count remains a separate operation.

The [weighted plan pass](OnlineReachabilityPreservers/SteinerWeightedPlanWork.lean)
reads each forest arc's two labels and stored hop weight once. It builds
the duplicate-free priced and free lists, accumulates the weight sum
and original comparison tally, and computes the exact scale and
separator fuel. Lean checks the label traversals, lookup charges,
list work and arithmetic at unit cost. The
[weighted preparation and replay](OnlineReachabilityPreservers/SteinerFinWeightedReplayWork.lean)
substitutes that plan in the fixed-budget evaluator and adds its
one-time work to the fixed-height polynomial. The cumulative allowance
retains the old comparison tally as well as the new bound on that pass.
All prefix graphs and existing tallies agree with the prior evaluator.

The [indexed replay](OnlineReachabilityPreservers/SteinerFinIndexedReplayWork.lean)
also prepares the canonical seed indexes for `Fin n` vertex keys. It scans
the raw arc list for each arithmetic lexicographic slot, then reserves and
fills one sorted arc array. Repetitions and arbitrary input order produce
the same canonical array. Vertex keys use their original numeric labels.
The [early-coordinate rank](OnlineReachabilityPreservers/SteinerEarlyCoordinateRankWork.lean)
uses arithmetic blocks for the trial, root, tier, and tree history.
The [array rank](OnlineReachabilityPreservers/SteinerArrayRankWork.lean)
charges each midpoint step on an arc lookup. Both lookup algorithms
produce the canonical rank and have a checked per-call word-work bound.
The replay charges construction of the indexes and preserves every
prior record.

The [streaming trace evaluator](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean)
prepares integer phase cutoffs and the duplicate-free sampled hub set
once for the replay after successful decoding. It maintains first
occurrences of non-self requests in arrival order and reuses the previous
computed record for repeats and self requests. Each new first-occurrence
prefix is split and evaluated once. Lean proves exact agreement with the earlier indexed
replay and bounds the extra phase preparation, split, and trace work.
The exhausted-word branch uses its own measured one-pass fallback.
The previous summed prefix tally is retained as a conservative allowance
when a previous result is reused.

The [early rounding evaluator](OnlineReachabilityPreservers/SteinerRoundingWork.lean)
records one gate read per trial, priced link, and tier, then one seed read
per tested ancestor whenever the gate opens. Free links use no seed
reads. Lean checks the same rounded graph and weight-read tally, and the
[prepared early evaluator](OnlineReachabilityPreservers/SteinerDistanceTable.lean)
sums the reads over the metric purchases it actually computes. The
[fixed-budget replay](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean)
adds these unit read charges to its trace tally with a fixed-height
polynomial bound. It preserves all previous graph and search records.

The [indexed thin decoder](OnlineReachabilityPreservers/SteinerSeedDecoderWork.lean)
retains access to the thin threshold array in canonical arc order, with
the same seed and decoder tally. After successful decoding, the
[threshold cache](OnlineReachabilityPreservers/SteinerThinReplay.lean)
takes one arc and one threshold directly from each stored position. The
[cached replay](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean)
shares these rows across late prefixes, including the thin branch's
reachability checks and final rounding. It preserves all prefix graphs,
earlier search and preparation tallies, and the seeded evaluation count.
The extra \(2m+9\) allowance for \(m\) arcs covers the two reads per row
and dispatch.

The [early and thin array views](OnlineReachabilityPreservers/SteinerSeedDecoderWork.lean)
come from the same fixed-budget bit decode. The [early seed reader](OnlineReachabilityPreservers/SteinerEarlyCoordinateRankWork.lean)
computes the arithmetic rank in the canonical seed order and reads the
word once at each used gate or ancestor test. The [forest work tally](OnlineReachabilityPreservers/SteinerRoundingWork.lean)
adds the returned rank costs while retaining the earlier weight tally.
The [rank-aware replay](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean)
sums these charges over the evaluated prefixes and retains the late
threshold cache. Lean checks a polynomial bound at each fixed height,
using a unit cost for an indexed array read and word-level arithmetic.
The prefix graphs, earlier base tallies, and seeded evaluation count
agree with the cached replay.

The [one-pass threshold builder](OnlineReachabilityPreservers/SteinerThinReplay.lean)
constructs the same cache from the supplied arc count and index. The
finite replay uses the canonical arc order.
Its \(11m+4\) word tally includes index traversal, the two reads per
row, and list assembly. The [replay with cache construction](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean)
charges this work on successful decoding and keeps the same fallback and
tally on exhaustion. The cumulative bound for each feasible trace adds \(11m+21\)
to the preparation and early trace polynomials. Other container work
and bit and native costs remain open.

The [incremental thin evaluator](OnlineReachabilityPreservers/SteinerThinReplay.lean#L800)
initializes one dense load table for a nonempty thin run, carries it
forward through the thin requests inside each evaluated late prefix, and
uses the rounded graph already computed for the final check when all checks
pass. The
[thin work bound](OnlineReachabilityPreservers/SteinerThinReplay.lean#L869)
covers that initialization, indexed updates on separating cuts, and
indexed rounding with repeated doubling. The [late equality](OnlineReachabilityPreservers/SteinerLateReplay.lean#L284)
preserves the rounded graph and previous search tally for every trace,
including the missed-thick fallback. The [complete replay specification](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L840)
preserves every earlier record and the evaluation count for every fixed
bit sample. With reachable requests, the [prefix bound](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L902)
adds the measured early and late work to the cumulative polynomial for
each fixed height. Remaining time obligations include separator, hub,
and container operations, bit arithmetic, and native array costs. The
inherited computation of the finite vertex count can also traverse the
vertex enumeration in the compiled evaluator.

The [indexed thin separator](OnlineReachabilityPreservers/SeparatorWork.lean#L668)
replaces the signed flow function by one array of ordered pairs for each
cut search. Each chosen augmenting arc increments its forward entry and
decrements its reverse entry. The selected augmenting paths, final flow,
cut and earlier search tally agree. For supply \(m\), the additional charge
per thin separator call is bounded by \(4n^2+m(20n+10)+23\). The
[thin bound](OnlineReachabilityPreservers/SteinerThinReplay.lean#L893)
uses the feasible trace's bound on the number of calls. The [complete replay](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L920)
includes this charge in the fixed-height polynomial and returns the same
prefix graphs on feasible traces. The [record equality](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L857)
also holds on exhaustion and infeasible traces.

The [rounded-list service check](OnlineReachabilityPreservers/SteinerThinReplay.lean#L268)
tests the current request directly on the retained arcs. The graph,
miss decision, and ordinary arc inspection tally agree with the
earlier check. The [thin fold](OnlineReachabilityPreservers/SteinerThinReplay.lean#L1069)
preserves the same graph and inspection tally for every trace,
including an entire-graph fallback after a miss. The [polynomial cap](OnlineReachabilityPreservers/SteinerThinReplay.lean#L1097)
adds the service work at each request on feasible traces with valid
threshold rows. This checkpoint covers the thin run.

The [capacity preparation](OnlineReachabilityPreservers/SeparatorWork.lean#L803)
initializes one pair table per cut search and evaluates a capacity once
for each arc in the demand interval. The [residual scan](OnlineReachabilityPreservers/SeparatorWork.lean#L894)
reads the stored capacity and signed flow at each ordered pair and constructs
the exact residual graph. It reuses one list of pair addresses across
augmentations and the final source-side search. The [separator specification](OnlineReachabilityPreservers/SeparatorWork.lean#L1084)
preserves the returned cut and the earlier search tally for every load
function. The additional work bound uses the load exponents' bound along
feasible thin traces. The [complete prefix theorem](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L966)
includes these charges in a fixed-height polynomial on feasible traces.

The [list route search](OnlineReachabilityPreservers/AssignmentListRouteWork.lean)
builds the same hop-decreasing graph and selects the same shortest route
in every residual graph. It uses the reachable list both to select the
route and to recover the previous successor-test count. The previous arc
inspection count is recovered from the two arc counts and the search depth.
The [cut comparison](OnlineReachabilityPreservers/SeparatorWork.lean#L1240)
also meters finding the terminal source side from the reversed residual
list. It returns the previous cut and search tally for every capacity
table and augmentation supply. The [complete prefix theorem](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1011)
includes these costs in its fixed-height polynomial on feasible traces.

The [arc preparation](OnlineReachabilityPreservers/SteinerFinArcRowsWork.lean#L136)
builds one duplicate-free arc list once per complete replay. The work
bound includes this pass and the earlier seed-index setup. For each
thin request within an evaluated thin run, the [interval construction](OnlineReachabilityPreservers/SteinerIntervalWork.lean#L145)
uses the forward and backward reaches to obtain the same interval vertices
and induced arcs. The [fractional loop](OnlineReachabilityPreservers/ThinSearchWork.lean#L933)
shares those rows across the cut searches and updates. The metered filters
restrict the same residual cut and select the same outgoing arcs for
doubling. Search and evaluation records still agree for arbitrary inputs.
The [complete prefix theorem](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1073)
includes these charges in the fixed-height polynomial on feasible traces.

The late phase also scans the stored arc list to choose the least sampled
hub for each non-self arrival and build the two ordered hub-leg lists.
The same list drives the short-circuit test for a missed thick demand.
The replay has the same graph and search records and the same number of
evaluations for all inputs. On feasible traces, the fixed-height
polynomial includes the new interval and trace-list operations.
[Hub selection and fallback scans](OnlineReachabilityPreservers/SteinerLateIntervalWork.lean)
· [Complete prefix bound](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1154).

The list-backed hub evaluator uses both projected preserver algorithms
and the same reachability decisions on their output arcs. It measures
the two orientations, each hit's service query, merging the two hub-leg
outputs, and merging the result with the thin graph. The count also
includes the late trace and fallback operations. The complete replay prepares
one ordinary vertex list for the hub routing and reuses the ordinary arc
list. On feasible traces it returns exactly the fixed-budget prefix graphs
and the same number of evaluations. The work bound includes the measured
late work, the earlier early search allowance, and the arc-inspection
allowance for the rounded thin service tests.
[Measured routing and service](OnlineReachabilityPreservers/SteinerHubRouteWork.lean)
· [Complete prefix bound with routing](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1506).

The outer union uses a single filter of the late graph against the early
arc set and a disjoint list append. Both operations have explicit
word counts. The complete evaluator uses this union at each evaluated prefix. All graph and search records and the evaluation
count agree with the earlier replay for every input. The fixed-height
bound includes the new union on feasible traces. The remaining thin
service operations, other container operations, bit
costs, and native costs remain open.
[Exact metered union](OnlineReachabilityPreservers/SteinerPhaseUnionWork.lean#L70)
· [Unchanged records](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1463)
· [Complete prefix bound](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1525).

The weighted run can also consume a supplied list of all ordered pairs
with each pair listed once. It stores accepted cuts in reverse order
for charge reads and returns them in their original order. The
[weighted history evaluator](OnlineReachabilityPreservers/SteinerWeightedChargeWork.lean)
proves equality of all charge values and the full cut list at the
same scale and fuel. Its bound includes explicit membership scans,
charge reads, integer capacity arithmetic with doubling, outgoing
cut selection, and the earlier residual search counts. The proof
also bounds each read of a returned charge.

The [explicit forest-pair enumerator](OnlineReachabilityPreservers/SteinerForestPairKeysWork.lean#L284)
forms the ordered pairs from the finite roots, the two sides, the history
nodes, and the three network labels. The one-time list construction uses
polynomial work at fixed height. The
[metric prefix evaluator](OnlineReachabilityPreservers/SteinerDistanceTable.lean#L1239)
shares this list across its weighted calls and preserves each rounded
early graph and the initial setup tallies. Its old search and weight tally
does not increase. A separate tally covers the measured weighted run and
the seed-access costs, with a
[fixed-height bound](OnlineReachabilityPreservers/SteinerFinWeightedReplayWork.lean#L286)
for every prefix and seed with bounded access costs.

The [complete replay with weighted early work](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1635)
shares the earlier seed decoder, late evaluator, trace normalization, and
outer union. Its prefix graphs and evaluation count agree for every input,
including exhausted seeds. The ordinary search total is no larger. The
[prefix bound](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1667)
includes the one-time key preparation and the weighted work across the
evaluated prefixes on feasible traces. It still uses the earlier search
conventions inside the weighted residual network. This replay version
leaves post-solver charge reads during rounding, request attachments,
remaining service and container operations, and bit and native costs
outside the work bound.

The [charge magnitude bound](OnlineReachabilityPreservers/SteinerWeightedChargeWork.lean#L629)
adds at most one unit per accepted cut to any starting charge. At fixed
separator fuel, the total increase is at most the fuel times the number
of requests. The [measured rounding evaluator](OnlineReachabilityPreservers/SteinerRoundingWork.lean#L1468)
accepts a charge reader that reports its work. At each paid ancestor
capacity query it counts the forest membership test, the weight and
charge reads, and the rounded capacity arithmetic. Under the stated
access bounds, the selected forest links agree with the earlier evaluator.
The two work bounds cover capacity and weight accesses and seed reads.
Tier and cutoff arithmetic, threshold comparisons, finite set assembly,
remaining search and service work, and bit and native costs remain outside
this bound.

The [finite early evaluator](OnlineReachabilityPreservers/SteinerFinWeightedReplayWork.lean#L397)
passes the weighted solver's paired charge reader directly into those
rounding trials. The metric graphs and setup tallies agree with the earlier
seeded evaluator, and the separate count now includes the rounded
capacity reads. The [complete replay comparison](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1712)
keeps all prefix graphs and evaluation counts, including the exhausted
branch. Its [feasible-prefix bound](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1737)
includes the new early rounding count.

The [forest attachment builder](OnlineReachabilityPreservers/SteinerForestAttachmentsWork.lean#L162)
takes a complete duplicate-free list of forest vertices. It scans each
row once for the source and sink leaf groups, charges the traversals for
their depth and terminal label, and forms the two exact arc unions with
the base free arcs. The
[request-list evaluator](OnlineReachabilityPreservers/SteinerForestAttachmentsWork.lean#L210)
keeps the earlier requests, including order and repetitions. It bounds
the recorded work by the number of requests times the per-request
budget, plus the empty-list charge.

The [shared enumeration](OnlineReachabilityPreservers/SteinerForestPairKeysWork.lean#L236)
returns the complete forest rows used on the way to the same ordered
pair keys. At height \(h\) there are at most \(2n(n+1)^h\) rows, with a
fixed extra setup allowance to return them. The
[prepared early evaluator](OnlineReachabilityPreservers/SteinerFinWeightedReplayWork.lean#L445)
uses these rows and the measured request builder at every evaluated
metric prefix before running the weighted solver. The
[complete comparison](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1782)
keeps the exact history replay's prefix graphs and evaluation count
for every trace. The [feasible-prefix theorem](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1806)
bounds the recorded operations with the new attachment costs.

The [measured forest query](OnlineReachabilityPreservers/SteinerForestLabelWork.lean#L49)
reads both terminal labels in one traversal of each history and then reads
the stored metric. It returns exactly the earlier value and comparison
count. The initial [weight plan](OnlineReachabilityPreservers/SteinerWeightedPlanWork.lean#L101)
shares this routine. The [metric prefix evaluator](OnlineReachabilityPreservers/SteinerDistanceTable.lean#L2099)
uses the measured values in the weighted separator and forest rounding,
with one allowance \(10h+8n^2+46\) for either kind of weight query. The
[complete comparison](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1843)
keeps the same prefix graphs and the same evaluation count as the history
replay on all traces. The
[feasible-prefix work bound](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1867)
includes these new query tallies.

The [forest route](OnlineReachabilityPreservers/SteinerForestExpansionWork.lean#L37)
reads both terminal labels, selects the exact original route using the
supplied arc list, and forms its arc set from the verified simple route.
The [standalone expansion](OnlineReachabilityPreservers/SteinerForestExpansionWork.lean#L112)
scans the supplied template rows for bought links and meters the route
selection and unions. Its graph is the expansion of the bought links
present in those rows. With a [complete template for the bought links](OnlineReachabilityPreservers/SteinerForestExpansionWork.lean#L192),
the evaluator returns the earlier expanded graph, including overlapping
routes. Its fixed-height bound uses the lengths of both supplied lists
and the cardinality of the bought graph.

The [early replay](OnlineReachabilityPreservers/SteinerEarlyReplay.lean#L629)
uses that expansion before each nonempty metric prefix check and for the
union of bought links when all checks succeed. The old reachability
checks and fallback decision agree, and the old ordinary search tally is
bounded above by its prior value. The [finite preparation](OnlineReachabilityPreservers/SteinerFinWeightedReplayWork.lean#L583)
supplies the original arc list and the already constructed forest template.
Every bought link belongs to that template. The
[complete comparison](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1904)
preserves all output graphs and evaluation counts for every input trace.
The [feasible-prefix work bound](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1928)
adds the route, union, and label work of both uses of expansion.

The [demand check](OnlineReachabilityPreservers/SteinerIntervalWork.lean#L298)
filters the original arc list for membership in the expanded graph, runs
reverse reachability on those rows, and tests the source against the
result. It computes reachability in the intersection of the supplied
arc set and the expanded graph. The [early preparation](OnlineReachabilityPreservers/SteinerDistanceTable.lean#L2293)
proves that each expanded graph is a subgraph of the supplied arcs and
uses the measured check on every nonempty metric prefix. The
[complete comparison](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1965)
keeps the same prefix graphs and evaluation count for every trace. Its
[feasible-prefix work bound](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1989)
includes arc filtering, reverse searching, and source membership for those
checks.

The [measured prefix assembly](OnlineReachabilityPreservers/SteinerEarlyReplay.lean#L802)
builds successive nonempty prefix lists by reversing the extended history,
uses the new request as the final request, and collects bought links and
validation records. It merges the bought graphs only if all checks pass.
Both branches return the same graph and ordinary search tally as the
prior prefix table. The [prepared evaluator](OnlineReachabilityPreservers/SteinerDistanceTable.lean#L2346)
shares the same metric, expansion, and validation. The
[complete comparison](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2026)
retains all graphs and evaluation counts, and its
[feasible-prefix work bound](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2050)
includes this assembly.

A standalone [capped dyadic routine](OnlineReachabilityPreservers/SteinerRoundingWork.lean#L112)
rounds a positive capacity up to a strictly greater power of two, clips
it at the tier power, and leaves zero at zero. The tier number bounds
the number of halvings. The [cutoff](OnlineReachabilityPreservers/SteinerRoundingWork.lean#L173)
uses the original ancestor minima and can share both powers within a
tier. The [standalone bound](OnlineReachabilityPreservers/SteinerRoundingWork.lean#L203)
includes generating the powers by doubling.

The [ancestor row construction](OnlineReachabilityPreservers/SteinerRoundingWork.lean#L276)
enumerates exactly the prefixes of the stored history in increasing
length. The [list minimum](OnlineReachabilityPreservers/SteinerRoundingWork.lean#L343)
returns the same capped capacity and charges enumeration, supplied
reads, and comparisons. The [cutoff from these rows](OnlineReachabilityPreservers/SteinerRoundingWork.lean#L429)
charges building the parent history and both minima. It gives the
reference cutoff when supplied the two correct powers. The
[forest trials](OnlineReachabilityPreservers/SteinerRoundingWork.lean#L1503)
now charge each gate and use these routines for the reached thresholds.
Each evaluated link and tier shares its two powers across the threshold
checks. The checked graph agrees with the previous charge-based trials.
The word bound includes the tier arithmetic, actual ancestor traversal,
and the parent arcs used as capacity keys. The seed-read bound is separate. The
[subset property](OnlineReachabilityPreservers/SteinerRoundingWork.lean#L1848)
keeps every link in the input forest.

The [prepared arithmetic evaluator](OnlineReachabilityPreservers/SteinerDistanceTable.lean#L2474)
passes the measured charge reader from the weighted separator to these
forest trials at every reached early metric. It uses the same prepared
metric, expansion, validation, and prefix assembly. The
[finite-index instance](OnlineReachabilityPreservers/SteinerFinWeightedReplayWork.lean#L805)
bounds the added word work at fixed height. The
[complete comparison](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2087)
proves exact agreement of prefix graphs and evaluation counts with the
early-history replay for every trace. The
[complete feasible-prefix bound](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2111)
includes the measured rounding.

In the [standalone list-backed trials](OnlineReachabilityPreservers/SteinerRoundingWork.lean#L1750),
a counted halving loop gives the exact tier count. The routine constructs
the trial and tier lists once and scans the supplied duplicate-free
forest links. It keeps a link if one trial selects it. Free links are
kept precisely when there is at least one trial. With a complete link
list, the graph agrees with the earlier forest trials. Seed reads have
a separate bound.
The loop and link assembly have a source-level word bound.

The [prepared metric](OnlineReachabilityPreservers/SteinerDistanceTable.lean#L2537)
uses the duplicate-free template rows for link selection and expansion.
Validation continues to scan the supplied original arcs. The
[finite evaluator](OnlineReachabilityPreservers/SteinerFinWeightedReplayWork.lean#L894)
bounds the measured work at fixed height in terms of the vertex count,
the raw arc-list length, and the demand-prefix length.
The [complete comparison](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2148)
agrees with the early-history replay on every prefix graph and the number
of evaluations for every trace. The
[feasible-prefix polynomial](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2172)
includes the trial, tier, and link assembly.

The [standalone weighted residual search](OnlineReachabilityPreservers/SteinerWeightedChargeWork.lean#L872)
uses the supplied vertex count as its search depth. It keeps the chosen
augmenting paths and computes each residual flow entry using forward and
reverse membership scans. It reuses the capacity rows for every route
search and for the terminal source-side search. When the rows contain
the reference capacity for every ordered pair and the depth equals the
vertex count, its cut decision and vertex set agree with the reference.
The word bound is polynomial in the vertex count and numeric supply.
The [weighted separator](OnlineReachabilityPreservers/SteinerWeightedChargeWork.lean#L947)
uses this search after constructing the capacity table and returns the
reference paid cut. The [weighted cover run](OnlineReachabilityPreservers/SteinerWeightedChargeWork.lean#L1018)
uses the same supplied vertex count at each separator call. It keeps the
exact charge values and chronological cut list, and bounds the run and
each charge read.

The [charge-reader comparison](OnlineReachabilityPreservers/SteinerWeightedChargeWork.lean#L1069)
shows equality of the full reader and the chronological cut list. The
[early metric](OnlineReachabilityPreservers/SteinerDistanceTable.lean#L2600)
uses the measured weighted cover before list-backed rounding. The
[finite preparation](OnlineReachabilityPreservers/SteinerFinWeightedReplayWork.lean#L989)
counts the existing forest vertex list once and uses three times its
length as the exact weighted-network depth. The
[complete comparison](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2209)
agrees with the early-history replay on every prefix graph and number
of evaluations for every trace. The
[feasible-prefix bound](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2233)
includes the setup and the measured weighted search. The trial-count
calculation still enumerates the original vertices at each reached
metric. This enumeration, later service steps, and bit and native costs
remain outside the bound.

The [late evaluator with measured thin service](OnlineReachabilityPreservers/SteinerHubRouteWork.lean#L528)
uses the rounded-list check whenever the late replay runs a thin cover.
The hub routing and thick fallback agree with the earlier evaluator.
The [combined whole-replay comparison](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2330)
preserves every graph, ordinary search tally, setup field, and evaluation
count on every trace, including decode exhaustion and unreachable requests.
The [fixed-height bound](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2389)
includes the measured weighted search and the additional thin service
work for feasible traces. The trial-count enumeration and bit and native
execution costs remain outside this bound.

The [finite trial count](OnlineReachabilityPreservers/SteinerFinWeightedReplayWork.lean#L1076)
uses measured halving on the supplied original vertex count. The
[prepared metric](OnlineReachabilityPreservers/SteinerDistanceTable.lean#L2667)
uses that same count with the same samples at each reached metric. The
[complete replay](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2421)
has identical prefix records and evaluation counts, with only the new
setup tally added to its recorded work. The [feasible-prefix bound](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2437)
adds at most \(7n+12\). This measures the trial-count calculation for
the metric, and bit and native execution costs remain outside the ledger.

The [thin parameter setup](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2477)
halves the supplied vertex and arc counts to obtain the exact thin
update cap and rounding offset. The [late comparison](OnlineReachabilityPreservers/SteinerHubRouteWork.lean#L515)
uses those same parameters and adds the supplied late cutoff to the
offset. The [complete comparison](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2520)
preserves every prefix record and evaluation count on all traces. The
[feasible-prefix bound](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2578)
adds at most \(7(n+m)+19+4(p+1)\) for the setup and reached calls.

The [binary arithmetic](OnlineReachabilityPreservers/SteinerBinaryArithmetic.lean#L45)
evaluates addition with a carry on explicit bit lists. The
[multiplication](OnlineReachabilityPreservers/SteinerBinaryArithmetic.lean#L100)
uses shifts and additions. The [length counter](OnlineReachabilityPreservers/SteinerBinaryArithmetic.lean#L165)
increments a binary word for each input bit. All three preserve decoded
values and bound the output length and recorded work. The
[thin setup evaluator](OnlineReachabilityPreservers/SteinerThinBitArithmeticWork.lean#L22)
combines these operations with a polynomial bound in the input lengths.
On canonical encodings of the two input counts, its
[refinement theorem](OnlineReachabilityPreservers/SteinerThinBitArithmeticWork.lean#L64)
matches the update cap and rounding offset used in the complete replay.
The [binary trial-count evaluator](OnlineReachabilityPreservers/SteinerEarlyBitArithmeticWork.lean#L23)
increments the binary height, squares it, multiplies it by the vertex
width, and shifts by four bits. Its exact
[reference comparison](OnlineReachabilityPreservers/SteinerEarlyBitArithmeticWork.lean#L68)
requires a canonical binary encoding of the vertex count. The height
word permits redundant high zeros. The two bounds apply to setup
calculations on supplied binary lists. Input encoding and bit and native
execution costs for the full replay remain open.

The [binary list access](OnlineReachabilityPreservers/SteinerBinaryIndexedWork.lean#L23)
reads the old cell and optionally replaces it by walking the supplied
list, with a binary zero test and decrement. The
[address calculation](OnlineReachabilityPreservers/SteinerBinaryIndexedWork.lean#L78)
computes the row-major index by binary multiplication and addition.
The [thin load table comparison](OnlineReachabilityPreservers/SteinerBinaryIndexedWork.lean#L112)
matches both the indexed read and the replacement in the list representation.
The bound includes the address arithmetic and list traversal but treats each
stored payload as one cell. Table conversion and native execution costs remain
outside this bound.

A [fixed-width increment](OnlineReachabilityPreservers/SteinerThinBitLoadWork.lean#L15)
charges the carry operations and preserves the width. It gives the decoded
successor whenever that successor fits. A
[single binary load update](OnlineReachabilityPreservers/SteinerThinBitLoadWork.lean#L65)
uses the same computed address for reading and replacement. The
[cut work bound](OnlineReachabilityPreservers/SteinerThinBitLoadWork.lean#L159)
includes the supplied list traversal and the payload increment for each cut
arc. It proves the exact change by multiplicity under a terminal load bound.
For a duplicate-free cut, the [array comparison](OnlineReachabilityPreservers/SteinerThinBitLoadWork.lean#L207)
matches every entry of the existing thin load update. The model assumes
fixed-width cells and supplied binary labels. It does not charge constructing
those encodings or run the separator or complete replay.

The thin rounding test for a sample \(s\), factor \(f\), and load \(\ell\)
is \(s < f\,2^\ell\). The [binary right shift](OnlineReachabilityPreservers/SteinerThinBitRoundingWork.lean#L27)
computes \(\lfloor s/2^\ell\rfloor\), stopping when the threshold word is empty
or the shift count is zero. The [binary comparison](OnlineReachabilityPreservers/SteinerBinaryArithmetic.lean#L332)
uses a subtraction borrow. The [rounding specification](OnlineReachabilityPreservers/SteinerThinBitRoundingWork.lean#L79)
proves the original inequality and a polynomial tally in the supplied word
lengths, including when the load represents a much larger value. This is the
arithmetic for a single row on supplied encodings.

The [decoded load read](OnlineReachabilityPreservers/SteinerBinaryIndexedWork.lean#L158)
selects the encoded cell that represents the reference entry. The
[binary threshold scan](OnlineReachabilityPreservers/SteinerThinBitScanWork.lean#L112)
reads and tests each supplied row, preserving the order and multiplicity
of passing rows. On duplicate-free arc rows the
[reference comparison](OnlineReachabilityPreservers/SteinerThinBitScanWork.lean#L144)
checks exact equality of the rounded arc sets. Its tally includes a list
walk and a binary comparison per row. The finite table and binary inputs
are supplied.

The [binary load initializer](OnlineReachabilityPreservers/SteinerThinBitInitializationWork.lean#L85)
constructs the fixed-width zero payload and all \(n^2\) row-major cells
from binary dimensions. Doubling the partial list directly follows the
[binary repetition bound](OnlineReachabilityPreservers/SteinerThinBitInitializationWork.lean#L30).
The measured work is polynomial in the count of cells, the numeric
payload width, and the lengths of both dimension words. The shared zero
payload is constructed even when there are no cells.

The [binary-label search](OnlineReachabilityPreservers/SteinerBinaryReachWork.lean#L153)
uses bit-by-bit equality on supplied encoded arcs. At any depth the output
is the exact ordered list used by the word-work search, encoded vertex by
vertex. The [Boolean demand test](OnlineReachabilityPreservers/SteinerBinaryReachWork.lean#L186)
agrees with its word-work counterpart. Given injective labels of width at
most \(w\), each sweep costs at most \(1+m(14+2(5w+8)n)\) in the
list-and-bit tally.

The [binary trial evaluator](OnlineReachabilityPreservers/SteinerThinBitServiceWork.lean#L25)
tests the demand on the passing labels at any supplied depth. Each vertex
uses one shared structural encoding, including in the query. With distinct
arc rows, the [reference comparison](OnlineReachabilityPreservers/SteinerThinBitServiceWork.lean#L79)
matches the thin replay's miss flag at depth \(n\). The tally covers the
rounding scan and the reachability check for that trial. Label construction,
load table conversion, counter representation, and the full replay remain open.

The [cut-trace evaluator](OnlineReachabilityPreservers/SteinerThinBitCutTraceWork.lean#L74)
uses the same bit table for every supplied cut and query. Each cut's arcs
are distinct. Repeated uses of an arc in different cuts are allowed.
If all initial loads plus their terminal counts fit the payload width,
every intermediate increment fits as well. Lean checks the exact flags
in order and the complete ending load table against the indexed reference.
The [empty-table entry point](OnlineReachabilityPreservers/SteinerThinBitCutTraceWork.lean#L164)
also accounts for the initial binary allocation. The work bound sums the
charges for the supplied cut arcs and trials. Producing cuts from the
input graph and integrating every phase of the replay are separate.

A [planned number of cut-and-query steps](OnlineReachabilityPreservers/SteinerThinBitCapacityPlanWork.lean#L44)
is enough to choose the fixed payload width up front. Each arc appears at
most once per cut. The width is the length of the supplied plan word,
which suffices for every trace of length at most its value. The evaluator
charges this setup and agrees with the same indexed reference.

The [binary outgoing-cut evaluator](OnlineReachabilityPreservers/SteinerBinaryResidualCutWork.lean#L98)
swaps the endpoints of the supplied residual arcs so the reverse search
finds the vertices reachable from the source. It filters the supplied
original arc list in order. At vertex-count depth, the [flow refinement](OnlineReachabilityPreservers/SteinerBinaryResidualCutWork.lean#L138)
gives the exact outgoing cut of the residual source side when the residual
list represents the signed reference flow. Distinct original arcs give
distinct cut arcs. The polynomial tally includes traversal and binary label
comparisons. The residual arc encodings are supplied.

The [signed comparison](OnlineReachabilityPreservers/SteinerBinaryFlowCutWork.lean#L28)
tests a supplied flow word against an unsigned capacity. It accepts high-zero
padding and either sign for zero. The [residual row scan](OnlineReachabilityPreservers/SteinerBinaryFlowCutWork.lean#L103)
retains exactly the encoded rows whose flow is strictly below capacity, in
input order. If the supplied table describes every ordered vertex pair,
the [composed binary flow cut](OnlineReachabilityPreservers/SteinerBinaryFlowCutWork.lean#L151)
returns the exact reference cut and charges both the table scan and the graph
search.

The [signed unit update](OnlineReachabilityPreservers/SteinerBinaryFlowAugmentWork.lean#L20)
adds or subtracts one on an encoded word, increasing its magnitude width
by at most one. It also handles both signs of zero. The [table refinement](OnlineReachabilityPreservers/SteinerBinaryFlowAugmentWork.lean#L155)
checks membership of the arc and its reverse in the supplied path, applies
the two indicators of the reference flow update, and preserves every key
and capacity word in order. Repeated path entries count once by membership.
Both directions contribute opposite updates to the same entry. The tally
includes bitwise label comparisons and arithmetic. Path selection is supplied.

The [tight-cut lemma](OnlineReachabilityPreservers/SteinerCutFlow.lean#L499)
puts the residual source side inside every separating cut whose capacity
equals the flow value. The [canonical source-side theorem](OnlineReachabilityPreservers/SteinerCutFlow.lean#L519)
shows that two stalled valid flows with the same capacities and terminals
have equal values and equal residual source sides. The [bounded separator comparison](OnlineReachabilityPreservers/SteinerCutFlow.lean#L567)
therefore obtains the exact reference response upon reaching the supply or
stalling below it, even if the underlying valid flows differ.

The [binary route search](OnlineReachabilityPreservers/SteinerBinaryPathWork.lean#L297)
tests reverse reachability in increasing depth order, then chooses the first
arc into the previous layer at each step. A returned route is simple and
shortest, and failure means the target is unreachable at the supplied depth.
The tally charges the depth tests, the searches during reconstruction, and
label comparisons on the input arc list. The source and target use the
same injective labels as the supplied arcs.

The [binary augmentation run](OnlineReachabilityPreservers/SteinerBinaryFlowRunWork.lean#L87)
builds residual arcs from the table at each step, selects a simple path,
and applies the signed update. Lean checks the validity and exact value of
the terminal flow and the absence of a residual route when supply remains.
The [zero-flow separator](OnlineReachabilityPreservers/SteinerBinaryFlowRunWork.lean#L249)
builds the initial flow, runs the augmentations and extracts the outgoing
arcs of the reference separator's exact cut. It needs a supplied unsigned
capacity row for every ordered vertex pair and the original arc labels.
The bound uses the numeric supply and controls how wide the flow magnitudes
can grow. Graph and capacity preparation and the full replay are separate.

For any nonnegative capacity table, [clipping at the augmentation supply](OnlineReachabilityPreservers/SteinerClippedFlowCut.lean#L13)
keeps the exact optional separator result. A cut returned below the supply
has no crossing capacity affected by clipping, so its source side also
matches the original residual cut. The [binary clipped power](OnlineReachabilityPreservers/SteinerBinaryClippedPowerWork.lean#L89)
computes the lesser of \(2^\ell\) and the supplied ceiling. It scans at most
the ceiling's width to build a candidate. Both its output width and the
polynomial list-and-bit tally are bounded by the supplied input widths.

The [binary interval evaluator](OnlineReachabilityPreservers/SteinerBinaryIntervalWork.lean#L138)
uses reverse search on the swapped rows to find vertices reachable from the
source. A reverse search on the original rows finds vertices that can reach
the target. The evaluator retains each original
arc whose endpoints pass both tests. At vertex-count depth it agrees exactly
with ordered filtering by the reference demand interval, including repeated
rows. The charged work covers both searches and the arc scan on the supplied
encoded graph.

The [binary capacity evaluator](OnlineReachabilityPreservers/SteinerBinaryThinCapacityWork.lean#L87)
scans supplied keys, reads the exact indexed load on each active arc,
and uses the clipped power of two for its capacity. Inactive keys get
zero without a load read. The result preserves key order and multiplicity.
The tally includes binary label membership, the indexed lookup and the
clipped arithmetic on the supplied load and ceiling words.

The [prepared binary thin separator](OnlineReachabilityPreservers/SteinerBinaryThinCutWork.lean#L49)
agrees with the reference thin test on whether it finds a cut and on the
outgoing arcs of the returned cut. Intersecting the source side with the
demand interval keeps the same outgoing arcs because every interval arc
has both endpoints inside. The [entry from encoded graph rows](OnlineReachabilityPreservers/SteinerBinaryThinCutWork.lean#L141)
also computes the interval. Both entries take the pair keys, count words,
and current binary load cells as inputs. The tally includes the capacity
construction and the bounded solver.

The [binary thin loop](OnlineReachabilityPreservers/SteinerBinaryThinLoopWork.lean#L148)
builds the demand interval once. Every successful separator call updates
the current loads on exactly the outgoing cut. The final table and update
count agree with the reference fractional loop at the supplied fuel. The
fixed payload must fit the reference load cap, and the supplied original
arc list must be distinct. For one feasible demand, the charge includes
the interval setup, every update and at most one terminal cut test.

The [chronological binary fractional run](OnlineReachabilityPreservers/SteinerBinaryThinCoverWork.lean#L42)
passes the updated table directly to the next feasible demand and uses the
reference fuel for each request. The total load increases by at least the
number of successful updates. Its [entry from zero](OnlineReachabilityPreservers/SteinerBinaryThinCoverWork.lean#L155)
chooses a payload one bit wider than the supplied ceiling word and agrees
with the reference fractional cover. With \(m\) arcs, at most
\(m(1+\lfloor\log_2 m\rfloor)\) successful updates occur across the whole
trace, with zero updates at \(m=0\). The graph and demand encodings, pair
enumeration, and numeric controls are supplied.

The [binary rounded demand step](OnlineReachabilityPreservers/SteinerBinaryThinDemandWork.lean#L77)
runs the fractional loop at the paper's fuel bound and returns its updated
encoded loads and cut count. It then scans the supplied threshold rows once
and tests reachability in the resulting graph. The returned encoded arc list
and miss flag agree with the reference rounded trial. The work bound charges
the interval setup, fractional cuts, final cut probe, threshold scan, and
rounded reachability test.

The [rounded trace](OnlineReachabilityPreservers/SteinerBinaryThinRoundRunWork.lean#L47)
passes the same updated table across arrivals and carries the latest rounded
list. Its cumulative miss flag is [equivalent to a failed prefix](OnlineReachabilityPreservers/SteinerBinaryThinRoundRunWork.lean#L160).
When the supplied threshold rows represent a fixed thin sample, the
[binary entry from zero](OnlineReachabilityPreservers/SteinerBinaryThinRoundRunWork.lean#L198)
returns the original graph if any prefix misses, the last rounded graph
if all prefixes succeed, and the empty graph for an empty request list.
It allocates its own table, and its work bound substitutes the global load
budget for the total number of successful cuts. The sample rows and other
binary inputs are supplied.

The [binary threshold cache](OnlineReachabilityPreservers/SteinerBinaryThinSampleWork.lean#L110)
reads one stored threshold per arc in the supplied shared index order. It
represents each value at the specified width and gives each arc its encoded
labels. The [entry using the indexed sample](OnlineReachabilityPreservers/SteinerBinaryThinSampleWork.lean#L197)
runs the same binary thin phase with the constructed cache. It uses the arc
count word's width for the thresholds and skips preparation on an empty
request list. On a successful fixed-budget decode, the [sample projection](OnlineReachabilityPreservers/SteinerBinaryThinSampleWork.lean#L247)
identifies the indexed thresholds with the thin sample of that same packet.
The accounting includes the scan of the arc count word, charges parity and
halving at the reserved operand width, and uses the supplied endpoint
label-read allowance and indexed read model.

The [finite-input entry](OnlineReachabilityPreservers/SteinerBinaryFinInputWork.lean#L174)
reads the label width from the word for the vertex count and encodes the
typed graph and demand lists in their given order. The [pair builder](OnlineReachabilityPreservers/SteinerBinaryFinInputWork.lean#L130)
encodes each entry of the supplied vertex list and pairs the resulting
words, including self-pairs and any repeated vertices. When the vertex
list is complete, every ordered pair has a key. The refinement retains
the same thin graph and charges the encodings and generated pair rows.

The [typed thin graph](OnlineReachabilityPreservers/SteinerBinaryFinOutputWork.lean#L155)
decodes both labels of each selected row and assembles the finite arc set.
The [structural length bound](OnlineReachabilityPreservers/SteinerBinaryFinOutputWork.lean#L127)
counts the input arc list and the threshold cache. There is one threshold
per original arc, so the decoding and insertion costs are bounded using
the input arc list length. The result is the exact reference thin graph
on the same feasible trace and fixed sample, including the empty and
full-graph fallback cases.

The [late evaluator using binary thin rounds](OnlineReachabilityPreservers/SteinerBinaryLateWork.lean#L27)
uses the same chronological classification and hub routes as the earlier
list evaluator. An unhit thick request still selects the original graph.
Otherwise it unions the hub arcs and the typed binary graph for the selected
thin trace. The result agrees with the assembled algorithm at early cutoff
zero for the supplied hubs, seed index and feasible suffix. The bound adds
the existing hub word work to the thin work at the supplied widths and
counts. The [prepared-control entry](OnlineReachabilityPreservers/SteinerBinaryLateControlsWork.lean#L88)
computes those sizes and the rounding factor from the graph counts and
late threshold. Its [control calculation](OnlineReachabilityPreservers/SteinerBinaryLateControlsWork.lean#L35)
proves the exact binary widths and fuel and adds the setup charge to the
same mixed work model. The [full seeded replay with binary late rounds](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2687)
passes the shared decoded arc index and thin sample directly to this
evaluator at each evaluated prefix. It keeps the measured early phase and
returns the [exact fixed-budget prefix graphs](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2796)
on feasible traces with the reference evaluation count. Decoder exhaustion
uses the same fallback as the reference. The [work comparison](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2702)
bounds the added binary late charge at each feasible evaluation. The
[full tally](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2808)
includes the earlier measured work, all retained setup counters, and
the binary late allowance within this mixed model.

The [binary weighted charge update](OnlineReachabilityPreservers/SteinerBinaryWeightedLoadWork.lean#L44)
stores the current remainder, doubling factor, and weighted numerator for
one positive-cost edge. It adds the factor to the numerator and resets the
remainder and doubles the factor at the cost boundary. The two additions
and comparison have a bound in their input word widths. The [capped weighted capacity](OnlineReachabilityPreservers/SteinerBinaryWeightedCapacityWork.lean#L129)
reuses the numerator, increments a binary candidate and its stored cost
multiple, and stops when the multiple reaches the numerator or the flow
supply is reached. It returns the exact clipped rounded capacity. The
bound is polynomial in the numeric supply and the input word widths. The
[weighted cut](OnlineReachabilityPreservers/SteinerBinaryWeightedCutWork.lean#L155)
checks each supplied pair against the free arcs for the request. Free arcs
have full supply, paid arcs use their clipped capacity, and absent pairs
have zero capacity. On the complete represented pair table, the binary
separator returns the exact optional reference paid cut. The bound charges
table preparation and the bounded flow computation. Pair states and free
rows are supplied. The [paid table advance](OnlineReachabilityPreservers/SteinerBinaryWeightedUpdateWork.lean#L138)
adds one reference charge to each selected paid state. Membership makes
repeated cut entries count once. The update keeps the ordered labels and
proves the new word widths and a work bound for this one cut. The [weighted loop](OnlineReachabilityPreservers/SteinerBinaryWeightedLoopWork.lean#L62)
uses each updated table for the next separator call. With the supplied
fuel for a single demand, the final charges and chronological paid cuts
agree with the reference. Its bound includes each cut and update and the
final probe when reached. The [weighted trace](OnlineReachabilityPreservers/SteinerBinaryWeightedTraceWork.lean#L78)
extends the comparison to the entire chronological weighted network run.
Each request uses its own supplied free arcs, and the next request starts
from the preceding updated paid table. The theorem verifies the full cut
history, final paid charges, and work including the append operations.
The [binary initializer](OnlineReachabilityPreservers/SteinerBinaryWeightedInitWork.lean#L44)
uses metered cost and label readers on distinct supplied pair keys. It
builds the zero-charge table with the same order and accumulates the
paid cost. When the keys are complete, the [exact total](OnlineReachabilityPreservers/SteinerBinaryWeightedInitWork.lean#L134)
gives the [reference scale, its binary word, and the fuel](OnlineReachabilityPreservers/SteinerBinaryWeightedInitWork.lean#L170).
The work includes paid cost encodings, word additions, and the supplied
reader fees. The [weighted run from zero](OnlineReachabilityPreservers/SteinerBinaryWeightedRunWork.lean#L97)
already combines the initial table, computed controls, and chronological
trace with the [metered encoding of typed requests](OnlineReachabilityPreservers/SteinerBinaryWeightedRunWork.lean#L52).
It returns the reference cut history and paid charges on complete
distinct keys with the supplied positive-cost and injective label readers.
The [finite metric forest label reader](OnlineReachabilityPreservers/SteinerBinaryForestLabelsWork.lean#L64)
computes its shared history block and binary width once. Each label uses
the network tag, original root, side, and history rank. The proof gives
injectivity, the exact vertex count, and the recorded ranking and encoding
work.
The [binary fractional forest run](OnlineReachabilityPreservers/SteinerBinaryForestFractionalWork.lean#L154)
combines these labels with complete typed pair keys. It reads each paid
cost from the metered hop reader and builds each request's source and sink
leaf attachments. Given the exact prepared paid and free classes, the
result agrees with the reference fractional forest run. Its work bound
includes the measured requests, keys, labels, and weighted trace. The
[binary capacity reader](OnlineReachabilityPreservers/SteinerBinaryWeightedUnitsWork.lean#L87)
charges its encoded key scan, clipped capacity calculation, and numeric
decode. The [clipping lemma for ancestor cutoffs](OnlineReachabilityPreservers/SteinerBinaryWeightedUnitsWork.lean#L130)
shows that clipping the units at a limit of at least the tier power
leaves the dyadic tier, ancestor minima, and cutoff unchanged.
The [stored-row rounding evaluator](OnlineReachabilityPreservers/SteinerRoundingWork.lean#L1871)
can use any metered capacity reader that preserves these cutoffs.
The [binary forest rounding theorem](OnlineReachabilityPreservers/SteinerBinaryForestRoundingWork.lean#L101)
instantiates this with the supplied binary paid states and the forest's
permanent zero-cost arcs. For fixed trial samples it returns the exact
reference rounded forest with separate word and seed-access tallies.
The [composed binary forest run](OnlineReachabilityPreservers/SteinerBinaryForestRunWork.lean#L46)
applies this evaluator to the final paid states of the binary fractional
trace. It encodes the supplied permanent free rows once for rounding.
With exact typed classes, complete forest links, and the metered hop and
seed readers, the result equals the reference rounded forest for the
supplied trials. The bound includes the fractional run, the setup and
rounding fees, and a separate seed-access tally.
The [weighted plan pass](OnlineReachabilityPreservers/SteinerWeightedPlanWork.lean#L116)
also returns the distinct raw zero-cost rows of the existing classification.
The [early prefix evaluator](OnlineReachabilityPreservers/SteinerBinaryEarlyWork.lean#L46)
uses the combined binary forest call on each reached prefix and reuses the
original validation, expansion, and fallback. Its bound counts the early
metric work separately and includes the fractional work, rounding and
seed reads. The [finite preparation](OnlineReachabilityPreservers/SteinerFinWeightedReplayWork.lean#L1179)
computes the exact metered hop table, paid and free classes, and trial
count. With the supplied metered samples it returns the reference early
graph and bounds the plan and trial-count preparation charge.
The [seeded replay with both binary solvers](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2887)
passes one decoded seed to the early weighted forest and late thin solver.
The [prefix theorem](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2935)
proves the exact reference graph at every feasible prefix and the same
number of evaluations as the earlier metered replay. On seed exhaustion,
the shared fallback supplies all prefix graphs.
The [uniform early allowance](OnlineReachabilityPreservers/SteinerBinaryEarlyBoundWork.lean#L133)
uses the typed forest dimensions, supplied reader bounds, and demand
count. It bounds the charged early metric work without evaluating the
fractional solver. The [full replay tally](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L3087)
includes the legacy validation and expansion counts, metered setup,
seed decoding and indexing, and both phases on every reached prefix.
The bound covers all recorded fields in the mixed model. A native
execution bound remains open.
The [early size allowance](OnlineReachabilityPreservers/SteinerBinaryEarlyPolynomialWork.lean#L87)
bounds the label and row counts, scale, fuel, and trial count using the
original vertex count and forest height. With this allowance, the
[input-size replay theorem](OnlineReachabilityPreservers/SteinerBinaryReplaySizeWork.lean#L26)
gives the exact feasible prefix graphs and evaluation count together
with a common bound on all eight work fields. The bound uses only the
vertex and arc counts, raw arc list length, height, and number of requests.
The [fixed-height growth theorem](OnlineReachabilityPreservers/SteinerBinaryReplayAsymptotics.lean#L159)
bounds this size allowance by a constant times a fixed power of the sum
of the input sizes plus one. The [combined theorem](OnlineReachabilityPreservers/SteinerBinaryReplayAsymptotics.lean#L171)
bounds the recorded work and the fixed supply of fair bits by one such
polynomial. Its degree and leading bound depend only on the forest height.
On every feasible trace, the [last executable graph](OnlineReachabilityPreservers/SteinerBinaryReplayCompetitive.lean#L22)
equals the fixed-budget reference for every supplied bit word, including
on exhaustion.
It [serves all feasible requests](OnlineReachabilityPreservers/SteinerBinaryReplayCompetitive.lean#L36)
and [keeps every edge bought on an earlier prefix](OnlineReachabilityPreservers/SteinerBinaryReplayCompetitive.lean#L46).
The [finite-seed expected bound](OnlineReachabilityPreservers/SteinerBinaryReplayCompetitive.lean#L56)
applies directly to this executable graph. It uses one fixed feasible trace
and any serving offline subgraph.
The [metered final-result entry](OnlineReachabilityPreservers/SteinerBinaryReplayResultWork.lean#L50)
counts the input arcs once and folds over the replay records to find the
last graph and sum the recorded search fields. Its
[graph and tally theorem](OnlineReachabilityPreservers/SteinerBinaryReplayResultWork.lean#L68)
includes both passes. The [expected bound](OnlineReachabilityPreservers/SteinerBinaryReplayResultWork.lean#L111)
and the [fixed-height work and bit bound](OnlineReachabilityPreservers/SteinerBinaryReplayAsymptotics.lean#L194)
apply to this entry point.

The [arrival operation](OnlineReachabilityPreservers/SteinerBinaryArrivals.lean#L39)
receives the next request and stores the history in reverse order. It
reconstructs only the seen prefix and reuses the original graph and the
same sampled bit word. Its [exact total](OnlineReachabilityPreservers/SteinerBinaryArrivals.lean#L92)
includes empty initialization, every prefix replay, and the history scan.
The [combined Theorem 21 statement](OnlineReachabilityPreservers/SteinerBinaryArrivals.lean#L188)
uses one fixed height for each positive \(\varepsilon\). For every feasible
trace and supplied word, the graph serves the trace, extends all prior
outputs for that word, and the total recorded work plus the prescribed
bit count is polynomial. On every fixed feasible trace the final graph
has the same expected competitive bound under the uniform finite bit law.
The [exact budget computation](OnlineReachabilityPreservers/SteinerBinaryReplayResultWork.lean#L128)
uses the metered hop table, forest, weighted scale and decoder sizes before
any bits or demands are needed. The
[array sampler](OnlineReachabilityPreservers/SteinerBinaryReplayResultWork.lean#L218)
consumes exactly the required number of bits from any starting stream
position. The
[arrival refinement](OnlineReachabilityPreservers/SteinerBinaryArrivals.lean#L265)
keeps the original graph and history and charges the initialization once.
The [sampled arrival theorem](OnlineReachabilityPreservers/SteinerBinaryArrivals.lean#L329)
uses the fair-stream law to recover the same competitive expectation. Its
fixed-height polynomial includes seed length computation, draws, array
construction and the earlier mixed word and binary-list tally. The
[raw arc-list theorem](OnlineReachabilityPreservers/SteinerRawArcRows.lean)
also constructs the graph from possibly repeated arc rows. It keeps the
same bit count, prefix inclusion, and competitive expectation, with the
graph construction included in the polynomial tally. Equality of finite
vertex labels is a primitive in that tally. A native execution bound remains open.

The binary arc preparation encodes both endpoints of each raw row
once at the bit length of the vertex count. The deduplication pass
compares stored bit lists and returns the raw list's finite edge set,
including for empty lists and repeated arcs. The tally counts width
computation, encoding, bit comparisons, and extraction of retained
rows. Its cubic bound uses the vertex and raw-row counts.
[Exact graph preparation](OnlineReachabilityPreservers/SteinerRawArcRows.lean#L354) · [Cubic bound](OnlineReachabilityPreservers/SteinerRawArcRows.lean#L397).

The sampled binary-arc entry uses this preparation before drawing its
single word. For each supplied stream and trace it returns the exact
same graph, history, and stream position as the certified raw-arc
solver. Its recorded work exchanges the preparation charges. On every
fixed feasible trace, each supplied stream yields preserved reachability
and an increasing sequence of edge sets as requests arrive. The solver
reads exactly the prescribed number of stream bits. The same expected
competitive bound holds under the fair-stream measure. The fixed-height
recorded polynomial includes the bit comparisons at intake.
[Exact replay](OnlineReachabilityPreservers/SteinerBinaryRawOnline.lean#L39) · [Theorem 21 with binary arc preparation](OnlineReachabilityPreservers/SteinerBinaryRawOnline.lean#L89).

For a list of pairs of binary endpoint words, decoding succeeds exactly
when every word denotes a finite vertex label. The returned endpoint
values agree in order and multiplicity, including empty lists and
repeated pairs. If each word fits the declared width, the decoding tally is at
most the existing per-row bound at that width, including rejected input.
[Exact endpoint values](OnlineReachabilityPreservers/SteinerBinaryInputDecoding.lean#L9)
· [Acceptance condition](OnlineReachabilityPreservers/SteinerBinaryInputDecoding.lean#L60)
· [Work bound at the supplied width](OnlineReachabilityPreservers/SteinerBinaryInputDecoding.lean#L90).

The guarded decoder scans both word lengths per row and stops at the first
over-width row, before numerical decoding. It accepts the lists whose words fit the width
and whose endpoint values are below the finite vertex count. It preserves
the input endpoint values, row order and multiplicity. Its recorded-work bound adds
the scan at the actual raw bit count and the maximum decoding charge at
the supplied width, including for malformed input.
[Width check](OnlineReachabilityPreservers/SteinerBinaryInputGuard.lean#L29)
· [Exact decoded rows](OnlineReachabilityPreservers/SteinerBinaryInputGuard.lean#L63)
· [Acceptance condition](OnlineReachabilityPreservers/SteinerBinaryInputGuard.lean#L84)
· [Combined work bound](OnlineReachabilityPreservers/SteinerBinaryInputGuard.lean#L104).

The binary demand wrapper checks only the current pair of endpoint words.
A valid pair produces exactly the existing typed solver step for the decoded
demand, the saved history and the sampled seed. A malformed pair is rejected.
The input charge is bounded separately by the one-row width and decoding
budgets, including the actual supplied bit count on rejection.
[Exact step](OnlineReachabilityPreservers/SteinerBinaryArrivalWordInput.lean#L22)
· [Acceptance condition](OnlineReachabilityPreservers/SteinerBinaryArrivalWordInput.lean#L63)
· [Agreement on encoded demands](OnlineReachabilityPreservers/SteinerBinaryArrivalWordInput.lean#L83)
· [Recorded input charge](OnlineReachabilityPreservers/SteinerBinaryArrivalWordInput.lean#L96).

The binary session initializer validates the fixed graph's arc words before
sampling. A rejected graph preserves the initial stream position. On a
successful decode, the initializer prepares exactly the decoded graph,
reads its prescribed seed length and stores the existing empty-prefix
state. Each subsequent binary arrival reuses that graph and seed. A
separate tally accounts for decoding and graph preparation at setup and
for one decoded demand per arrival.
[Binary initialization](OnlineReachabilityPreservers/SteinerBinaryWordSession.lean#L20)
· [Rejection and stream position](OnlineReachabilityPreservers/SteinerBinaryWordSession.lean#L33)
· [Exact accepted initialization](OnlineReachabilityPreservers/SteinerBinaryWordSession.lean#L45)
· [Exact seed length](OnlineReachabilityPreservers/SteinerBinaryWordSession.lean#L60)
· [Stored-session step](OnlineReachabilityPreservers/SteinerBinaryWordSession.lean#L85)
· [Per-arrival input charge](OnlineReachabilityPreservers/SteinerBinaryWordSession.lean#L99).

A binary session reads one demand row at a time and stops at the first
rejection. At a width that can encode every vertex label, the final
session on a canonically encoded trace agrees exactly with the typed
arrival fold and stores the same fixed graph and seed. The guarded graph decoder preserves order and multiplicity on
canonical input. The extra trace input tally is bounded by the total count
of supplied bits and a per-row allowance at the advertised width, including
when replay stops early.
[Trace replay](OnlineReachabilityPreservers/SteinerBinaryWordTrace.lean#L9)
· [Exact typed fold](OnlineReachabilityPreservers/SteinerBinaryWordTrace.lean#L23)
· [Canonical graph decoding](OnlineReachabilityPreservers/SteinerBinaryWordTrace.lean#L42)
· [Input work for arbitrary traces](OnlineReachabilityPreservers/SteinerBinaryWordTrace.lean#L69).

The guarded word entry validates the fixed graph before drawing a seed,
then decodes each demand only when that row is served. For all arc and
demand encodings that pass the width and range checks, the final state
has exactly the graph and history of the typed solver on the decoded
inputs, with the same seed-stream position. The result keeps the graph
preparation charge outside the solver state as part of the input tally.
[Decoded trace agreement](OnlineReachabilityPreservers/SteinerBinaryWordOnline.lean#L9)
· [Guarded word entry](OnlineReachabilityPreservers/SteinerBinaryWordOnline.lean#L52)
· [Graph rejection](OnlineReachabilityPreservers/SteinerBinaryWordOnline.lean#L63)
· [Accepted result refinement](OnlineReachabilityPreservers/SteinerBinaryWordOnline.lean#L74).

For accepted binary graph rows and every fixed feasible binary demand
trace, the sampled word solver reads the prescribed seed, records every
request in order, preserves reachability and keeps the outputs increasing
across accepted prefixes. Against every serving offline subgraph it has
the same expected \(O(n^{3/5+\varepsilon})\) competitive bound. The sum of
recorded input and solver work is polynomial in the vertex count, row
counts, declared width and total supplied bit count. The input bound is
cubic in those dimensions and also covers rejection. A native execution
bound remains open.
[Input work bound](OnlineReachabilityPreservers/SteinerBinaryWordGuarantee.lean#L18)
· [Cubic input allowance](OnlineReachabilityPreservers/SteinerBinaryWordGuarantee.lean#L52)
· [Guarded binary Theorem 21](OnlineReachabilityPreservers/SteinerBinaryWordGuarantee.lean#L126).

The variable-length entry derives its allowances from the fixed graph
and one demand pair at a time. It accepts every encoding whose endpoint
values belong to the fixed vertex type. An invalid graph keeps the
initial seed-stream position, and a demand trace stops at its first
out-of-range value. Accepted traces refine the typed graph, history,
solver tally and stream position exactly. Polynomial total recorded work
now depends on vertex and row counts and the actual supplied endpoint
bits. The separate cubic input bound also applies to rejection. For fixed
\(\varepsilon\) and feasible decoded traces, accepted-prefix inclusion holds
for each shared stream. The competitive bound is an expectation under
the fair bit-stream measure.
A native execution-time bound remains open.
[Single demand semantics](OnlineReachabilityPreservers/SteinerBinaryVariableWordInput.lean#L58)
· [Variable-length entry](OnlineReachabilityPreservers/SteinerBinaryVariableWordInput.lean#L175)
· [Graph rejection](OnlineReachabilityPreservers/SteinerBinaryVariableWordInput.lean#L186)
· [Refinement](OnlineReachabilityPreservers/SteinerBinaryVariableWordInput.lean#L207)
· [Cubic input work](OnlineReachabilityPreservers/SteinerBinaryVariableWordInput.lean#L270)
· [Variable-length Theorem 21](OnlineReachabilityPreservers/SteinerBinaryVariableWordInput.lean#L355).

For typed requests, the final graph depends on the fixed graph and seed
and the first non-self occurrences in arrival order. The compact session
implements that rule online and agrees with the full-history replay
on any fixed feasible trace under the same seed. It retains at most one
entry per possible pair and bypasses replay on self or repeated requests.
After a feasible prefix with a duplicate-free arc list, recorded work per
feasible arrival is polynomial in the vertex count at fixed height.
Theorem 21 keeps exact prefix inclusion and the uniform finite seed
expectation. A native execution-time bound remains open.
[Dependence on first occurrences](OnlineReachabilityPreservers/SteinerBinaryCompactArrivals.lean#L53)
· [Per-prefix refinement](OnlineReachabilityPreservers/SteinerBinaryCompactArrivals.lean#L126)
· [Bounded history](OnlineReachabilityPreservers/SteinerBinaryCompactArrivals.lean#L147)
· [Per-arrival recorded work](OnlineReachabilityPreservers/SteinerBinaryCompactArrivals.lean#L160)
· [Compact-arrival Theorem 21](OnlineReachabilityPreservers/SteinerBinaryCompactArrivals.lean#L245).

The compact variable-length session deduplicates the decoded graph's
arc list at startup. Graph rejection consumes no bits. Acceptance
retains the exact graph, seed slice, and stream position of the earlier
entry. The empty-history graph agrees with compact initialization for
the new arc list. Each accepted request uses the compact step at its
decoded endpoint values, including padded representations of a pair
already seen. With a duplicate-free feasible stored history, at fixed
height the recorded cost of a reachable decoded pair depends
polynomially on the vertex count and the lengths of that pair's supplied
words. The request bound also covers out-of-range words. At fixed height,
a separate polynomial in the vertex count, supplied arc-row count and
actual endpoint bit count covers startup, including rejection. Native
execution time remains open.
[Startup with the original seed](OnlineReachabilityPreservers/SteinerBinaryCompactWordSession.lean#L103)
· [Exact variable-length request semantics](OnlineReachabilityPreservers/SteinerBinaryCompactWordSession.lean#L67)
· [Recorded startup bound](OnlineReachabilityPreservers/SteinerBinaryCompactWordSession.lean#L210)
· [Recorded request bound](OnlineReachabilityPreservers/SteinerBinaryCompactWordSession.lean#L169).

On accepted feasible words, the complete compact trace agrees pointwise
with the previous word solver's graph. The stream stops at the same
seed offset. The stored distinct non-self history is in reverse arrival
order and has length at most \(n^2\). One polynomial bounds recorded
startup and request work in the vertex count, both row counts and the actual bit
count at fixed height. Theorem 21 keeps accepted-prefix inclusion for
each fixed stream and the expected rate against any serving offline
subgraph under the fair bit stream.
[Whole-trace decoding](OnlineReachabilityPreservers/SteinerBinaryCompactWordOnline.lean#L29)
· [Seedwise graph refinement](OnlineReachabilityPreservers/SteinerBinaryCompactWordOnline.lean#L78)
· [Recorded total bound](OnlineReachabilityPreservers/SteinerBinaryCompactWordOnline.lean#L239)
· [Compact encoded Theorem 21](OnlineReachabilityPreservers/SteinerBinaryCompactWordOnline.lean#L295).

Instantiate the same compact solver with a finite sequential bit tape.
Each draw reads one list cell. The sampler keeps the exact seed tally
and reports exhaustion for a tape shorter than the seed budget.
Invalid graph words give the ordinary graph rejection and leave the tape
intact. With valid graph words and sufficient bits, the finite run agrees
with the stream run whose prefix is on the tape, including entry and
service tallies. The unused bits remain available. This holds for any
demand words. For accepted feasible traces the compact history and
polynomial recorded work bounds transfer, independent of the suffix.
[Tape source](OnlineReachabilityPreservers/SteinerBinarySeedTape.lean#L9)
· [Sampler](OnlineReachabilityPreservers/SteinerBinarySeedTape.lean#L46)
· [Tape exhaustion](OnlineReachabilityPreservers/SteinerBinarySeedTape.lean#L135)
· [Exact run](OnlineReachabilityPreservers/SteinerBinarySeedTape.lean#L153)
· [Polynomial recorded work](OnlineReachabilityPreservers/SteinerBinarySeedTape.lean#L187).

The [integer magnitude bounds](OnlineReachabilityPreservers/SteinerIntegerBounds.lean)
control the signed flow entries by the augmentation supply, the thin
capacities by twice the number of arcs, and the weighted capacities by
four times the forest scale plus one. The [weighted numerator bound](OnlineReachabilityPreservers/SteinerRoundedCapacities.lean)
is \((4S+1)c\) with positive scale \(S\), cost \(c\), and the checked load cap.
The forest threshold operands are
polynomial in the scale. The thin rounding comparison on each feasible
prefix has an operand bound of \((5n+4)\cdot 2|E|\).

## Appendix dependencies

At half cutoff four, [the replacement cleaning proof](OnlineReachabilityPreservers/FrozenHalfFourCleaning.lean)
works for arbitrary indexed simple paths with positive budgets and mass
\(M\) at least both budgets. It retains at least \(M/5000\) of that mass
within both budgets and all four original-average caps. This applies to
the unrestricted indexed maximum. Length clipping handles small total
excess. Pruning handles large mass on overlong paths when the excess is
large. Otherwise each conflict
between width pieces requires two incidences at its late central corner.
The [conflict accounting](OnlineReachabilityPreservers/FrozenHalfFourConflicts.lean)
uses one outgoing target per source and two deletion colors. It keeps
either enough mass on the overlong pieces alone or at least \(337M/650\)
within the whole path budget. The exact vertex width controls the last
trim. A low-mass construction covers \(M\le8\max(n,p)\).

The [literal simple-path set version](OnlineReachabilityPreservers/FrozenDistinctCleaning.lean)
uses a separate maximum over distinct nonempty rows whenever those positive exact
input counts are feasible. Each bridge corner occurs on two distinct
rows, so an unused vertex could be added to one row without creating a
bridge. A maximizing set therefore reaches both original budgets.
At input mean length above four, the lower length cap and half-two
exclusion force a distinct nonempty output. At smaller means, the
disjoint-path, singleton, and bipartite constructions give the literal
witness directly. The half-four and full-six results retain \(M/5000\).
The full result at cutoffs three to five retains \(M/119\), and the all-size
full family theorem retains \(M/40\). Each guarantee uses both original
budgets and all four original-average caps.

At full cutoff six, [the unrestricted indexed cleaning result](OnlineReachabilityPreservers/FrozenFullSixCleaning.lean)
retains at least \(M/5000\) of the maximizing mass with both budgets and
all four original caps. At the moderate overlong mass, a conflict joins
a later central piece incidence to an opposite-step incidence. Full-three
exclusion gives both directed degree bounds. Choosing an independent set
covers the conflicts by its complement, so the retained family satisfies
the contiguous full-six lift. The path-budget proof retains either
\(3M/10\) on the heavy pieces alone or \(13M/25\) within the mixed path budget
before the final vertex trim and peel. The other mass branches are shared
with the half-four proof.
[Conflict classification](OnlineReachabilityPreservers/FrozenFullSixConflicts.lean)
· [Path-budget selection](OnlineReachabilityPreservers/FrozenFullSixRepair.lean).

At half cutoff five, [the unique-intersection theorem](OnlineReachabilityPreservers/HalfFiveProjection.lean)
retains at least \(M/16\). When paths can meet more than once,
[bounded length excess](OnlineReachabilityPreservers/HalfFiveCleaning.lean)
retains at least \(M/5000\) if clipping at \(\lfloor4M/p\rfloor\)
removes at most \(7M/50\) incidences. Each theorem assumes simple
half-five-free input with positive budgets and incidence mass \(M\) at
least both budgets. Its witness preserves half-five exclusion, fits both
budgets, and meets all four original-average caps. The bounded-excess proof
uses a two-color deletion on overfull vertices and charges peeling to the
chosen vertex support.

For half-five-free input with the same budget and mass assumptions,
[overlong subfamily pruning](OnlineReachabilityPreservers/FrozenOverlongPaths.lean#L274)
gives \(M/216\) if the paths longer than the original length cap carry at
least \(2M/3\) incidences.
[The excess variant](OnlineReachabilityPreservers/FrozenOverlongPaths.lean#L299)
gives \(M/2000\) when the overlong paths have mass at least \(7M/12\)
and total length excess at least \(7M/15\). If opposite-intersection pruning
keeps at least \(13M/24\), [trimming both supports](OnlineReachabilityPreservers/FrozenMatchedPartners.lean#L650)
keeps \(M/288\). The latter threshold follows from at least \(M/12\)
nonempty paths or at most \(11M/24\) opposite links. All these witnesses
preserve half-five exclusion within both budgets and all four frozen caps.

[Path-cut repair](OnlineReachabilityPreservers/HalfFivePathCleaning.lean)
at half cutoff five uses the same input assumptions. Let \(E\) count
distinct participating piece incidences where one comparison crosses a
length-width cut and its reverse stays within a piece of the other parent.
Let \(U\) be the total original degree excess above \(\lfloor4M/n\rfloor\).
The \(M/5000\) guarantee holds if \(20E\le3M\) or
\(100U+50E\le43M\). It preserves half-five exclusion and all four caps
within both original budgets.

[A single deletion for both splits](OnlineReachabilityPreservers/HalfFiveSharedWidthCleaning.lean)
uses the union of the path-cut conflict incidences and the incidences
at vertices above the original degree width. Under the same input
assumptions, a union of size at most \(4M/5\) gives a witness of mass
at least \(M/5000\) with both budgets and all four original-average caps.
[Weighted row selection](OnlineReachabilityPreservers/HalfFiveWeightedWidthCleaning.lean)
extends the same conclusion to \(22M/25\). It selects the row support by
the sum of the mass retained in both deletion colors and splits vertices
after retaining those rows.
[Counting the copies at overfull original vertices](OnlineReachabilityPreservers/HalfFiveHeavyWidthCleaning.lean)
gives the same conclusion if those vertices carry at least 71 percent of
the original mass. This condition uses the original degree width
\(\lfloor4M/n\rfloor\) and places no restriction on the conflict count.
Two small supports can also suffice together. Write \(D=\lfloor4M/n\rfloor\)
and \(L=\lfloor4M/p\rfloor\). A rectangle on vertices \(A\) and rows \(B\)
of mass \(S\) gives a starting-average witness if \(D|A|\le M\),
\(L|B|\le M\), and \(31M+1280(D|A|+L|B|)\le8640S\).
The witness keeps at least \(M/640\) and both original budgets. For the
sets of overdegree vertices and overlength rows it suffices that their
intersection carries at least \(57M/320\).
[Rectangle with actual support charges](OnlineReachabilityPreservers/HalfFiveDenseRectangle.lean#L42)
· [Overfull support intersection](OnlineReachabilityPreservers/HalfFiveDenseRectangle.lean#L213).

For each choice of \(a,b\in[0,1/4]\) with \(a+b\le7/15\), every simple
half-five input with positive budgets and \(M\ge\max(n,p)\) has a witness
within both budgets of mass in \([M/930,M]\). It satisfies the upper caps
\(4M/n\) and \(4M/p\) and the lower caps \(aM/n\) and \(bM/p\).
Equal coefficients \(7/30\) and the
asymmetric pairs \((1/4,13/60)\) and \((13/60,1/4)\) are included. For
literal input the witness is distinct and nonempty. The printed pair of
lower coefficients \((1/4,1/4)\) remains open without further hypotheses.
[Indexed lower-cap tradeoff](OnlineReachabilityPreservers/HalfFiveStartingLowerCaps.lean#L30)
· [Literal lower-cap tradeoff](OnlineReachabilityPreservers/HalfFiveStartingLowerCaps.lean#L49).

Let \(t_q=\lfloor(M-1)/(4q)\rfloor\) for \(q=n,p\). An integer meets the
exact quarter-average lower cap at budget \(q\) precisely when it exceeds
\(t_q\). If \(15(nt_n+pt_p)<7M\), the lower coefficient choice can force
both integer thresholds. Thus, under the same positive-budget and density
assumptions, simple half-five input has a witness of mass in \([M/930,M]\)
with the exact four starting-average caps and both budgets. The literal
version gives distinct nonempty rows.
[Integer removal charge](OnlineReachabilityPreservers/HalfFiveRoundedLowerCaps.lean#L12)
· [Indexed criterion](OnlineReachabilityPreservers/HalfFiveRoundedLowerCaps.lean#L85)
· [Literal criterion](OnlineReachabilityPreservers/HalfFiveRoundedLowerCaps.lean#L104).
With actual opposite-pruned mass \(K\), a sharper test is
\(C+\lfloor(M-1)/r\rfloor<K-4K^2/(31M)\) for \(r\ge8\) and
\(C\) the integer removal charge above. It yields both budgets,
all four exact starting caps, and retention \(M/r\) at half
cutoff five. The same indexed and literal results hold at half
cutoff six with full-three exclusion. For \(r=930\), the coarser
criterion permits equality in \(15C\le7M\) since \(M/930\) strictly
exceeds \(\lfloor(M-1)/930\rfloor\).
[Coarse charge](OnlineReachabilityPreservers/RoundedCropCaps.lean#L18)
· [Indexed half-five](OnlineReachabilityPreservers/RoundedCropCaps.lean#L155)
· [Literal half-five](OnlineReachabilityPreservers/RoundedCropCaps.lean#L171)
· [Indexed half-six](OnlineReachabilityPreservers/RoundedCropCaps.lean#L190)
· [Literal half-six](OnlineReachabilityPreservers/RoundedCropCaps.lean#L207).

[Actual degree-cut cleaning after clipping](OnlineReachabilityPreservers/HalfFiveDegreeCutCleaning.lean)
gives \(M/5000\) and all four original caps within both original
budgets if \(A+2(M-K)\le23M/25\), where \(K\) is the clipped mass and
\(A\) is the number of distinct copied incidences in a reversed comparison
across an actual degree cut of the clipped rows.
[The joint repair in degree-first order](OnlineReachabilityPreservers/HalfFiveDegreeFirstCleaning.lean)
counts distinct affected incidences of both actual cuts. The path
comparisons are formed on the copied vertices. For the same simple
half-five-free input with mass at least both positive budgets, union
size at most \(81M/100\) gives \(M/5000\), both budgets, and all four
original-average caps.
[The cover formulation](OnlineReachabilityPreservers/HalfFiveDegreeFirstCleaning.lean)
gives the same guarantee whenever at most \(37M/100\) raw incidences
cover every actual degree-first conflict edge. An edge increases the
original arrival label, and each source has at most one later target.
[Matching and cover equality](OnlineReachabilityPreservers/CutConflictMatching.lean)
reduces that cover condition to a bound of \(37M/100\) on the size of
each matching of the actual conflicts. The witness has the same mass
guarantee, budgets, and original-average caps.
[A retained rectangle formulation](OnlineReachabilityPreservers/DegreeFirstRectangleCleaning.lean)
uses at most \(n\) degree copies and \(p\) path pieces. If every
matching within its raw incidences fits its incidence count after the
two actual support charges and \(M/5000\) are set aside, it gives the
same half-five conclusion.
[The supported comparison version](OnlineReachabilityPreservers/DegreeFirstSupportedCleaning.lean)
counts only edges with both witness incidences in that rectangle and
uses the same inequality and conclusion.
The deletion can hit either endpoint or either witness incidence of
a supported comparison. The repaired rectangle must have no supported
conflict. One witness deletion meets the budget on a checked rectangle
whose endpoint matching has size two and exceeds that budget.
[Deletion theorem](OnlineReachabilityPreservers/DegreeFirstSupportedCleaning.lean#L171) · [Checked example](OnlineReachabilityPreservers/VertexSplitAudit.lean#L476).
Original-average half-five cleaning for general inputs remains open.

For Lemmas 23 and 39, the [contiguous six-bridge lift](OnlineReachabilityPreservers/CyclicSplits.lean)
uses the original relative order of pieces in addition to the mirrored-cut
condition. It assumes full exclusion through size three. With unique
intersections and mass at least both positive input counts, the
[checked width-block cleaning](OnlineReachabilityPreservers/ContiguousSixCleaning.lean)
preserves full exclusion through size six with both original budgets and
all four frozen caps, retaining at least one sixteenth of the input mass.
With unique intersections, full exclusion through size three also
suffices for both width splits at half cutoff six. If the first two
projected steps end at the river's terminal, they form a full
three-bridge with the river.
The indexed and literal starting-average witnesses keep both budgets
and at least \(M/16\). For arbitrary intersections, pruning before
rectangle selection yields output-average witnesses retaining at least
\(M/392\) in the indexed convention and \(M/7056\) in the literal
convention. These still assume both half-six and full-three exclusion
on the original family.
[Projection](OnlineReachabilityPreservers/HalfSixProjection.lean#L21)
· [Both splits](OnlineReachabilityPreservers/HalfSixProjection.lean#L62)
· [Indexed starting caps](OnlineReachabilityPreservers/HalfSixProjection.lean#L113)
· [Indexed output caps](OnlineReachabilityPreservers/HalfSixProjection.lean#L130)
· [Literal output caps](OnlineReachabilityPreservers/HalfSixProjection.lean#L154)
· [Literal starting caps](OnlineReachabilityPreservers/HalfSixProjection.lean#L173).
For arbitrary intersections and the same two input exclusions, both
starting-average upper caps hold with either exact lower cap, provided
the other lower coefficient is at most \(13/60\). More generally the
coefficients can be in \([0,1/4]\) with sum at most \(7/15\).
Both conventions meet the original budgets and retain at least
\(M/930\). If the opposite-pruned mass is at least \(13M/24\), the
same crop and peel give all four exact caps and at least \(M/288\).
[Indexed lower fractions](OnlineReachabilityPreservers/HalfSixStartingLowerCaps.lean#L30)
· [Literal lower fractions](OnlineReachabilityPreservers/HalfSixStartingLowerCaps.lean#L49)
· [Indexed exact caps](OnlineReachabilityPreservers/HalfSixStartingLowerCaps.lean#L71)
· [Literal exact caps](OnlineReachabilityPreservers/HalfSixStartingLowerCaps.lean#L98).
The general cyclic existence claim at half cutoff six remains open.

At any cutoff \(k\) and in either mode, assume simple input with the
selected bridge exclusion and incidence girth greater than \(k\). A bridge in the width
blocks projects to a closed trail in the bipartite graph on rows and
vertices because each original incidence has one retained copy. If
any interior label repeats, the two circuits on its two sides together
have length at most \(2k\), although each contains a cycle longer than
\(k\). Thus row and vertex labels project distinctly, and the half
mode keeps strict last-arc arrival by the parent order. On positive
budgets and dense input, the indexed and literal versions give both
budgets, all four original caps and \(M/16\). With caps at the witness's
own averages they give \(M/392\) indexed or \(M/7056\) literal.
The literal results use cutoff at least two and distinct nonempty
simple paths.
[Incidence projection](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L509)
· [Width splits](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L688)
· [Indexed starting caps](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L757)
· [Literal starting caps](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L804)
· [Indexed output caps](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L843)
· [Literal output caps](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L870).

The same guarantees follow when two edge-disjoint incidence cycles
through any one label always have combined length greater than \(2k\).
The two closed trails from a projection collision each contain a
cycle through the repeated label, with disjoint edges and within the
same combined length. Conversely, appending two edge-disjoint cycles
of combined length at most \(2k\) gives a closed trail with a repeated
interior label. Under this condition both original budgets, the bridge
cutoff and the same four types of witnesses hold even when some cycles
are short. A graph with one cycle, for example, satisfies the condition
at every cutoff.
[Trail equivalence](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L124)
· [Widths](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L679)
· [Indexed starting caps](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L743)
· [Literal starting caps](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L790)
· [Indexed output caps](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L817)
· [Literal output caps](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L854).

The combined bound \(2k\) includes imbalanced lengths. A simple
ten-row example on twenty vertex labels excludes every half-bridge.
The original widths are four and eight. Splitting creates a half-six
bridge at the common terminal of two incidence cycles of lengths
four and eight. Every incidence cycle of length at most six uses
one specified edge, so two edge-disjoint cycles each of length at
most six are absent even though the split fails.
[Input and bridge](OnlineReachabilityPreservers/IncidenceCyclePairAudit.lean#L76)
· [Combined length](OnlineReachabilityPreservers/IncidenceCyclePairAudit.lean#L134)
· [Separate length check](OnlineReachabilityPreservers/IncidenceCyclePairAudit.lean#L206).

Only duplicated occupied labels need the cycle-pair test for the
projection. In the standard consecutive splits, distinct occupied
pieces from one row imply its length exceeds the path width. Distinct
occupied copies of one vertex imply its degree exceeds the degree
width. Impose the test at those original labels. Simple input with
either bridge exclusion at cutoff \(k\) then has a witness with the
same exclusion, all four starting caps, both positive budgets, and
at least \(M/16\) of the mass when \(M\) is at least both budgets.
The distinct nonempty literal version uses \(k\ge2\).
[Pointwise condition](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L16)
· [Occupied-label projection](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L465)
· [Width tests](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L617)
· [Indexed starting caps](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L722)
· [Literal starting caps](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L768).

In full mode the degree split already preserves every input bridge
cutoff. The subsequent split needs the pointwise condition only at
overlong rows of the actual degree-copied incidence graph. When the
test holds there, both original budgets, all four starting caps,
and retention \(M/16\) follow. Testing the overlong rows in the original
graph also suffices, because the copied graph projects injectively
on its edges. The pointwise test transfers under this projection.
Both tests give indexed and distinct nonempty literal witnesses.
[Copied-row width theorem](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L943)
· [Indexed copied-row criterion](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L985)
· [Literal copied-row criterion](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L1003)
· [Indexed original-row criterion](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L1024)
· [Literal original-row criterion](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L1041).

For output-average caps, the linear-mass construction covers input
of mass at most \(392\max(n,p)\). Otherwise select a rectangle with
at least \(M/49\) incidences in at most one quarter of each support.
Both widths computed from its mass are at least sixteen. Thus only
original rows of length above sixteen need the cycle-pair test in
either mode. In half mode the test also applies to vertices of degree
above sixteen. With simple input and both positive budgets and density
assumptions, the indexed and literal witnesses have the same cutoff,
both budgets, and all four own-average caps, retaining \(M/392\) or
\(M/7056\), respectively. Literal input and output are distinct and
nonempty, with cutoff at least two.
[Rectangle rule](OnlineReachabilityPreservers/LocalAverageCleaning.lean#L305)
· [Indexed output caps](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L1061)
· [Literal output caps](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L1121).

The splitting rule can instead group neighbors by component after
deleting their common incidence label. Two copies of that label in one
component of the split graph would admit a simple connecting path. The
portion between the first exit and the first return to the original
label projects to a walk in the deleted graph. The grouping rule forces
the return to be to the first copy, violating simplicity. All the labels
of a bridge lie in a single incidence component, so the projected
bridge preserves all distinct labels. A monotone parent order preserves
the last-arc comparison in half mode.
[Injectivity in a component](OnlineReachabilityPreservers/IncidenceComponentCleaning.lean#L86)
· [Bridge exclusion](OnlineReachabilityPreservers/IncidenceComponentCleaning.lean#L113).

After the original-width degree split, check that the neighbors of
each copied row in any one component after deleting that row fit its
original path width \(\lfloor4M/p\rfloor\). Pack the groups whole, with
at most one piece of half width or less per row. The packing keeps all
degrees and incidences. With admissible degree copies, simple input and
mass at least both positive budgets, the cleaned witness keeps the
original cutoff, both budgets and four starting-average caps. The indexed
mass is at least \(M/4\). For cutoff at least two the literal theorem
also assumes exclusion on the original distinct nonempty simple rows.
Its output has distinct nonempty simple rows and retains \(M/8\).
In full mode the standard degree split is admissible, and the component
sizes can also be bounded in the original graph because copying cannot
increase them.
[Packing](OnlineReachabilityPreservers/IncidenceComponentCleaning.lean#L253)
· [Indexed witness](OnlineReachabilityPreservers/IncidenceComponentCleaning.lean#L310)
· [Full witness after copying](OnlineReachabilityPreservers/IncidenceComponentCleaning.lean#L328)
· [Size under projection](OnlineReachabilityPreservers/IncidenceComponentCleaning.lean#L182)
· [Full witness from original groups](OnlineReachabilityPreservers/IncidenceComponentCleaning.lean#L342)
· [Literal witness](OnlineReachabilityPreservers/IncidenceComponentCleaning.lean#L363).

The nine-vertex, nine-row example has three nonempty rows
\([0,1,2,3,4,5]\), \([5,0]\), and \([4,1]\). It excludes every full
bridge and has mass ten, giving both original widths equal to four.
After degree copying, two edge-disjoint incidence four-cycles share
the overlong first row. The consecutive pieces allow the river
\(4\to1\) and the detour \(4\to5\to0\to1\), a full four-bridge.
Grouping the neighbors after deleting the first row allows the pieces
\([0,1,4,5]\) and \([2,3]\). They preserve both bridge exclusions at
every cutoff. All neighbor groups fit, so the indexed full cleaner
has the original budgets and all four starting-average caps, and
retains at least \(M/4\) at every cutoff.
[Original exclusion](OnlineReachabilityPreservers/IncidenceComponentAudit.lean#L107)
· [Widths](OnlineReachabilityPreservers/IncidenceComponentAudit.lean#L118)
· [Copied graph's cycles](OnlineReachabilityPreservers/IncidenceComponentAudit.lean#L189)
· [New bridge](OnlineReachabilityPreservers/IncidenceComponentAudit.lean#L159)
· [Grouped exclusion](OnlineReachabilityPreservers/IncidenceComponentAudit.lean#L114)
· [Group-size bound](OnlineReachabilityPreservers/IncidenceComponentAudit.lean#L208)
· [Frozen witness](OnlineReachabilityPreservers/IncidenceComponentAudit.lean#L223).

The incidence transpose lists incident rows at each original vertex.
Swapping the two sides maps incidence edges exactly. After deleting
an original vertex, group its incident rows by component and pack those
groups within the original degree width. Each original vertex has at
most one copy whose degree is at most half the width. The projection
recovers every original row in order and the grouping preserves both
bridge exclusions through the selected cutoff.
[Incidence membership](OnlineReachabilityPreservers/IncidenceDegreeComponentCleaning.lean#L18)
· [Deleted-vertex group](OnlineReachabilityPreservers/IncidenceDegreeComponentCleaning.lean#L35)
· [Grouped degree copies](OnlineReachabilityPreservers/IncidenceDegreeComponentCleaning.lean#L43).

Check both kinds of groups in the original incidence graph, using
\(\lfloor 4M/n\rfloor\) on the vertex side and \(\lfloor 4M/p\rfloor\)
on the row side. Copying vertices preserves every row and cannot enlarge
its deleted-row groups. Pack the copied rows with the second width.
For each side the threshold profile bounds the restriction loss by
\(M/8\), and peeling to the two lower caps costs at most \(M/2\).
For admissible simple input on positive budgets with \(M\) at least both,
the indexed witness retains at least \(M/4\) with both budgets, all four
starting-average caps, and the original cutoff in either mode. At
cutoff at least two, the literal theorem takes and gives distinct
nonempty simple rows and retains at least \(M/8\).
[Indexed frozen witness](OnlineReachabilityPreservers/IncidenceDegreeComponentCleaning.lean#L225)
· [Literal frozen witness](OnlineReachabilityPreservers/IncidenceDegreeComponentCleaning.lean#L243).

In the twenty-incidence mixed-cycle example, every original row has
length two. The only vertex of degree above two is the terminal of the
new half-six bridge under standard degree copying. Delete this vertex
and color the remaining graph by a function constant on each edge. At
most two of the terminal's incident rows have any one color. This
bounds every deleted-vertex or deleted-row neighbor group by two.
The group-based degree copies have width four and preserve the original
rows and admissibility at any chosen half cutoff. Using the original
path width eight, the same input gives an indexed frozen witness with
both budgets, all four starting-average caps and at least \(M/4\) at
every half cutoff.
[Standard split obstruction](OnlineReachabilityPreservers/IncidenceCyclePairAudit.lean#L76)
· [Group-size certificate](OnlineReachabilityPreservers/IncidenceDegreeComponentAudit.lean#L59)
· [Grouped degree copies](OnlineReachabilityPreservers/IncidenceDegreeComponentAudit.lean#L82)
· [Frozen half witness](OnlineReachabilityPreservers/IncidenceDegreeComponentAudit.lean#L95).

The group-size conditions can be certified after deleting incidences.
Keep sublists of total mass \(K\ge2M/3\), where \(M\) is the original
mass of the simple admissible family. Keep both original widths and
test the neighbor group sizes in the retained incidence graph. The
quadratic bounds on the two trims, each at most \(K^2/(8M)\), guarantee
at least \(5M/9\) before enforcing the lower caps. Thus the cleaner
keeps \(M/18\) or more, the selected cutoff, both original budgets and
all four starting-average caps. In the literal theorem with cutoff at
least two, the original and output rows are distinct, nonempty and simple.
[Fixed-mass group trims](OnlineReachabilityPreservers/IncidenceDegreeComponentCleaning.lean#L176)
· [Trim bound at two thirds](OnlineReachabilityPreservers/ShortReturnOverflow.lean#L126)
· [Indexed restriction](OnlineReachabilityPreservers/IncidenceComponentRestriction.lean#L13)
· [Literal restriction](OnlineReachabilityPreservers/IncidenceComponentRestriction.lean#L39).

A bridge of size at most \(k\) traces a closed incidence walk of length
at most \(2k\) through all its labels. Any two visited labels are joined
by a walk of length at most \(k\), using the shorter portion of the
closed walk. If they are distinct copies of one original label, take a
simple path of that length or shorter and stop at the first positive
return to the original label. Removing its first and last edges leaves
a projected walk of length at most \(k-2\) that avoids the common label.
Forcing its original neighbor incidences into one copy excludes this
collision. All corners, arc labels and the river label then project
injectively. Preserving incidences makes the projected walks valid.
Preserving comparisons and parent arrival order transports the chosen
bridge exclusion through the selected cutoff.
[Bridge's closed walk](OnlineReachabilityPreservers/IncidenceGirthCleaning.lean#L310)
· [Half-length walk](OnlineReachabilityPreservers/ShortIncidenceProjection.lean#L13)
· [First-return bound](OnlineReachabilityPreservers/IncidenceComponentCleaning.lean#L29)
· [Projection in either mode](OnlineReachabilityPreservers/ShortIncidenceProjection.lean#L56).

Within a row, join each pair of its neighbors that connects by a walk
of at most \(k-2\) edges after deleting the row. The connected groups of
this graph fit inside the corresponding deletion components. Each
group must fit in the original path width. Packing whole groups
preserves all incidences, degrees and the chosen cutoff. Each original
row gives at most one piece of half width or less.
For simple inputs of mass at least both positive budgets and admissible
degree copies, the resulting indexed frozen witness retains \(M/4\)
or more with both budgets and all four starting-average caps. The
literal theorem also uses original admissibility with distinct nonempty
simple input and output at cutoff at least two, retaining \(M/8\) or more.
In full mode, checking the groups before degree copying also suffices.
[Short-link group inclusion](OnlineReachabilityPreservers/ShortIncidenceRowPacking.lean#L49)
· [Size under copying](OnlineReachabilityPreservers/ShortIncidenceRowPacking.lean#L73)
· [Packing](OnlineReachabilityPreservers/ShortIncidenceRowPacking.lean#L109)
· [Indexed witness](OnlineReachabilityPreservers/ShortIncidenceRowPacking.lean#L166)
· [Original-group full witness](OnlineReachabilityPreservers/ShortIncidenceRowPacking.lean#L198)
· [Literal witness](OnlineReachabilityPreservers/ShortIncidenceRowPacking.lean#L220).

The transpose carries a short connection through the graph with a
vertex deleted to a connection of the same length with that transposed
row deleted. Use these links to group incident rows for each vertex
copy. The two group-size tests use the original graph, since the
path-side group sizes cannot grow under copying. After packing, each
original label has at most one copy or piece at most half its original
width. The same two quadratic trims and original lower
caps give an indexed \(M/4\) witness or a literal \(M/8\) witness,
under the original admissibility, width and density conditions.
Both budgets, all four starting-average caps and the selected cutoff
hold in either mode. The literal theorem takes and gives distinct
nonempty simple rows at cutoff at least two.
[Transposed groups](OnlineReachabilityPreservers/ShortIncidenceDegreePacking.lean#L13)
· [Grouped degree copies](OnlineReachabilityPreservers/ShortIncidenceDegreePacking.lean#L21)
· [Fixed starting mass](OnlineReachabilityPreservers/ShortIncidenceDegreePacking.lean#L89)
· [Profile trim](OnlineReachabilityPreservers/IncidenceDegreeComponentCleaning.lean#L111)
· [Indexed witness](OnlineReachabilityPreservers/ShortIncidenceDegreePacking.lean#L139)
· [Literal witness](OnlineReachabilityPreservers/ShortIncidenceDegreePacking.lean#L157).

Enumerate each incidence in both directions from the input lists and
remove arcs touching a given label. Backward search of depth \(r\)
then decides whether a walk of length at most \(r\) avoids the
removed label, given a starting label distinct from it.
The neighbor graph built from these searches computes the same
short-link groups as the walk definition. For whole deletion
groups, a simple path has fewer edges than the total number of
incidence labels, which gives a sufficient search depth. The search
collects only the neighbors of the deleted label. Degree grouping uses
the transpose.
[Incidence arc enumeration](OnlineReachabilityPreservers/IncidenceConnectionSearch.lean#L19)
· [Exact bounded search](OnlineReachabilityPreservers/IncidenceConnectionSearch.lean#L60)
· [Short-link groups](OnlineReachabilityPreservers/IncidenceConnectionSearch.lean#L117)
· [Whole deletion groups](OnlineReachabilityPreservers/IncidenceConnectionSearch.lean#L129).

In a family with nine vertices and eighteen indexed rows, the long row
has vertices \(0,\ldots,5\). Two rows reverse its first and last triples.
A corridor between the ends of those rows joins all six of the long
row's neighbors after the long row is deleted. Its original path width
is four. The kernel checks that every radius-two group has size at most
three and that the original family excludes full bridges through four.
The original degree width is eight and the degree groups fit there.
The indexed full witness at cutoff four has both budgets, all four
starting-average caps and at least a quarter of the starting mass.
[Widths](OnlineReachabilityPreservers/ShortIncidenceRowAudit.lean#L16)
· [Full-four exclusion](OnlineReachabilityPreservers/ShortIncidenceRowAudit.lean#L31)
· [Whole deletion group](OnlineReachabilityPreservers/ShortIncidenceRowAudit.lean#L50)
· [Radius-two groups](OnlineReachabilityPreservers/ShortIncidenceRowAudit.lean#L61)
· [Frozen witness](OnlineReachabilityPreservers/ShortIncidenceRowAudit.lean#L88).

The size-seven counterexample below
applies to the printed midpoint split. The factor-four block split before trimming and peeling also creates
a full size-seven bridge in the dense branch on a simple input with unique
intersections, all-size full exclusion, and zero pruning loss.
[Dense width-block counterexample](OnlineReachabilityPreservers/FrozenWidthSplitAudit.lean#L539).

On that same input, only the padded four-vertex row splits across width
blocks. A tested return's endpoints lie among its four consecutive
core positions because no other row contains any padding vertex.
The parent span is at most three, so the short-span cover gives a
frozen \(M/27\) witness at every full cutoff \(k\ge7\). The original
budgets and all four original caps hold.
[Span bound](OnlineReachabilityPreservers/FrozenWidthSplitAudit.lean#L599)
· [Dense input repaired](OnlineReachabilityPreservers/FrozenWidthSplitAudit.lean#L651).

Through full cutoff seven, disjoint contiguous pieces preserve the
exclusion when one-step reversals stay on one piece and there is no
crossed two-step return through two distinct other parents. For a
seven-bridge, disjointness, original parallel-step exclusion and the
one-step condition rule out a shared parent at cyclic distance one or
two. A repeat at distance three either gives an original bridge of size three or four,
or supplies a two-step return across the reversed pieces. In the
existing seven-vertex example the one-step condition holds, and the
steps \(3\to4\to0\) cross the split of the original row \((0,1,2,3)\)
against its order.
[Two-step return test](OnlineReachabilityPreservers/CyclicSplits.lean#L336) · [Seven-bridge lift](OnlineReachabilityPreservers/CyclicSplits.lean#L383) · [Preservation through seven](OnlineReachabilityPreservers/CyclicSplits.lean#L506) · [Two-step return in the example](OnlineReachabilityPreservers/UniqueSplitAudit.lean#L92) · [One-step condition in the example](OnlineReachabilityPreservers/UniqueSplitAudit.lean#L101).

Under the same one-step and two-step conditions, disjoint sublists
may interleave. Only the order of the two gap corners in a common
parent is needed. If both intervening steps are arcs, that order either
gives a full three-bridge or a forbidden two-step return. If one is the
river, either order gives a full three-bridge. The lift assumes full
three-exclusion of the parents, and it preserves any full cutoff up to
seven given the corresponding original exclusion. A graph of retained
comparisons can certify the absence of returns with radius two.
In particular, the test on the actual pieces after the degree and path
width splits gives an indexed frozen \(M/16\) witness through full cutoff
seven for simple input of mass \(M\) at least both positive budgets.
It keeps both budgets and all four original-average caps.
[Lift with interleaving](OnlineReachabilityPreservers/CyclicSplits.lean#L659) · [Full preservation](OnlineReachabilityPreservers/CyclicSplits.lean#L694) · [Graph certificate](OnlineReachabilityPreservers/FullSevenWidthCleaning.lean#L11) · [Width-cut application](OnlineReachabilityPreservers/FullSevenWidthCleaning.lean#L39) · [Frozen witness](OnlineReachabilityPreservers/FullSevenWidthCleaning.lean#L66).

The full cutoff eight extension adds a three-step condition. After
the previous tests exclude repeated parents at cyclic distances one,
two and three, any remaining repeated pair has opposite slots. One
of the two gaps avoids the river. Its three arc parents are distinct
from each other and from the repeated parent. A matching comparison
in that parent gives a full four-bridge. An opposite comparison gives
a three-step return across the pieces. Ruling out these returns gives
full preservation at the same cutoff for any full cutoff through eight.
[Three-step return condition](OnlineReachabilityPreservers/CyclicSplits.lean#L720) · [Size-eight parent lift](OnlineReachabilityPreservers/CyclicSplits.lean#L751) · [Preservation through eight](OnlineReachabilityPreservers/CyclicSplits.lean#L818).

An eight-vertex audit shows a disjoint order-preserving split
that passes the radius-two test and creates a full eight-bridge. The seven
original rows are simple with unique intersections and exclude all
full bridges. The only row longer than the original mean of \(16/7\)
has length four. Its midpoint split covers the original rows. The return
\(1\to2\to3\to4\) crosses the split. A finite search proves
original exclusion by ruling out
every alternative route with distinct rows at the bounded length forced
by the number of row labels.
[Simple rows and covering split](OnlineReachabilityPreservers/FullEightSplitAudit.lean#L50) · [Original full exclusion](OnlineReachabilityPreservers/FullEightSplitAudit.lean#L34) · [Radius-two test](OnlineReachabilityPreservers/FullEightSplitAudit.lean#L65) · [New bridge](OnlineReachabilityPreservers/FullEightSplitAudit.lean#L84) · [Finite search certificate](OnlineReachabilityPreservers/RainbowListSearch.lean#L53).

At any full cutoff \(k\ge7\), the shortened return bound is
\(k-5\). For a bridge of size \(s\ge8\), exclude repeated pairs at
cyclic distances one through three. Among the remaining pairs with
the same parent, choose the smallest linear gap with the river last.
The slot index difference is at most \(s-4\). Its \(s-5\) or fewer interior
steps are forward comparisons on distinct other parents. The order
of the two corners in the repeated parent determines either a
shorter full bridge or a forbidden crossed return. This projects
every bridge through the chosen cutoff. A passing test on the
actual standard degree and path pieces gives an indexed or feasible
literal witness of at least \(M/16\) with both original budgets and
all four frozen caps. The input rows are simple and exclude full
bridges through \(k\), and the mass reaches both positive budgets.
[Crossed return predicate](OnlineReachabilityPreservers/CyclicSplits.lean#L876) · [Projection at the original cutoff](OnlineReachabilityPreservers/CyclicSplits.lean#L1003) · [Standard width test](OnlineReachabilityPreservers/FullReturnRadius.lean#L40) · [Indexed witness](OnlineReachabilityPreservers/FullReturnRadius.lean#L67) · [Literal witness](OnlineReachabilityPreservers/FullReturnRadius.lean#L89).

For a fixed split into simple pieces, a set of labeled incidences covers
all short crossed returns by meeting each return's start or end incidence
on the parent's pieces or either labeled endpoint of a step in the original
pieces. This is equivalent to the absence of those returns after deleting the
set. The comparison between the return endpoints in the pre-split
parent stays fixed. When the split is disjoint and order preserving and
the original family excludes full bridges through \(k\ge7\), applying
this test with radius \(k-5\) preserves that exclusion on the retained pieces.
[Incidence cover](OnlineReachabilityPreservers/FullReturnIncidenceCover.lean#L17)
· [Exact deletion criterion for crossed returns](OnlineReachabilityPreservers/FullReturnIncidenceCover.lean#L30)
· [Preservation at the original cutoff](OnlineReachabilityPreservers/FullReturnIncidenceCover.lean#L63).

Assume simple input excluding full bridges through \(k\ge7\), with mass
at least both positive budgets. At the original factor-four widths,
choose vertex and piece labels fitting those budgets. The quadratic
loss bounds leave at least \(5M/6\) incidences in their rectangle before
erasure. A cover of all crossed returns of at most \(k-5\) steps in the
original pieces, of size at most \(5M/16\), leaves at least \(25M/48\)
incidences in the chosen rectangle. Peeling pays at most \(M/2\) and
gives full exclusion through the original cutoff, retention of at least
\(M/48\), both original budgets and all four original-average caps. The
cover condition is needed when \(M>8\max(n,p)\).
The literal witness has distinct nonempty rows for feasible literal input.
[Rectangle mass](OnlineReachabilityPreservers/FrozenQuadraticTrimming.lean#L426)
· [Cover budget](OnlineReachabilityPreservers/FrozenFullReturnCover.lean#L52)
· [Indexed frozen witness](OnlineReachabilityPreservers/FrozenFullReturnCover.lean#L64)
· [Literal frozen witness](OnlineReachabilityPreservers/FrozenFullReturnCover.lean#L144).

A cover can be chosen after selecting vertex labels \(A\) and piece labels
\(B\) within the original budgets. Test returns only on the retained
rectangle, with parent comparisons on the degree-copied rows before the
path split. Let \(R\) count its original incidences and let \(S\) cover all
its crossed returns of at most \(k-5\) steps. If the positive integer \(r\) satisfies
\(M/r+M|A|/(4n)+M|B|/(4p)+|S|\le R\), the witness keeps at least \(M/r\).
For simple input excluding full bridges through \(k\ge7\) with mass at
least both positive budgets, this gives the same cutoff, both budgets and
all four original-average caps. For feasible literal distinct nonempty
input, \(r\ge8\) yields a distinct nonempty witness with the same bound.
[Rectangle restriction](OnlineReachabilityPreservers/FrozenFullReturnSupportedCover.lean#L13)
· [Supported cover and cost](OnlineReachabilityPreservers/FrozenFullReturnSupportedCover.lean#L32)
· [Indexed witness](OnlineReachabilityPreservers/FrozenFullReturnSupportedCover.lean#L49)
· [Literal witness](OnlineReachabilityPreservers/FrozenFullReturnSupportedCover.lean#L150).

When both original averages are at least eight, rounding the widths
leaves capacity at least \(31M/8\) in each dimension. The two quadratic
charges then give a rectangle of at least \(27M/31\) incidences within
both original budgets. For \(M>8\max(n,p)\), a cover of all crossed
returns of at most \(k-5\) steps in the original pieces can cost up to
\(M/3\). The retained rectangle pays at most \(M/2\) for peeling and
still gives a frozen witness of mass at least \(M/27\). The low-mass
branch needs no cover bound. For simple input excluding full bridges
through \(k\ge7\) with mass at least both positive budgets, both the
indexed and feasible literal versions preserve the cutoff, budgets and
four original-average caps.
[Dense rectangle bound](OnlineReachabilityPreservers/FrozenQuadraticTrimming.lean#L443)
· [One-third cover condition](OnlineReachabilityPreservers/FrozenFullReturnSupportedCover.lean#L167)
· [Indexed witness](OnlineReachabilityPreservers/FrozenFullReturnSupportedCover.lean#L179)
· [Literal witness](OnlineReachabilityPreservers/FrozenFullReturnSupportedCover.lean#L218).

With the standard copied rows and path width \(L=\lfloor4M/p\rfloor\),
a crossed return whose endpoints have distance at most \(b\) along its
parent starts within the first \(b\) positions of the later block.
Erasing those positions in all noninitial blocks costs at most
\(b\sum_i \lfloor|\pi_i|/L\rfloor\). For simple input excluding full
bridges through \(k\ge7\), assume positive budgets and \(M\ge\max(n,p)\).
When \(M>8\max(n,p)\), require every tested return of at most \(k-5\)
steps to have parent span at most \(\lfloor L/3\rfloor\).
The boundary erasure then supplies a cover of size at most \(M/3\).
The low-mass case needs no span premise. The indexed and feasible literal
witnesses retain at least \(M/27\) with both original budgets, all four
original caps and the same cutoff.
[Boundary cost](OnlineReachabilityPreservers/FullReturnBoundaryCover.lean#L30)
· [Endpoint test](OnlineReachabilityPreservers/FullReturnBoundaryCover.lean#L76)
· [Cover from the span test](OnlineReachabilityPreservers/FullReturnBoundaryCover.lean#L122)
· [Indexed witness](OnlineReachabilityPreservers/FullReturnBoundaryCover.lean#L179)
· [Literal witness](OnlineReachabilityPreservers/FullReturnBoundaryCover.lean#L192).

The same width-boundary erasure also repairs half-bridge exclusion.
In the actual comparison graph of the width pieces, test walks from a
later position to an earlier position in another block of the same
parent, within \(\max(0,k-3)\) steps.
For simple half-free input through \(k\ge2\), assume positive budgets
and \(M\ge\max(n,p)\). When \(M>8\max(n,p)\), require the standard degree
copies to exclude half-bridges through \(k\) and all the tested returns
to span at most \(\lfloor L/8\rfloor\) positions of their copied parent.
Erasing the boundary marks then costs at most \(M/8\), and the original
arrival order permits a frozen \(M/32\) witness at the same cutoff.
Both budgets and all four original caps hold for the indexed and feasible
literal versions. The low-mass branch needs neither test.
[Width-walk span test](OnlineReachabilityPreservers/HalfReturnBoundaryCover.lean#L24)
· [Returns after erasure](OnlineReachabilityPreservers/HalfReturnBoundaryCover.lean#L60)
· [Half-bridge preservation](OnlineReachabilityPreservers/HalfReturnBoundaryCover.lean#L94)
· [Indexed witness](OnlineReachabilityPreservers/HalfReturnBoundaryCover.lean#L119)
· [Literal witness](OnlineReachabilityPreservers/HalfReturnBoundaryCover.lean#L188).

For half exclusion, both tests can be confined to the width pieces
inside a selected rectangle after erasure. Keep the original degree
copies and width labels. Reconstruct each parent as the ordered sublist
of copied vertices that survive in its own pieces. Test backward returns
to an earlier degree copy using comparisons in these reconstructed
parents, including comparisons between different pieces of one parent.
Test backward returns across width pieces on the retained comparison
graph, using the original copied parent's order at the endpoints.
Both tests use radius \(\max(0,k-3)\). The half-bridge projection then
preserves the original cutoff on the retained pieces.

For simple input excluding half-bridges through \(k\), with mass \(M\)
at least both positive budgets, let \(R\) be the original width mass
inside supports \(A,B\) and let \(S\) be the certified erased incidences.
If the two tests pass and
\(M/r+M|A|/(4n)+M|B|/(4p)+|S|\le R\) for a positive integer \(r\),
the witness retains at least \(M/r\) with both original budgets and
all four original-average caps. For feasible literal input at \(k\ge2\)
and \(r\ge8\), the witness has distinct nonempty rows.
[Reconstructed parents](OnlineReachabilityPreservers/HalfWidthRectangleRepair.lean#L13)
· [Half exclusion on the retained pieces](OnlineReachabilityPreservers/HalfWidthRectangleRepair.lean#L39)
· [Supported erasure and cost](OnlineReachabilityPreservers/HalfWidthRectangleRepair.lean#L75)
· [Indexed witness](OnlineReachabilityPreservers/HalfWidthRectangleRepair.lean#L94)
· [Literal witness](OnlineReachabilityPreservers/HalfWidthRectangleRepair.lean#L167).

When \(M>8\max(n,p)\), the original widths admit rectangles of mass at
least \(27M/31\) within both budgets. For simple half-free input with
positive budgets, \(M\ge\max(n,p)\), and \(k\ge2\), require such a rectangle whose tested
width walks span at most \(\lfloor L/3\rfloor\) in their original copied
parent. Mark that many initial positions of every noninitial original
block before restricting to the rectangle. Erase the marks in the
rectangle, charging at most \(M/3\) for the entire mark set. The retained pieces have no crossed return
within radius \(\max(0,k-3)\). The degree-return test is on the parents
reconstructed after this erasure, with the same radius. If it passes,
the supported repair preserves the input cutoff, both original budgets
and all four original caps with \(M/27\) retention. The low-mass branch
needs neither test. The feasible literal witness is distinct and nonempty.
[Dense rectangle certificate](OnlineReachabilityPreservers/HalfWidthRectangleBoundary.lean#L13)
· [Indexed short-span repair](OnlineReachabilityPreservers/HalfWidthRectangleBoundary.lean#L31)
· [Literal short-span repair](OnlineReachabilityPreservers/HalfWidthRectangleBoundary.lean#L71).

Refine the standard copied vertices by assigning a colour to each
parent occurrence. A tested crossed return survives exactly when each
corner has a colour consistent with both occurrences at that corner.
Separating a corner on every return of at most \(k-5\) steps preserves
full exclusion through \(k\ge7\) with the same path pieces and all their
incidences. Start from simple input excluding full bridges through
\(k\), with positive budgets and \(M\ge\max(n,p)\). When
\(M>8\max(n,p)\), require a separating colouring with at most \(4n/3\)
occupied vertex copies. The indexed and feasible literal witnesses retain
at least \(M/16\) with both original budgets, the same cutoff and all four
original caps. Low mass requires no colouring.
[Exact return criterion](OnlineReachabilityPreservers/FullReturnCopyColours.lean#L75)
· [Full preservation](OnlineReachabilityPreservers/FullReturnCopyColours.lean#L102)
· [Copy support premise](OnlineReachabilityPreservers/FullReturnCopyColours.lean#L140)
· [Indexed witness](OnlineReachabilityPreservers/FullReturnCopyColours.lean#L153)
· [Literal witness](OnlineReachabilityPreservers/FullReturnCopyColours.lean#L211).

With two colours, a copied vertex outside a chosen exception set uses
a fixed tag across its occurrences. Each exception adds at most one
occupied vertex label. At mean degree at least eight, the standard
degree blocks number at most \(39n/31\), so exceptions on at most
\(7n/93\) copied vertices fit the \(4n/3\) support allowance. If the
binary refinement separates every tested return, it therefore supplies
the support premise for the full \(M/16\) cleaning witness.
[Width budget](OnlineReachabilityPreservers/LocalFrozenCleaning.lean#L1067)
· [Binary copy count](OnlineReachabilityPreservers/FullReturnBinaryCopies.lean#L11)
· [Small exception certificate](OnlineReachabilityPreservers/FullReturnBinaryCopies.lean#L44).

The same radius \(k-5\) works for grouped path splitting at every
full cutoff \(k\ge7\). When every group on the standard copies
fits the original path width, pack whole groups and trim both
supports. For simple input excluding full bridges through \(k\)
with mass at least both positive budgets, the original-width
witness then keeps at least \(M/4\). The original rows can also be
used for the group-size test because the copied comparisons and
their groups project to the original ones. For feasible literal
input the original-row test gives a distinct nonempty witness of
mass at least \(M/8\) with the same cutoff, budgets and four caps.
[Packing](OnlineReachabilityPreservers/FullReturnGroupedCleaning.lean#L14) · [Copied-group test](OnlineReachabilityPreservers/FullReturnGroupedCleaning.lean#L39) · [Original-group test](OnlineReachabilityPreservers/FullReturnGroupedCleaning.lean#L61) · [Literal witness](OnlineReachabilityPreservers/FullReturnGroupedCleaning.lean#L76).

For simple paths excluding full bridges through a cutoff of at least three,
restrict to a set of vertices contained in one reference row. Among the other rows, starts of
consecutive comparisons are distinct. Two comparisons with a shared start
would be parallel or would form a full 3-bridge using the reference row's
comparison between their ends. The starts also avoid the reference row's
first vertex in the restriction, since all other comparisons follow the
reverse order there. This bounds the total restricted excess by
\(2\max(0,|S|-1)\). For \(t\) covering rows, assign every occurring vertex to
one row that contains it. Summing the resulting estimates gives
\(M\le tp+2n\). At most six covering rows put the input within the low-mass
cleaning regime. For positive budgets and mass at least both of them, the
indexed or feasible literal witness retains at least \(M/8\), with the same
cutoff, both budgets and all four original-average caps.
[Restricted excess](OnlineReachabilityPreservers/FullCoveringRow.lean#L142)
· [Mass with covering rows](OnlineReachabilityPreservers/FullCoveringRow.lean#L293)
· [Indexed witness](OnlineReachabilityPreservers/FullCoveringRow.lean#L339)
· [Literal witness](OnlineReachabilityPreservers/FullCoveringRow.lean#L372).

For simple input excluding half bridges through a cutoff of at least three,
assign each occurring vertex to the row of its first occurrence. The
reference comparison between the ends of two other comparisons would be
the final arc on an earlier row, so the same shared-start argument applies
within each assigned vertex set. If there are \(t\) first-occurrence rows,
the mass bound is again \(M\le tp+2n\). With \(t\le6\) and mass reaching
both positive budgets, the witness retains at least \(M/8\) and can exclude
full bridges through any chosen cutoff. This gives a conditional instance
of the comparison in the literal Lemma 39 when a half-bridge maximizer
has such a cover. The feasible literal witness is distinct and nonempty,
and both versions meet the four original-average caps within the original
budgets.
[Shared starts with an earlier row](OnlineReachabilityPreservers/FullCoveringRow.lean#L31)
· [Restricted excess](OnlineReachabilityPreservers/FullCoveringRow.lean#L164)
· [Mass bound](OnlineReachabilityPreservers/FullCoveringRow.lean#L303)
· [Indexed full witness](OnlineReachabilityPreservers/FullCoveringRow.lean#L406)
· [Literal full witness](OnlineReachabilityPreservers/FullCoveringRow.lean#L451).

Both covering-row mass proofs count only nonempty restrictions. Let \(A\)
be the sum, over input rows, of the numbers of assigned vertex sets they
meet. The mass estimate becomes \(M\le A+2n\), since the excess in each
vertex set still contributes at most twice its cardinality. With the same
positive budgets, density, original cutoff of at least three and either
corresponding cover premise, \(A+2n\le8\max(n,p)\) supplies the frozen
\(M/8\) witness. A sufficient condition is that each row meets at most six
assigned sets. The full-input witness retains the original cutoff. The
half-input witness can exclude full bridges through any chosen cutoff.
The literal versions apply to feasible distinct nonempty families.
[Count nonempty restrictions](OnlineReachabilityPreservers/FullCoveringRow.lean#L187)
· [Per-row bound](OnlineReachabilityPreservers/FullCoveringRow.lean#L190)
· [Full mass bound](OnlineReachabilityPreservers/FullCoveringRow.lean#L264)
· [Half mass bound](OnlineReachabilityPreservers/FullCoveringRow.lean#L277)
· [Indexed full input](OnlineReachabilityPreservers/FullCoveringRow.lean#L322)
· [Literal full input](OnlineReachabilityPreservers/FullCoveringRow.lean#L353)
· [Indexed half input](OnlineReachabilityPreservers/FullCoveringRow.lean#L388)
· [Literal half input](OnlineReachabilityPreservers/FullCoveringRow.lean#L421).

For any simple indexed input excluding half or full bridges through a
cutoff of at least three, with a positive path budget, assign each used
vertex to its first row. Keep that whole assigned set on its reference
row. Restrict every other row to at most one representative from that
set. The loss in each set is exactly the sum of the excesses over one
on the nonreference rows. The reference row contributes \(|S|-1\) when
\(S\) is nonempty, so the restricted excess bound gives total loss at most
\(\max(0,|S|-1)\) there. The sets are disjoint, giving a loss of at most
\(n\) overall. All first occurrences remain, and sublists preserve the
same bridge exclusion and original path labels.
[First-occurrence assignment](OnlineReachabilityPreservers/FirstOccurrenceTrimming.lean#L11)
· [Half-input trimming](OnlineReachabilityPreservers/FirstOccurrenceTrimming.lean#L45)
· [Full-input trimming](OnlineReachabilityPreservers/FirstOccurrenceTrimming.lean#L179).

For simple input excluding half bridges through five, suppose two vertices
have the same first row whenever their comparisons occur in both directions
on different rows.
The preceding trimming deletes at least one comparison in each pair. Parallel
comparisons are already forbidden, so the surviving rows have pairwise
intersections of size at most one. For positive budgets and mass \(M\) at
least both budgets, the low-mass construction applies
when \(M\le8\max(n,p)\). Above that threshold the trimmed rows retain
at least \(7M/8\). Their unique intersections protect both splits at
the original widths. Restriction and peeling give an indexed or feasible
literal frozen witness of mass at least \(M/32\), using both original
budgets and all four original-average caps at half cutoff five.
[First-occurrence premise](OnlineReachabilityPreservers/FirstOccurrenceHalfFive.lean#L13)
· [Unique intersections](OnlineReachabilityPreservers/FirstOccurrenceHalfFive.lean#L89)
· [Indexed witness](OnlineReachabilityPreservers/FirstOccurrenceHalfFive.lean#L139)
· [Literal witness](OnlineReachabilityPreservers/FirstOccurrenceHalfFive.lean#L177).

Allow opposite comparisons to cross first-occurrence groups. Let \(S\)
be a set of original incidences containing one of the four endpoints,
with its row label, of each such pair. Use first-occurrence trimming
for the pairs within a group and erase \(S\) for the cross-group pairs.
The resulting rows have unique intersections and total loss at most
\(n+|S|\). For simple input excluding half bridges through five, with
positive budgets and mass at least both of them, the low-mass construction
handles \(M\le8\max(n,p)\). Otherwise require \(8(n+|S|)\le M\) to
retain at least \(7M/8\) before the original-width splits. The resulting
indexed or feasible literal frozen witness retains at least \(M/32\)
with half exclusion through five, both budgets and all four caps.
[Cross-group cover](OnlineReachabilityPreservers/FirstOccurrenceHalfFive.lean#L19)
· [Erasure and incidence loss](OnlineReachabilityPreservers/FirstOccurrenceHalfFive.lean#L26)
· [Indexed witness](OnlineReachabilityPreservers/FirstOccurrenceHalfFive.lean#L108)
· [Literal witness](OnlineReachabilityPreservers/FirstOccurrenceHalfFive.lean#L158).

The loss from opposite-intersection pruning after first-occurrence trimming
can be bounded before trimming. Use the graph of neighboring common vertices
that have opposite orders on two rows. Restrict its original links to endpoints
in different first-occurrence groups and let \(E\) be the number of those links.
The surviving opposite links all cross groups. Each surviving link's endpoints
are joined by a chain of original links within its original interval, so that
chain contains a link across groups. Orient the charge by the two row labels.
Exclusion of parallel comparisons determines those labels, and different surviving
intervals on the same pair of rows cannot share a charged link. Hence the
charges are injective. For a simple family with a positive path budget and
half exclusion through \(k\ge3\), the combined pruning gives unique
intersections, keeps that cutoff and loses at most \(n+E\) incidences.
[Crossing link within an interval](OnlineReachabilityPreservers/CrossGroupOppositeLinks.lean#L23)
· [Graph of cross-group links](OnlineReachabilityPreservers/CrossGroupOppositeLinks.lean#L76)
· [Cardinality bound](OnlineReachabilityPreservers/CrossGroupOppositeLinks.lean#L94)
· [Combined pruning](OnlineReachabilityPreservers/CrossGroupOppositeLinks.lean#L148).

At half cutoff five, the original cross-group link count \(E\) yields a frozen
witness if \(24(n+E)\le11M\) in the range \(M>8\max(n,p)\). The loss bound
leaves at least \(13M/24\) on the unique-intersection sublists before width
splitting and trimming. For simple input with positive budgets and mass at
least both budgets, the witness retains \(M/288\) or more, fits both original
budgets and all four original-average caps, and preserves half-five exclusion.
The same guarantee applies to feasible literal distinct nonempty input and
output. The low-mass branch needs no link bound.
[Unique sublist version](OnlineReachabilityPreservers/FrozenMatchedPartners.lean#L702)
· [Indexed cross-group witness](OnlineReachabilityPreservers/CrossGroupFrozenCleaning.lean#L14)
· [Literal cross-group witness](OnlineReachabilityPreservers/CrossGroupFrozenCleaning.lean#L40).

The first-occurrence sublist condition permits a degree-splitting failure.
On an indexed family with twelve vertices, forty-three rows and mass
forty-eight, each occupied first-occurrence group has one vertex. The five
active rows retain the order of the earlier half-five example. The added singleton
rows shift the degree blocks and introduce no comparisons. All half bridges
are excluded in the original family. The degree width is sixteen and the
path width is four. The actual degree split contains a half-five bridge.
The two arcs of its terminal detour project to opposite original
comparisons across groups. The low-mass construction supplies a separate
witness at these budgets.
[Exact widths](OnlineReachabilityPreservers/FirstOccurrenceDegreeSplitAudit.lean#L89)
· [First-occurrence condition](OnlineReachabilityPreservers/FirstOccurrenceDegreeSplitAudit.lean#L100)
· [Cross-group opposites](OnlineReachabilityPreservers/FirstOccurrenceDegreeSplitAudit.lean#L107)
· [Half-five bridge after the degree split](OnlineReachabilityPreservers/FirstOccurrenceDegreeSplitAudit.lean#L115).

The graph radius is sharp for the disjoint split test at every
full cutoff \(k\ge7\). A checked indexed family on \(k\) vertices
and \(k\) labels excludes full bridges at all sizes. The split
preserves the order of each piece, covers every original incidence and passes
the \(k-6\) graph test on the actual pieces. The explicit return
from 1 to \(k-4\) fails the \(k-5\) test. The split pieces contain
a full bridge of size \(k\). The witness audits preservation by a
split, and the general frozen existence question remains open.
[Condition at radius \(k-6\)](OnlineReachabilityPreservers/FullReturnRadiusSharpness.lean#L381) · [Crossing at radius \(k-5\)](OnlineReachabilityPreservers/FullReturnRadiusSharpness.lean#L437) · [Uniform example](OnlineReachabilityPreservers/FullReturnRadiusSharpness.lean#L452).

The full-seven lift also permits packing the original-width path
pieces from components of returns of at most two steps in the
whole copied rows. Each connected group of endpoints must fit
the original length width. This retains at least \(M/4\) at full
cutoff seven with both original budgets and all four original-average
caps, for simple input excluding full bridges through seven and
mass \(M\) at least both positive budgets.
Testing the original row components instead also suffices because
copied components only project inside original ones.
For feasible literal distinct nonempty input, the witness can
be distinct and nonempty with retention at least \(M/8\).
[Packing theorem](OnlineReachabilityPreservers/ShortReturnPiecePacking.lean#L253) · [Frozen witness on copied components](OnlineReachabilityPreservers/ShortReturnStandardCleaning.lean#L195) · [Original component test](OnlineReachabilityPreservers/ShortReturnStandardCleaning.lean#L215) · [Literal witness](OnlineReachabilityPreservers/ShortReturnStandardCleaning.lean#L230).

The radius-two group condition also works after initial rowwise
deletions. Keep the two original widths and charge the initial
loss together with the radius-two path excess on the restricted
rows. At most \(\lfloor M/3\rfloor\) combined loss gives a
full-seven frozen witness of mass at least \(M/18\) with both
original budgets and all four caps. The simple original input
excludes full bridges through seven, and its mass \(M\) is at
least both positive budgets. The transfer to feasible literal
input gives the same guarantee with distinct nonempty output rows.
[Mass threshold after grouping](OnlineReachabilityPreservers/ShortReturnVertexPacking.lean#L166) · [Two-thirds restriction](OnlineReachabilityPreservers/ShortReturnStandardCleaning.lean#L252) · [Recomputed excess test](OnlineReachabilityPreservers/ShortReturnStandardCleaning.lean#L275) · [Literal witness](OnlineReachabilityPreservers/ShortReturnStandardCleaning.lean#L316).

In an indexed family on six vertices and nine row labels with
mass nine, the original widths are six and four. The input
excludes full bridges at every size. On the standard copied pieces,
the return \(4\to5\to0\) crosses the consecutive width-four cut of
the long row. The original radius-four component exceeds width four
and every original radius-two component fits that width. The grouped
test gives a full-seven frozen quarter-mass witness with both budgets
and all four original-average caps.
[Original widths](OnlineReachabilityPreservers/FullSevenGroupedAudit.lean#L20) · [Consecutive cut obstruction](OnlineReachabilityPreservers/FullSevenGroupedAudit.lean#L66) · [Radius-two room](OnlineReachabilityPreservers/FullSevenGroupedAudit.lean#L93) · [Radius-four size](OnlineReachabilityPreservers/FullSevenGroupedAudit.lean#L101) · [Frozen witness](OnlineReachabilityPreservers/FullSevenGroupedAudit.lean#L106).

For a two-step return to an earlier vertex of a parent, fix the first
alternative row and the common start vertex on the parent. Under full
exclusion through four, distinct third rows give distinct corners
whose orders agree along the parent and first alternative row.
Lemma 24 applies in an auxiliary arrival order with the parent first.
The number of third rows is at most the number of parent predecessors
and at most the number of first-row successors at the fixed vertex.
Under unique intersections, each third row has exactly one pair of
corners, so counting all witnesses gives the same count.
[Return relation](OnlineReachabilityPreservers/TwoStepReturnMatching.lean#L83) · [Order agreement](OnlineReachabilityPreservers/TwoStepReturnMatching.lean#L90) · [Both cardinality bounds](OnlineReachabilityPreservers/TwoStepReturnMatching.lean#L130) · [Exact witness count with unique intersections](OnlineReachabilityPreservers/TwoStepReturnMatching.lean#L164).

For full-three-free parent rows, assume comparisons lift from the
pieces, the pieces are order convex, and the one-step condition holds.
A two-step return crossing two parent pieces has no original direct
reverse between its two parent corners. The statement refers to the
parent rows immediately before the path split, including vertex labels
from a preceding degree split. If those pieces cover their parents,
each of the three corners is absent from the opposite row of the
return triangle. For full-seven-free parents, disjoint pieces satisfying
the same one-step and convexity conditions preserve full-seven
exclusion if every original two-step return through distinct other
parents has a direct reverse comparison.
[Convex standard width blocks](OnlineReachabilityPreservers/FullSevenReverseComparison.lean#L18) · [No direct reverse](OnlineReachabilityPreservers/FullSevenReverseComparison.lean#L78) · [Corner memberships](OnlineReachabilityPreservers/FullSevenReverseComparison.lean#L168) · [Preservation theorem](OnlineReachabilityPreservers/FullSevenReverseComparison.lean#L213).

When the pieces cover their parents, the one-step condition is
enough to deduce all three absent-corner memberships for an
actual crossed two-step return, including with interleaved pieces.
For disjoint order-preserving covering pieces of full-seven-free
rows, the one-step condition and a check of only these induced
returns on the actual pieces suffice at full cutoff seven. A
sufficient static condition keeps the endpoints of all such induced
returns and direct reversals together. Under full-three exclusion,
the noninduced returns are implied by one or two direct reversals,
so the sets of feasible static width partitions are equal.
[Induced return](OnlineReachabilityPreservers/FullSevenInducedReturns.lean#L14) · [Actual piece test](OnlineReachabilityPreservers/FullSevenInducedReturns.lean#L32) · [Endpoint condition](OnlineReachabilityPreservers/FullSevenInducedReturns.lean#L55) · [Decomposition of links](OnlineReachabilityPreservers/FullSevenInducedReturns.lean#L74) · [Equivalent static partitions](OnlineReachabilityPreservers/FullSevenInducedReturns.lean#L101).

The component test can use the row labels of the return steps.
A comparison is protected if it has a direct reverse or a return
through two distinct other rows. Put its endpoints in the same
part. This rule suffices for full exclusion through any cutoff
up to seven on disjoint order-preserving pieces of parents
with the corresponding full exclusion. At a prescribed width,
a partition respecting these comparisons exists exactly when
the symmetric graph's components on each row fit that width.
These components refine the components from the radius-two
precedence graph.
[Protected comparisons](OnlineReachabilityPreservers/FullSevenPathLinks.lean#L20) · [Full exclusion through seven](OnlineReachabilityPreservers/FullSevenPathLinks.lean#L42) · [Width-bounded partition equivalence](OnlineReachabilityPreservers/FullSevenPathLinks.lean#L88) · [Refinement](OnlineReachabilityPreservers/FullSevenPathLinks.lean#L105).

Width-bounded packing of those groups preserves both mass and
vertex degrees. With the corresponding original full exclusion,
it preserves full exclusion through every chosen cutoff at most
seven. Apply it at the factor-four path width on the standard
degree copies. If the components on those copies fit that width,
the two support trims and frozen peeling give an indexed full-seven
witness retaining at least \(M/4\), with both original budgets and
all four original-average caps. The original input is simple and
full-seven-free, with mass \(M\) at least both positive budgets.
[Group packing](OnlineReachabilityPreservers/FullSevenLinkedCleaning.lean#L14) · [Copied component test](OnlineReachabilityPreservers/FullSevenLinkedCleaning.lean#L33).

An exact projection of each copied row to a simple original row
preserves the labels and comparisons of its returns. The projection
maps the copied component into the original component and is injective
on the copied row, so the original component bounds also give the
same indexed \(M/4\) witness. For feasible distinct nonempty input,
the same original width test gives a distinct nonempty \(M/8\)
witness at full cutoff seven with both original budgets and all
four original-average caps.
[Linked comparison projection](OnlineReachabilityPreservers/FullSevenLinkedCleaning.lean#L57) · [Component size comparison](OnlineReachabilityPreservers/FullSevenLinkedCleaning.lean#L73) · [Original component test](OnlineReachabilityPreservers/FullSevenLinkedCleaning.lean#L101) · [Literal witness](OnlineReachabilityPreservers/FullSevenLinkedCleaning.lean#L125).

With five vertices and seven indexed rows, the first two rows
`[0,1,2,3,4]` and `[4,0]` carry all seven incidences. There are no
full bridges at any size. The path width is four. The protected
group of vertex 0 in the first row has size two, and the broad
radius-two group at the same vertex has size five. All the protected
groups fit and give the indexed frozen witness at full cutoff seven.
[Input and full exclusion](OnlineReachabilityPreservers/FullSevenPathLinkAudit.lean#L25) · [Exact group sizes](OnlineReachabilityPreservers/FullSevenPathLinkAudit.lean#L77) · [Width test](OnlineReachabilityPreservers/FullSevenPathLinkAudit.lean#L86) · [Frozen witness](OnlineReachabilityPreservers/FullSevenPathLinkAudit.lean#L99).

At half cutoff four, a [balanced midpoint split with no valid arrival permutation](OnlineReachabilityPreservers/HalfFourSplitOrderAudit.lean#L103)
starts from a half-free indexed family with uniform degree two and mean
length \(7/2\). Its sole length-six path splits into two length-three
pieces. The split system has a 3-bridge and a 4-bridge imposing opposite
relative arrival constraints on one piece and one unchanged row.
A [separate witness](OnlineReachabilityPreservers/HalfFourSplitOrderAudit.lean#L118)
fits the original budgets and caps.

At full cutoff six, [output-average cleaning](OnlineReachabilityPreservers/LocalAverageCleaning.lean)
starts at the unrestricted maximum over indexed simple paths. It retains
at least \(M/392\) of the maximizing mass \(M\), keeps both budgets, and
meets all four factor-four caps around the cleaned witness's own averages.
The same construction preserves half exclusion through six for an input
that also excludes full bridges through four and whose mass is at least
both positive budgets.

At half cutoff five, [output-average cleaning](OnlineReachabilityPreservers/HalfFiveAverageCleaning.lean)
holds for arbitrary simple half-five-free input of mass at least both
positive budgets and for the unrestricted indexed maximum at every pair
of positive budgets. The witness retains at least \(M/392\) within both
original budgets and meets all four caps relative to its own averages.
Pruning produces unique intersections, so the two width splits preserve
half-five exclusion after both supports are restricted.

[Literal output-average cleaning](OnlineReachabilityPreservers/OutputAverageDistinctCleaning.lean)
covers the feasible distinct nonempty path maximum at cutoff four in
either mode, half cutoff five, and full cutoff six. It gives both budgets,
all four caps relative to the output averages, and at least \(M/7056\).
A short row in the indexed witness bounds its mean length by four. In
that case a single spanning row or a uniform directed bipartite family
replaces the indexed witness within both original budgets. When all
indexed witness rows have length at least two they are already distinct.

[Output-average cleaning for each small cutoff](OnlineReachabilityPreservers/OutputAverageShortCleaning.lean)
covers half cutoffs through five and full cutoffs through six at every
positive indexed maximum. It covers the corresponding feasible literal
maxima of distinct nonempty paths from cutoff two. The retention factors
are \(M/392\) and \(M/7056\), respectively. Both models meet both
budgets and all four caps relative to the output averages.

[Output-average full component cleaning](OnlineReachabilityPreservers/IncreasingFullAverageCleaning.lean)
retains at least \(M/523\) with both original budgets and all four caps
relative to the output averages. At a cutoff of at least three, it applies
to simple full-bridge-free input through that cutoff with mass at least
both positive budgets, provided each precedence component excludes full
bridges at every size. When the cutoff covers the smaller budget, it
applies at the unrestricted indexed maximum and the output excludes every
full bridge. The [literal transfer](OnlineReachabilityPreservers/OutputAverageDistinctCleaning.lean)
gives the corresponding feasible literal maximum with distinct nonempty
rows and retention \(M/9414\). It also gives a literal witness under the
finite full component condition at the input cutoff.

An opposite-neighbor link joins consecutive common vertices of two
oppositely ordered paths. In an input excluding full bridges through size
three, a simple cycle of \(r\) links produces a full bridge of size at most
\(r\). At full cutoff \(k\ge3\), every cycle has length greater than \(k\).
The existing pruning charges each removed incidence to a distinct link
using half exclusion through size two. With full exclusion at every size,
the link graph is a forest and the loss is at most \(n-1\) for \(n>0\).
[Cycle bound](OnlineReachabilityPreservers/OppositeLinkForest.lean#L331)
· [Finite cutoff](OnlineReachabilityPreservers/OppositeLinkForest.lean#L410)
· [Charge in half mode](OnlineReachabilityPreservers/OppositeLinkForest.lean#L468)
· [Pruning bound](OnlineReachabilityPreservers/OppositeLinkForest.lean#L528).

For simple paths with full exclusion through six or half exclusion through
four, let \(E\) count these links. If \(M\ge8E\) and the mass \(M\) is
at least both positive budgets, there is a cleaned family within both
budgets with the input's cutoff and bridge mode, all four original-average
caps, and mass at least \(M/32\).
[Full cutoff six](OnlineReachabilityPreservers/ContiguousSixCleaning.lean#L136)
· [Half cutoff four](OnlineReachabilityPreservers/ContiguousHalfCleaning.lean#L340).

For an input excluding full bridges at every size, the same size-six
cleaning conclusion holds at every mass at least both positive budgets.
The lower-mass case uses explicit witnesses. The larger-mass case uses the
forest bound and the original cap widths.
[All-size input](OnlineReachabilityPreservers/ContiguousSixCleaning.lean#L151).

The [common-order deletion](OnlineReachabilityPreservers/OfflineBridgeConverse.lean#L209)
also yields [cleaning with full exclusion at every size](OnlineReachabilityPreservers/FullBridgeCleaning.lean#L37)
for input that excludes every full bridge and has mass \(M\) at least
both positive budgets. It meets the two budgets and all four original
caps with retention \(M/32\) when \(M\le8\max(n,p)\) or \(24n\le M\).
In the latter range, deleting at most \(3n\) incidences leaves at least
seven eighths of the original mass and a common order. The resulting
precedence graph allows both width splits at any cutoff. The output
excludes every full bridge by its path budget.

The [stronger deletion bound](OnlineReachabilityPreservers/OfflineBridgeConverse.lean#L209)
removes at most two incidences per vertex. If \(M>8\max(n,p)\), the retained
mass \(K\) is at least \(3M/4\). For either support, the original width cuts
expand the budget by a factor at most \((31M+8K)/(31M)\). With the sparse
witness in the other range, the [all-mass theorem](OnlineReachabilityPreservers/FullBridgeCleaning.lean#L271)
gives a cleaned system excluding every full bridge, with at least \(M/40\),
both original budgets, and all four original-average caps. Its input
excludes every full bridge and has mass at least both positive budgets.

At a specified finite full cutoff \(k\), each precedence component can
be handled on its own if it excludes all full bridges locally. For
example, [at most \(k\) rows with strict steps inside a component](OnlineReachabilityPreservers/OfflineBridgeConverse.lean#L292)
give all-size local exclusion, because the river and chain use distinct
rows. At each elimination, a remaining component of maximal condensation
rank supplies a [vertex with at most two outgoing rows](OnlineReachabilityPreservers/OfflineBridgeConverse.lean#L221).
The [finite-cutoff cleaning theorem](OnlineReachabilityPreservers/FullBridgeCleaning.lean#L203)
uses this deletion bound to meet both original budgets and all four
original-average caps while retaining \(M/40\).

[After rowwise deletions](OnlineReachabilityPreservers/FullBridgeCleaning.lean#L218), the same local all-size premise
can be checked on the surviving precedence components. If the deletions
cost at most \(M/28\), a further loss of at most two incidences per
vertex still permits frozen cleaning at the original finite cutoff,
retaining at least \(M/128\). The original budgets and all four
original-average caps hold. The [row-count test](OnlineReachabilityPreservers/FullBridgeCleaning.lean#L250)
is one sufficient way to certify the surviving components.

Every bridge corner belongs to two distinct original rows with internal
steps in its component. The [corner count](OnlineReachabilityPreservers/FullBridgeComponentSupports.lean#L39)
therefore gives another bound on the size of a local bridge. The
[mixed support theorem](OnlineReachabilityPreservers/FullBridgeComponentSupports.lean#L96)
accepts either at most \(k\) internal rows or at most \(k\) vertices
shared by two such rows in each component. The choice is independent
across components.

The [oversized component visit theorem](OnlineReachabilityPreservers/FullBridgeComponentSupports.lean#L269)
applies when neither original support bound fits in some components.
These visits retain their first vertex and lose only their excess over
one. At loss at most \(M/28\), the surviving graph gives the same
\(M/128\) frozen guarantee through the original finite full cutoff.

For half-bridge exclusion through size three, the
[opposite-link graph has no triangles](OnlineReachabilityPreservers/OppositeLinkForest.lean#L576).
Each link joins consecutive common vertices of two paths that traverse
them in opposite orders. The [two-link property](OnlineReachabilityPreservers/OppositeLinkForest.lean#L620)
puts the intermediate vertex on any path that contains both distinct endpoints.
At cutoff four, the [four-cycle exclusion](OnlineReachabilityPreservers/OppositeLinkForest.lean#L793)
uses that property to compare the last arcs in competing detours. It
shows that [every cycle has length at least five](OnlineReachabilityPreservers/OppositeLinkForest.lean#L846).

Under half-bridge exclusion through five, every cycle of consecutive
opposite links has length at least six. If no row contains all five
vertices of a putative five-cycle, no row can contain four, by the
two-link property. A gap in the latest row used by the links yields
a detour of at most four steps using earlier rows only. Consecutive
repeated labels can be compressed to a single step. If one row contains
all five vertices, choose a sink whose two neighbors are higher in that
row. A comparison in the spanning row and the complementary detour
give two bridges requiring opposite arrival orders at the sink. The
complementary detour uses at most one spanning-row comparison and
compressing repeated labels keeps its final arc.
[Spanning-row reduction](OnlineReachabilityPreservers/HalfFiveOppositeCycles.lean#L161) · [Five-cycle exclusion](OnlineReachabilityPreservers/HalfFiveOppositeCycles.lean#L566) · [All cycle lengths](OnlineReachabilityPreservers/HalfFiveOppositeCycles.lean#L575).

On the two sides of an opposite link, the two-step walks that continue
away from that link have distinct endpoints. All of these endpoints
lie outside the two disjoint neighborhoods of the link endpoints.
If the opposite-link graph has an edge and minimum degree at least
\(d\), this gives \(2d+2(d-1)^2\le n\). For a regular opposite-link graph
with simple input, positive budgets and mass \(M\) at least both budgets,
the inequalities \(12n\le11M\) and \(144n^3\le2(11M-12n)^2\) bound the
number of links by \(11M/24\). The resulting half-five witness retains
at least \(M/288\) with both original budgets and all four frozen caps.
[Two-step endpoint count](OnlineReachabilityPreservers/HalfFiveOppositeLinkCount.lean#L34) · [Minimum degree bound](OnlineReachabilityPreservers/HalfFiveOppositeLinkCount.lean#L140) · [Frozen cleaning with regular opposite links](OnlineReachabilityPreservers/HalfFiveOppositeLinkCount.lean#L171)

The two-step count also controls arbitrary degrees. Write \(m=2E\) for
the number of oriented links. For each oriented link \(xy\), sum the
product of its endpoint degrees. Twice that sum is at most
\(nm+2n(n-1)\). Summing the rooted bounds gives the degree-product term
along with the sum of vertex degree squares. The count of two-step
walks with distinct endpoints bounds that square term after removing
the walks that immediately return to their start.
[Degree products over oriented links](OnlineReachabilityPreservers/HalfFiveOppositeLinkCount.lean#L301).

For arbitrary degrees, Cauchy–Schwarz bounds the degree-product sum below
by \(m^3/n^2\) when \(n>0\). Each nonisolated vertex contributes exactly one
to the sum of reciprocal degrees over oriented links starting at that
vertex. Applying the arithmetic–geometric mean inequality to each link
and using Cauchy–Schwarz twice gives the lower bound. The resulting
integer inequality is \(2m^3\le n^3m+2n^3(n-1)\). For simple input with positive
budgets, mass \(M\) at least both budgets and half exclusion through five,
the conditions \(48n\le11M\) and \(108n^3\le(11M)^2\) ensure at most \(11M/24\)
opposite links. The half-five frozen witness keeps at least \(M/288\)
of the original mass with both budgets and all four original-average caps.
[Cubic bound on opposite links](OnlineReachabilityPreservers/HalfFiveOppositeLinkCount.lean#L474) · [Half-five cleaning with the mass bound](OnlineReachabilityPreservers/HalfFiveOppositeLinkCount.lean#L499).

The [link count](OnlineReachabilityPreservers/OppositeLinkForest.lean#L877)
uses triangle and four-cycle exclusion to inject ordered two-link walks
into ordered pairs of distinct vertices. Cauchy–Schwarz gives
\(4E^2\le n^2(n-1)\). For a simple half-four-free family with positive
budgets and \(M\) at least both counts, the
[incidence condition](OnlineReachabilityPreservers/ContiguousHalfCleaning.lean#L370)
\(M^2\ge16n^2(n-1)\) gives \(8E\le M\) and hence a cleaned family
with both original budgets, all four original-average caps, and
retention of \(M/32\). At the unrestricted half-four maximum, the
[path-budget condition](OnlineReachabilityPreservers/ContiguousHalfCleaning.lean#L393)
\(p^2\ge16n^2(n-1)\) gives this stronger retention bound.

For any fixed ordered disjoint split, each retained nested reversal marks
the starting incidence of its inner step. The
[post-split repair](OnlineReachabilityPreservers/ContiguousHalfCleaning.lean#L443)
deletes exactly the [distinct marked incidences](OnlineReachabilityPreservers/ContiguousHalfCleaning.lean#L473)
and restores half exclusion through size four. For the original-width
blocks, at most \(M/12\) such incidences suffice for
[both budgets and all four original-average caps](OnlineReachabilityPreservers/ContiguousHalfCleaning.lean#L559),
with retention at least \(M/64\) after restriction and peeling. Each
mark [charges a distinct incidence](OnlineReachabilityPreservers/ActiveNestedCutCounting.lean#L58)
with a successor in a non-first central block. Exclusion through size
three prevents two later rows from charging the same incidence. The
[sum over block lengths](OnlineReachabilityPreservers/ActiveNestedCutCounting.lean#L35)
counts these available incidences. If the sum is at most \(M/12\), the
[same cleaning conclusion](OnlineReachabilityPreservers/ActiveNestedCutCounting.lean#L135)
follows.

The [full-block profiles](OnlineReachabilityPreservers/WidthBlockProfiles.lean#L161)
show that each original vertex and path contributes at most one remainder.
Keeping all filled blocks and choosing the heaviest remainders bounds the
[loss across both budgets](OnlineReachabilityPreservers/BalancedRegularization.lean#L697)
by \(M/6\). This leaves enough room for an
[admissibility repair](OnlineReachabilityPreservers/FrozenBlockTrimming.lean#L74)
that removes up to \(M/4\) of the original incidences. Peeling then meets both
budgets and all four original-average caps with at least \(M/12\) mass. The
half-four criterion applies when either the
[marked count](OnlineReachabilityPreservers/FrozenBlockTrimming.lean#L153)
or the [later nonterminal count](OnlineReachabilityPreservers/FrozenBlockTrimming.lean#L177)
is at most \(M/4\).

If rows longer than \(\lfloor 4M/p\rfloor\) carry at least \(2M/3\),
the [overlong-subfamily theorem](OnlineReachabilityPreservers/FrozenOverlongPaths.lean#L191)
prunes opposing intersections only in that subfamily before splitting.
Its path pieces already fit in the original path budget, and
[vertex trimming](OnlineReachabilityPreservers/BalancedRegularization.lean#L684)
loses at most the squared retained mass divided by four times the vertex
block width times the vertex budget. Peeling uses the actual piece count.
The witness retains at least \(M/216\) and has all four original-average
caps and both original budgets through half cutoff four or full cutoff six.
When those overlong rows carry at most \(7M/15\), the
[length-capped subfamily](OnlineReachabilityPreservers/FrozenLengthCappedPaths.lean#L154)
retains at least \(8M/15\) before trimming. It requires only vertex splits,
so the construction preserves full exclusion at every cutoff and half
exclusion through size four. It meets both original budgets and all four
frozen caps and retains at least \(M/104\). The
[underlying theorem](OnlineReachabilityPreservers/FrozenLengthCappedPaths.lean#L88)
applies to any length-capped subfamily carrying that much mass.
The [clipped subfamily](OnlineReachabilityPreservers/FrozenLengthCappedPaths.lean#L193)
keeps the first \(\lfloor4M/p\rfloor\) entries of every row. It therefore
works when the excess \(T\) above that width is at most \(7M/15\).
If the overlong rows carry mass \(S\) and there are \(q\) such rows, the
[excess identity](OnlineReachabilityPreservers/FrozenOverlongPaths.lean#L20)
gives \(S=T+q\lfloor4M/p\rfloor\). For large \(T\), it sharpens the
bound on how many path pieces peeling can delete. Combining the cases
[covers \(S\ge7M/12\)](OnlineReachabilityPreservers/FrozenLengthCappedPaths.lean#L232)
with retention at least \(M/2000\) through half cutoff four or full cutoff
six. With these two arguments, inputs having \(T>7M/15\) and \(S<7M/12\)
still require a separate criterion.

The [ordered comparison count](OnlineReachabilityPreservers/FrozenSmallBudgets.lean)
charges each ordered pair of distinct vertices at most once under half-bridge
exclusion through size two. Cauchy–Schwarz then gives
\(M^2\le p(2n(n-1)+M)\). For either positive budget at most 29 this forces
\(M\le8\max(n,p)\), so the low-mass witness gives both budgets and all four
frozen caps, retains at least \(M/8\), and excludes full bridges through
the input cutoff. The result applies to unrestricted maxima in either mode.
At \(n=p=30\), the numerical comparison inequality permits \(M=241\).
Extending beyond 29 uniformly therefore requires another estimate.

The [path-triple count](OnlineReachabilityPreservers/FrozenPathTriples.lean)
uses the fact that any three paths meet together at at most one vertex.
If they shared two distinct vertices, two of the paths would order those
vertices the same way. Thus the sum of \(\binom{d_v}3\) is at most
\(\binom p3\). Supporting affine bounds for this binomial coefficient
give \(M\le2n+\binom p3\) and \(21M\le112n+\binom p3\).
When \(\binom p3\le56n\), the second inequality forces \(M\le8n\)
and gives a witness with at least \(M/8\), both original budgets and all
four frozen caps, excluding full bridges through any input cutoff of at
least two. For the actual subfamily of \(q\) overlong paths, counting
triples gives \(3S\le8n+\binom q3\). If \(5\binom q3\le16n\)
and \(T>7M/15\), the inequality \(T\le S\) again forces \(M\le8n\).
Combining with the clipping theorem gives at least \(M/104\), with both
frozen budgets and all four caps, at full cutoffs of at least two and
half cutoffs two through four.

When the length-capped subfamily uses at most half the available paths,
the path peeling charge is at most \(M/8\). The
[half-budget lemma](OnlineReachabilityPreservers/FrozenLengthCappedPaths.lean#L124)
then needs initial mass at least \(2M/5\) and retains \(M/90\) within
both original budgets and all four frozen caps. In the
[common partition application](OnlineReachabilityPreservers/FrozenOverlongPartitions.lean#L48),
let \(r\) be the positive number of vertex parts and \(q\) the number of
rows longer than \(L=\lfloor4M/p\rfloor\). Require \(2qr\le p\) and
an ordered-pair count on those rows at most
\(r(4L-2)\lfloor M/15\rfloor\). Partitioning and clipping then lose at
most \(\lfloor M/15\rfloor\) of their mass. When \(T>7M/15\), enough
mass remains for the half-budget lemma. Combining with ordinary clipping
gives \(M/104\) at every full cutoff and at half cutoffs through four.
The construction uses a common partition to preserve bridge exclusion
when splitting paths.

An [incidence coloring](OnlineReachabilityPreservers/IncidenceColorCleaning.lean#L45)
assigns a color to each pair of a path and a vertex on it. Tag the row
pieces and vertex copies with that color. Every bridge stays in one
color. Projecting therefore preserves distinct vertices, distinct rows,
and the original arrival order. The transformation preserves the mass
and both bridge exclusions at every cutoff. The occupied support counts
sum the number of incident colors at each
[original vertex](OnlineReachabilityPreservers/IncidenceColorCleaning.lean#L142)
and on each [original path](OnlineReachabilityPreservers/IncidenceColorCleaning.lean#L175).
If the upper caps hold in each colored piece and the occupied supports
are at most four thirds of the original budgets,
[restriction and peeling](OnlineReachabilityPreservers/IncidenceColorCleaning.lean#L213)
retain at least \(M/16\) with both original budgets and all four frozen
caps. A [full-cutoff-two family](OnlineReachabilityPreservers/IncidenceColorBudgetAudit.lean#L80)
on 64 vertices has one increasing row through all vertices and every
descending two-vertex row. It has \(p=2017\), \(M=4096\), and original
upper length cap 8. A coloring meeting the vertex support bound uses at
most 85 occupied copies. Its increasing row forces 64 base copies and
at most eight of those in a color. At most 21 additional copies leave at
most 29 vertices in any color. Each color supports at most 14 times its
number of vertices in unsplit two-vertex rows. Their total is at most
1190, while the path support bound of 2689 requires at least 1343.
This gives an [obstruction to coloring all the incidences](OnlineReachabilityPreservers/IncidenceColorBudgetAudit.lean#L249)
under the two support bounds and the original length cap. The
[independent frozen witness](OnlineReachabilityPreservers/IncidenceColorBudgetAudit.lean#L261)
retains at least \(M/8\) for these original counts and mass.

The [two-layer example](OnlineReachabilityPreservers/LayeredIncidenceColorAudit.lean#L91)
uses two length-64 rows on disjoint vertex layers and all 4096 cross
rows from the first layer to the second. The cross rows arrive in
lexicographic order by source and then target, before the two long rows.
It respects one vertex order and excludes half-bridges at every cutoff.
The original upper length cap is 8. With at most 170 occupied vertex
copies, the two long rows force 128 base copies and at most 16 per
color. The 42 remaining copies allow at most 58 vertices per color. A
color with \(a,b\) vertices from the two levels supports at most
\(ab\le15(a+b)\) monochromatic cross rows, so at most 2550 cross rows
are monochromatic. The path support bound of 5464 requires at least
2728. This [obstruction](OnlineReachabilityPreservers/LayeredIncidenceColorAudit.lean#L274)
therefore applies even to common-order half-bridge-free input. The
[separate frozen witness](OnlineReachabilityPreservers/LayeredIncidenceColorAudit.lean#L287)
for \(n=128,p=4098,M=8320\) retains at least \(M/8\) and excludes full
bridges through any requested cutoff. General cyclic frozen-average
statements at the remaining cutoffs stay open.

Under half exclusion through size three, a pair of paths that share two
vertices must compare them in opposite directions. At a shared vertex
\(v\), put an edge from an earlier path to a later one if some \(u\)
precedes \(v\) in the earlier path and follows \(v\) in the later path.
Each path has [at most one such outgoing partner](OnlineReachabilityPreservers/ReverseIntersectionCopies.lean#L23)
at \(v\). Assigning opposite colors along these edges is possible by
recursing from later to earlier paths. The
[vertex-only split](OnlineReachabilityPreservers/ReverseIntersectionCopies.lean#L123)
keeps all incidences and makes intersections unique. It preserves
[full exclusion at any cutoff](OnlineReachabilityPreservers/ReverseIntersectionCopies.lean#L91)
and [half exclusion through four](OnlineReachabilityPreservers/ReverseIntersectionCopies.lean#L96).
Choosing one color separately at each vertex, and taking the complementary
choices, instead partitions the original incidences into two subfamilies
with unique intersections and no extra paths or vertices.
[Rowwise mass identity](OnlineReachabilityPreservers/ReverseIntersectionCopies.lean#L142)
· [Unique intersections](OnlineReachabilityPreservers/ReverseIntersectionCopies.lean#L162).
For simple inputs with positive budgets and mass \(M\) at least both
budgets, [frozen cleaning](OnlineReachabilityPreservers/ReverseIntersectionCopies.lean#L233)
retains \(M/16\) with both original budgets and all four original caps.
It preserves the selected input exclusion at cutoff four in either mode
or at full cutoff six. The occupied vertex copies plus the bound on
additional width blocks must fit within four thirds of the original
vertex budget. This includes
[inputs with at most \(n/16\) vertices having an outgoing partner](OnlineReachabilityPreservers/ReverseIntersectionCopies.lean#L299).

[Quadratic trimming of both supports](OnlineReachabilityPreservers/FrozenQuadraticTrimming.lean#L225)
starts with a subsystem within the original budgets, with mass \(K\)
between \(9M/16\) and \(M\). Its splits at the original factor-four
widths must preserve the chosen bridge exclusion. All nonfinal blocks
have full width and are kept. Trimming among the final blocks costs at
most \(K^2/(6M)\) because the width times its budget is at least \(3M\)
in each dimension. At least \(261M/512\)
remains before peeling, so the cleaned mass is at least \(M/104\) with
both original budgets and all four caps. If the vertex-only split uses
at most \(16n/9\) copies, the [heaviest original-budget set](OnlineReachabilityPreservers/FrozenQuadraticTrimming.lean#L280)
retains the needed nine sixteenths. The unique intersections justify
the width splits at cutoff four in either mode or at full cutoff six,
with the corresponding input exclusion. A sufficient condition is that
[at most seven ninths of the original vertices have outgoing reverse partners](OnlineReachabilityPreservers/FrozenQuadraticTrimming.lean#L353).

[Half-budget width splits](OnlineReachabilityPreservers/FrozenMatchedPartners.lean#L98)
use a subsystem of simple paths within the original vertex budget and at
most half the original path budget. When it carries \(K\) between
\(7M/16\) and \(M\)
and its splits at the original widths preserve the required exclusion,
the path pieces already fit the original budget. The path peeling charge
is at most \(M/8+K/12\). Trimming the vertex dimension and peeling at the
original averages retain at least \(M/104\) within both budgets and all
four caps.

If all reversed comparisons between simple paths occur within disjoint
pairs, keeping the heavier row in each pair makes intersections unique.
When the paired rows hold at most \(7M/8\), keeping the unpaired rows as well gives at
least \(9M/16\) for quadratic trimming of both supports. When the paired
rows hold more than \(7M/8\), their selected rows alone give at least
\(7M/16\) in at most half the original path budget. This proves
[frozen cleaning for matched reverse partners](OnlineReachabilityPreservers/FrozenMatchedPartners.lean#L207)
with at least \(M/104\), both original budgets, and all four original caps.
It preserves the input exclusion at cutoff four in either mode or at full
cutoff six, for positive budgets and mass at least both counts.

The [two-class theorem](OnlineReachabilityPreservers/FrozenMatchedPartners.lean#L323)
gives the same original budgets, caps, retention and cutoff guarantees
when simple paths can be partitioned into two classes with every reversed
comparison crossing classes. Each class has unique intersections under
the matching input bridge exclusion. A class with mass at least
\(9M/16\) permits trimming both supports. If both are below that mass,
each carries at least \(7M/16\) and one uses at most half the original
path budget.

A repair may delete at most \(M/24\) incidences as sublists of the original
rows before assigning every remaining reversed comparison across two classes.
Beyond the low-mass cases, each rounded width times its budget is at least
\(31M/8\). A single class of mass at least \(13M/24\) pays for quadratic
trimming on both sides, or each class has mass at least \(5M/12\) and the one
with fewer rows can keep all its path pieces. Either proof gives at least
\(M/288\), with both budgets and all four caps at the original averages.
The same thresholds apply at cutoff four in either mode and at full cutoff
six. A filter can perform the repair by dropping the later vertex of a
reversed comparison in its earlier row whenever the rows share a class.
The hypothesis counts removed incidences. Also, a unique sublist family
of mass at least \(13M/24\) suffices by itself. Opposite-intersection
pruning supplies such a family whenever the opposite-link count is at most
\(11M/24\).
[Repaired classes](OnlineReachabilityPreservers/FrozenMatchedPartners.lean#L529)
· [Unique sublists](OnlineReachabilityPreservers/FrozenMatchedPartners.lean#L566)
· [Opposite-link bound](OnlineReachabilityPreservers/FrozenMatchedPartners.lean#L582).

At half cutoff five, two row classes after repair suffice when all
remaining reversed comparisons cross between classes and the combined
mass is at least \(6M/7\). Width splitting within one class preserves
half exclusion through size five. Keeping all path pieces in budget before
peeling, or using a single large class with quadratic trimming on both
sides, gives mass at least \(M/288\) with both original budgets and all four
starting-average caps. The criterion also applies when the same-class
reverse-end filter removes at most \(M/7\) incidences.
[Two repaired classes at half cutoff five](OnlineReachabilityPreservers/FrozenMatchedPartners.lean#L770)
· [Same-class deletion budget](OnlineReachabilityPreservers/FrozenMatchedPartners.lean#L903).

The same conditional half-five conclusion holds in the literal convention
with distinct nonempty input and output rows. A bipartite graph on row
labels in which adjacency means a reversed comparison supplies the classes
without any repair. A forest on these row labels is a sufficient case.
[Literal two-class witness](OnlineReachabilityPreservers/LiteralFrozenHalfFive.lean#L14)
· [Row reversal graph](OnlineReachabilityPreservers/LiteralFrozenHalfFive.lean#L44)
· [Bipartite sufficient condition](OnlineReachabilityPreservers/LiteralFrozenHalfFive.lean#L53).

If an eligible family has \(s\) nonempty paths, opposite-intersection
pruning keeps at least \((M+s)/2\) incidences. It meets the \(13M/24\)
threshold whenever \(M\le12s\). For the unrestricted extremum at positive
budgets, replacing an empty row with a singleton would increase the mass
and leave all bridge steps unchanged, so every row is nonempty. The
ordered-pair bound gives \(M^2\le p(2n(n-1)+M)\). When
\(n(n-1)\le66p\) it implies \(M\le12p\), giving both original budgets,
all four original-average caps, and at least \(M/288\) at half cutoff
four and full cutoffs four and six.
[Cleaning at a large path budget](OnlineReachabilityPreservers/FrozenManyRows.lean#L39).

Counting all ordered comparisons also controls the loss from clipping
paths at the original width \(L=\lfloor4M/p\rfloor\). With half exclusion
through size two, the sum of \(\ell_i(\ell_i-1)\) is at most
\(2n(n-1)\). If \(T=\sum_i(\ell_i-L)_+\), the clipping inequality gives
\((4L-2)T\le2n(n-1)\). When \(M>8\max(n,p)\), \(p\le227\) or
\(n(n-1)\le235p\) suffices for \(15T\le7M\). The low-mass construction
covers the other density branch. Clipping keeps a sublist of every row,
and splitting vertices preserves full exclusion at any input cutoff.
With positive budgets this yields all four original-average caps, both
original budgets, and \(M/104\) of the unrestricted maximum at every full cutoff of at
least two and half cutoffs two through four.
[Squared lengths and frozen clipping](OnlineReachabilityPreservers/FrozenClippingBudgets.lean).

For half exclusion through size three, the degree-side count satisfies
\(\sum_v d_v(d_v-1)\le p(p-1)+2M\). For each pair of rows, every common
vertex after the first in the earlier row charges that row's incidence
at the vertex. It has at most one later reverse partner. The ordered
pair count uses both orientations. Capping each vertex's occurrences
keeps the earliest rows at that vertex and removes exactly the excess
degree. When \(M>8\max(n,p)\), the original length and degree excesses
\(T,Y\) obey \(488T\le Mp\) and \(1008Y\le M(p+16)\). In terms
of the vertex budget they also satisfy \(504T\le Mn\) and
\(976Y\le M(n+16)\). Either \(n\le157\) or \(p\le156\) gives
the combined bound \(104(T+Y)\le51M\).
Clipping both sides and peeling retain at least \(M/104\)
with both original budgets and all four original-average caps. The
low-mass witness and size-two case give the rest of the stated range.
With positive budgets the conclusion holds for the unrestricted maximum
at every full or half cutoff of at least two.
[Degree counting and two-sided clipping](OnlineReachabilityPreservers/FrozenDegreeClipping.lean).

Applying Cauchy--Schwarz to the degree count gives
\(M^2\le n(p(p-1)+3M)\) at half cutoffs of at least three. Together with
the row bound \(M^2\le p(2n(n-1)+M)\), this gives an \(M/8\) witness
relative to the unrestricted maximum with both original budgets and
all four original-average caps. The positive budgets must satisfy
\(n(n-1)\le28p\) at an input cutoff of at least two or
\(p(p-1)\le40n\) at an input cutoff of at least three. The input may
use either mode. The low-mass proof chooses full exclusion through the
original vertex count, which covers every bridge size because a bridge
has distinct vertices.
[Unbalanced budget bounds](OnlineReachabilityPreservers/FrozenUnbalancedBudgets.lean).

The [extremal rectangle bound](OnlineReachabilityPreservers/ExtremalCopyBounds.lean)
uses the same indexed path convention. If a restriction to \(A,B\) has
mass \(m\) and \(t|A|\le n,\ t|B|\le p\), then \(tm\le M\) at the
unrestricted maximum. Disjoint copying and empty padding preserve both
bridge exclusions at every cutoff. The rectangle of rows and vertices
above their original upper caps fits four copies, so its mass is at
most \(M/4\). The two separate clipping losses still require bounds.

In half mode with positive budgets, \(p\le n\) and \(p(p-1)\le108n\)
suffice at every input cutoff of at least three. The squared-degree
inequality gives \(M\le12n\). In the range \(M>8n\) it also gives
\(16n\le p^2\), which lets a square grid of width
\(\lceil M/(4p)\rceil\) fit both budgets. The grid has degree three and
a fixed arrival order with all horizontal paths before vertical paths.
Disjoint copies meet all four frozen caps and retain at least \(M/8\)
of the unrestricted maximum. Both this construction and the low-mass
branch give one witness excluding half-bridges at every size.
[Half-bridge grid cleaning](OnlineReachabilityPreservers/HalfGridCleaning.lean).

The [grid in arbitrary dimension](OnlineReachabilityPreservers/AxisGridCleaning.lean)
gives an \(M/8\) witness with the original caps and all-size half
exclusion under the following explicit budget conditions. For positive
\(n,p\), \(2n\le M\), and \(p\le M\), write
\(D=\max(2,\lceil M/(4n)\rceil)\) and \(w=\lceil M/(4p)\rceil\).
A block fits if \(w^{D-1}\le n\) and \(D w^{D-2}\le p\).
The proof checks the degree \(D\), length \(w\), the arrival order of
the two directions along the last coordinate, and the two exact
rounded block counts. The same witness covers every requested half
cutoff. The constraints allow the degree and path length to grow
together.

The [finite-budget cases](OnlineReachabilityPreservers/FrozenBoundaryCases.lean)
give an exact \(np\) maximizer meeting all four caps with either
empty budget or a cutoff below two, in the indexed convention. At a
cutoff below two with feasible positive literal budgets, \(\min(p,n!)\)
distinct spanning rows retain at least \(M/3\) with both original budgets
and the four caps at the starting and witness averages in either mode.
[Literal short-cutoff construction](OnlineReachabilityPreservers/LiteralShortCutoff.lean#L121).
With positive budgets and cutoff at most three, the previously checked
split-and-peel witness is relabeled on finite ordinals with both
budgets, the four original caps, and \(M/16\) in either mode.
When \(k\ge\min(n,p)\), both injective labels in a bridge certificate
show that full exclusion through \(k\) is all-size exclusion. The
all-size construction gives \(M/40\) of that unrestricted maximum,
using both original budgets and all four original caps.

For cutoffs below the smaller support, keeping the heaviest \(k\)
vertices or rows of that support rules out every full bridge. If
\(a\min(n,p)\le bk\) with \(a\le b\), its retained mass \(K\) satisfies
\(aM\le bK\). At \(28k\ge27\min(n,p)\) and \(k\ge2\), this gives
\(M/128\) with the original-average caps and the original finite cutoff.
If \(Ck\ge\min(n,p)\) for a positive integer \(C\), output-average
cleaning gives \(M/(523C)\) and all-size full exclusion under the indexed
convention. The feasible literal transfer at \(k\ge2\) gives
\(M/(9414C)\) with distinct nonempty rows and all-size full exclusion.
Both caps conventions respect the original budgets and apply at the
corresponding full maxima for positive budgets.
[All-size restriction](OnlineReachabilityPreservers/FrozenFullNearCutoff.lean#L32)
· [Mass ratio](OnlineReachabilityPreservers/FrozenFullNearCutoff.lean#L86)
· [Indexed original-average maximum](OnlineReachabilityPreservers/FrozenFullNearCutoff.lean#L145)
· [Literal original-average maximum](OnlineReachabilityPreservers/FrozenFullNearCutoff.lean#L159)
· [Indexed output-average maximum](OnlineReachabilityPreservers/FrozenFullNearCutoff.lean#L239)
· [Literal all-size output-average maximum](OnlineReachabilityPreservers/FrozenFullNearCutoff.lean#L306).

A logarithmic output-average bound holds at arbitrary full cutoffs, with
both original budgets and full exclusion through the original cutoff.
Use the largest of at most \(2(1+\lfloor\log_2 n\rfloor)\) groups of
comparable lengths. Each group's upper length bound is at most three
halves of each of its row lengths. In a dense group, only degree splitting is needed.
A quadratic trimming bound and the two peeling charges leave one
sixteenth of the group mass. A spanning row handles the other case.
The retained fractions at the indexed and the feasible literal full
maxima have denominators \(32(1+\lfloor\log_2 n\rfloor)\) and
\(576(1+\lfloor\log_2 n\rfloor)\), respectively, with \(k\ge2\) for
the literal transfer. The uniform constant-factor claim remains open.
[Degree splitting in a length group](OnlineReachabilityPreservers/FullLengthBucketCleaning.lean#L15)
· [Indexed logarithmic bound](OnlineReachabilityPreservers/FullLengthBucketCleaning.lean#L237)
· [Literal logarithmic bound](OnlineReachabilityPreservers/FullLengthBucketCleaning.lean#L270).

For simple input excluding full bridges through \(k\) with positive
budgets and \(M\ge\max(n,p)\), use a restriction of mass \(K\) on \(b\) row
labels with length at most the original upper cap. Splitting vertices at the
original width, trimming and peeling give the original-average caps
whenever \(M/r\le K-K^2/(12M)-M/4-Mb/(4p)\) for a positive integer \(r\).
With every row truncated
at the upper cap, retaining \(3M/5\) gives a witness of mass at least
\(M/16\), and retaining \(8M/15\) gives at least \(M/128\). Both original
budgets and the original cutoff hold. In the literal case \(k\ge2\),
feasible distinct nonempty input gives distinct nonempty output.
[Charge inequality](OnlineReachabilityPreservers/FrozenFullLengthCapped.lean#L14)
· [Indexed full truncation](OnlineReachabilityPreservers/FrozenFullLengthCapped.lean#L84)
· [Literal full truncation](OnlineReachabilityPreservers/FrozenFullLengthCapped.lean#L135).

For the indexed maxima at the same positive budgets, put
\(q=\min(n,p)\). The finite and all-size full masses satisfy
\(\min(k,q)\beta_k\le q\beta_\infty\le q\beta_k\). It follows by selecting
the heaviest \(\min(k,q)\) labels of the smaller support and then using
maximality in each direction. The result concerns mass without cleaning
caps.
[Comparison of the indexed full extrema](OnlineReachabilityPreservers/FrozenFullNearCutoff.lean#L327).

With \(6k\ge5\min(n,p)\) and \(k\ge2\), the original-average
witness keeps at least \(M/256\) within both original budgets. In the
high-mass case with larger budgets, select at most
\(\lceil5\min(n,p)/6\rceil\) labels on the smaller side, then
use its reduced support count after making the rows increasing. The
original widths and peeling thresholds still use the starting mass and
counts. The indexed and feasible literal maximum have the same bound
and full exclusion through the input cutoff. For the narrower range
\(28k\ge27\min(n,p)\), the earlier \(M/128\) bound still applies.
[Original-average construction](OnlineReachabilityPreservers/FrozenFullSupportFraction.lean#L241)
· [Indexed maximum](OnlineReachabilityPreservers/FrozenFullSupportFraction.lean#L289)
· [Literal maximum](OnlineReachabilityPreservers/FrozenFullSupportFraction.lean#L303).

The stronger range \(4k\ge3\min(n,p)\) gives the same \(M/256\) bound
for positive budgets and \(k\ge2\). In the larger high-mass case, the
shorter support starts at most \(19/25\) of its original size, and the
increasing rows retain mass \(K\ge M/2\). At \(K\ge7M/12\) use the
support ratios above. At the lower masses, the smaller support fits after
the width split and the other support loses at most \(7K/186\) in a
quadratic trim. The actual support sizes charge at most
\(11M/25+2K/31\) for peeling. Both original budgets and all four frozen
caps hold at the input cutoff for indexed and feasible literal maxima.
[Original-average construction](OnlineReachabilityPreservers/FrozenFullSupportFraction.lean#L483)
· [Indexed maximum](OnlineReachabilityPreservers/FrozenFullSupportFraction.lean#L561)
· [Literal maximum](OnlineReachabilityPreservers/FrozenFullSupportFraction.lean#L575).

Start with simple input excluding full bridges through \(k\) and positive
budgets. Let \(q=\min(n,p)\), \(s\le k\) be the retained size on the
smaller side, and \(t=s/q\). Charge the common-order deletion against \(v=s\) when
\(n\le p\), and against \(v=n\) otherwise. The original-cap criterion
uses \(t\le19/25\), \(M\ge8\max(n,p)\), \(r\ge256\), and
\(M/r+(1+t)M/4\le(167/186)(tM-2v)\). The resulting indexed and distinct
nonempty witnesses retain \(M/r\) within both budgets and exclude every
full bridge. For \(k\ge2\) and \(M\ge\max(n,p)\), the indexed and feasible
literal witnesses at the input cutoff retain \(M/512\) with the same four original caps when
\(n\le p\) and \(5k\ge3n\), or when \(5k\ge2\min(n,p)\) and \(M\ge256n\).
[All-size indexed margin](OnlineReachabilityPreservers/FrozenFullSupportFraction.lean#L597)
· [All-size literal margin](OnlineReachabilityPreservers/FrozenFullSupportFraction.lean#L680)
· [Indexed cutoff and density guarantee](OnlineReachabilityPreservers/FrozenFullSupportFraction.lean#L702)
· [Literal cutoff and density guarantee](OnlineReachabilityPreservers/FrozenFullSupportFraction.lean#L773).

The [quarter-count example](OnlineReachabilityPreservers/AverageSplitAudit.lean#L430)
has \(n=40\), \(p=14\), and \(M=73\), with full exclusion at every size
and nonempty simple rows. At the prescribed widths \(7\) and \(20\) it
marks at least 19 starts. The [same input has a clean witness](OnlineReachabilityPreservers/AverageSplitAudit.lean#L447)
at the original averages from the low-mass construction.

The [clipped partition theorem](OnlineReachabilityPreservers/ClippedVertexPartitions.lean#L127)
averages over common vertex assignments to \(q\) parts. An ordered pair
of distinct vertices shares a part in one \(q\)-th of the assignments.
A piece of length \(x\) supplies \(x(x-1)\) such ordered pairs, enough
to pay \((4L-2)(x-L)\) when it is clipped at \(L\). With room for
one piece per selected path and part, retaining three quarters of the
original mass after this loss is sufficient for the
[frozen cleaning conclusion](OnlineReachabilityPreservers/ClippedVertexPartitions.lean#L199).
It preserves full exclusion at any cutoff. For half exclusion it uses
the safe degree split through size four or already capped degrees.

For any simple graph, take the two orientations of each edge as paths
of two vertices. The [dart family](OnlineReachabilityPreservers/OppositeLinkForest.lean#L1041)
excludes full bridges through a cutoff exactly when the graph's girth
exceeds that cutoff. Its [opposite-link graph](OnlineReachabilityPreservers/OppositeLinkForest.lean#L1022)
is the original graph, and its [incidence mass](OnlineReachabilityPreservers/OppositeLinkForest.lean#L1059)
is four times the number of edges in the finite case. Thus every graph
of girth greater than four occurs as an opposite-link graph for half
exclusion through four. With positive budgets and mass at least both
counts, these two-vertex paths already fall in the low-mass cleaning regime.

The [finite field construction](OnlineReachabilityPreservers/OppositeLinkDensity.lean#L120)
uses points and nonvertical lines over a prime field of order \(q\).
This graph has \(2q^2\) vertices and at least \(q^3\) edges. Two
distinct points lie on at most one common line, which excludes
four-cycles, and bipartiteness excludes triangles. For every constant
\(C\), a sufficiently large prime gives a simple indexed half-four
family with two vertices per path and \(E>Cn\) opposite links. Its
mass is \(2p\), and it falls in the low-mass cleaning regime.

The [nested link set](OnlineReachabilityPreservers/NestedOppositeCleaning.lean#L23)
contains only links reversed by a later path inside a larger interval
reversed by a distinct partner of the central path. It is a subset of
the opposite-link graph's edges and is empty when every path has at
most three vertices. The [pruning proof](OnlineReachabilityPreservers/NestedOppositeCleaning.lean#L70)
deletes the later start of each marked link. If a nested reversal
would survive across multiple original links, its first link still
marks that start. The [incidence bound](OnlineReachabilityPreservers/NestedOppositeCleaning.lean#L92)
charges each deleted incidence to a distinct marked link. For simple
half-four-free input with positive budgets and mass \(M\) at least both
counts, [frozen cleaning](OnlineReachabilityPreservers/NestedOppositeCleaning.lean#L147)
now suffices when this subset has at most \(M/8\) links. It retains at
least \(M/32\), keeps both budgets, and meets the four caps at the
original averages.

| Source | Mathematical obligation |
| --- | --- |
| Definition 2 | Half-\(k\)-bridge-free means no bridge of size at most \(k\) whose last arc precedes the river. |
| Lemmas 23 and 39 | [Acyclic cleaning](OnlineReachabilityPreservers/BalancedRegularization.lean) checks both original budgets, all four degree and length caps, and retention of at least one sixteenth of the original mass when the mass is at least both original counts. It preserves the bridge exclusions at every size. [Local cleaning](OnlineReachabilityPreservers/LocalBalancedRegularization.lean) gives the same budgets and caps through size four under unique intersections and through size three for arbitrary simple paths with mass at least both counts. For simple paths excluding half-bridges through size four whose mass is at least twice both counts, [opposite-intersection pruning](OnlineReachabilityPreservers/OppositeIntersectionPruning.lean) followed by local cleaning gives both original budgets, at least one thirty-second of the mass, lower caps at one eighth of the original averages and upper caps at four times those averages. It preserves the half exclusion and preserves full exclusion when the input has it. The [pruning bound with first incidences](OnlineReachabilityPreservers/OppositeIntersectionPruning.lean) retains at least \((M+s)/2\) incidences, where \(s\) is the number of original nonempty paths. At a maximum with positive vertex budget, \(s=p\). [Two opposite rows](OnlineReachabilityPreservers/OppositePruningGain.lean) attain equality for every positive vertex count. If every original path is nonempty, the pruned paths satisfy both upper caps, and the original mean path length is at most \(C\), the [frozen peeling argument](OnlineReachabilityPreservers/LocalFrozenCleaning.lean) yields both budgets, all four original-average caps, and retention at least \(M/(2C)\). [Output-average cleaning](OnlineReachabilityPreservers/LocalAverageCleaning.lean) gives a witness at the unrestricted size-four maximum in either bridge mode. It meets both budgets, retains at least one 392nd of the maximizing mass, and keeps all four factor-four caps relative to the witness's averages. [Full-bridge cleaning with frozen averages](OnlineReachabilityPreservers/LocalFrozenCleaning.lean) retains at least one 119th of the maximum without unique intersections, within both original budgets and all four original-average caps at full bridge cutoffs three through five. When the mass lies between the larger budget and eight times it, the [low-mass witnesses](OnlineReachabilityPreservers/LocalFrozenLowMass.lean) retain at least one eighth of the mass and meet both budgets and all four original-average caps. They exclude every full bridge, and apply to both modes for simple families excluding half-bridges at a cutoff of at least two. This includes every unrestricted maximum when either positive budget is at most eight. [Length truncation](OnlineReachabilityPreservers/LocalFrozenCleaning.lean) and [a common vertex partition](OnlineReachabilityPreservers/VertexPartitionCleaning.lean) give both budgets, all four frozen caps and mass at least \(M/16\) when the length-capped subsystem fits both original budgets and still has at least \(3M/4\) incidences. Keeping the pieces of a common partition preserves both bridge exclusions at every cutoff. The subsequent vertex split is justified for full bridges at every cutoff and for half-bridges through size four. Already capped degrees also suffice at any cutoff. Both shared partitions can also be applied together. The [occupied-support cleaning theorem](OnlineReachabilityPreservers/CommonPartitionCleaning.lean) preserves mass and both exclusions at every cutoff while splitting every incidence by its path and vertex parts. It counts only occupied copies and pieces, using the number of incident parts of each original vertex and each original path. If the full mass meets the two upper caps after partitioning and each occupied support fits within four thirds of its original budget, a restriction to both budgets has all four frozen caps and at least \(M/16\) mass. The common-partition proof also gives an explicit grouping criterion in terms of occupied input supports, upper-cap capacities, and the numbers of opposite groups. [Ordered-path cleaning](OnlineReachabilityPreservers/ContiguousHalfCleaning.lean) retains \(M/16\) and all four frozen caps through size four by splitting, restriction, and peeling for simple paths with positive budgets and mass at least both counts, when there are no two distinct partners reversing strictly nested intervals with the inner partner later than the split parent. For any fixed ordered disjoint split, half-4 exclusion is equivalent to the absence of a nested reversal whose required four steps all survive in the pieces. [Synchronized cleaning](OnlineReachabilityPreservers/LocalFrozenCleaning.lean) keeps both budgets, all four original caps and at least \(M/119\) for simple systems with a half cutoff from three through five that also exclude full bridges through size three. A collision under the degree-split projection would erase at least two steps and leave a forbidden full bridge. Mirrored path cuts then preserve the half exclusion up to size five. The [average-width examples](OnlineReachabilityPreservers/AverageSplitAudit.lean) exhibit the failure after the printed mean-width midpoint procedure terminates and after the exact factor-four-width block split. The same audit proves that every arrival permutation of one fully bridge-free family still has the nested obstruction. The [unrestricted half-four witness](OnlineReachabilityPreservers/FrozenHalfFourCleaning.lean) retains at least \(M/5000\) under the frozen caps and both original budgets. The unrestricted full-six witness retains at least \(M/5000\) under the same caps and budgets. Unrestricted half cleaning at the starting averages stays open at cutoffs of at least five. At the witness's own averages it stays open at cutoffs of at least six. At larger full cutoffs, [support restriction](OnlineReachabilityPreservers/FrozenFullSupportFraction.lean#L561) gives the original caps when \(4k\ge3\min(n,p)\). At a fixed positive fraction of the smaller budget, it also gives [output-average caps](OnlineReachabilityPreservers/FrozenFullNearCutoff.lean#L239). At arbitrary full cutoffs, a [logarithmic loss](OnlineReachabilityPreservers/FullLengthBucketCleaning.lean#L237) suffices for the four output-average caps. The general constant-factor claims at the remaining finite cutoffs of at least seven stay open. The printed path split can create a [half-7-bridge with unique intersections](OnlineReachabilityPreservers/UniqueSplitAudit.lean). The degree split can create a [half-5-bridge without unique intersections and a half-6-bridge with unique intersections](OnlineReachabilityPreservers/VertexSplitAudit.lean). The same split preserves full exclusion at all sizes. |
| Definition 3 and Lemma 24 | In a triple of distinct path indices, the middle path meets \(\pi_1\) before meeting \(\pi_3\), with \(\pi_3\) earlier in arrival order than the middle path. [CyclicIntersections](OnlineReachabilityPreservers/CyclicIntersections.lean) proves the fiber bound for arbitrary simple paths and the left and right order properties when a witness is chosen for each middle path. The right order becomes strict under full bridge-freeness. Multiple witnesses for one middle path can occur. [IntersectionOrder](OnlineReachabilityPreservers/IntersectionOrder.lean) proves uniqueness under a common vertex order for the incidence counts downstream. |
| Lemmas 25–27 | The corrected tail inequality is checked in [SourceAudit](OnlineReachabilityPreservers/SourceAudit.lean). [GeneralInitial](OnlineReachabilityPreservers/GeneralInitial.lean) proves the chain lower count for distinct path triples and the initial \(O(n+(np)^{2/3}+p)\) incidence bound for arbitrary ordered simple paths. Opposite-intersection pruning provides unique witnesses before counting, and every retained triple is a triple in the original paths. [PairwiseInitial](OnlineReachabilityPreservers/PairwiseInitial.lean) uses the same threshold argument in the common-order case. |
| Lemma 28 | Close pairs in the ordered \(R\)-fibers charge into sampled branching subsystems. For \(\ell\ge h\ge Cp/(\ell d^2)\), the mean \(Q\)-count is \(\Omega(h\sum_R\lvert R\rvert^2/(\ell p))\). [LocalBranching](OnlineReachabilityPreservers/LocalBranching.lean) proves the finite lower comparison and its dense normalization for local path orders with unique intersections. Every online charge with its right endpoint on the base has its left start before that endpoint on the base. The full-bridge-free charges have both endpoints off the base. [BranchWindow](OnlineReachabilityPreservers/BranchWindow.lean) supplies the common scaling arithmetic. The right-side distance uses the two distinct middle paths. |
| Lemmas 29–31 | [Weak majorization](OnlineReachabilityPreservers/Majorization.lean) and its [integral version](OnlineReachabilityPreservers/IntegralMajorization.lean) are checked. [SecondMoment](OnlineReachabilityPreservers/SecondMoment.lean) proves the acyclic second-moment estimate with explicit constants from the inductive size bound on subfamilies. The proof sorts the path indices and bounds clipped powers. [LocalOffBaseMoment](OnlineReachabilityPreservers/LocalOffBaseMoment.lean) proves the same three-term estimate for actual induced vertex samples of simple lists under the subfamily bound, allowing different local orders. |
| Lemmas 32–33 | [LocalBranchingDegrees](OnlineReachabilityPreservers/LocalBranchingDegrees.lean) checks the count for all long paths in the actual predecessor subsystem and for the subset of base paths avoiding the fixed vertex. It gives the expected high-degree count for thresholds above the envelope constant and the deterministic incidence bound. Each path has its own order. The branching identity uses unique intersections. |
| Lemmas 34–36 | [LocalBranchingDegrees](OnlineReachabilityPreservers/LocalBranchingDegrees.lean) bounds \(Q_1\) by weighted middle-path squares in local orders. [LocalOffBaseMoment](OnlineReachabilityPreservers/LocalOffBaseMoment.lean) checks the dyadic triangle inequality and each sampled moment in the actual subsystems. [LocalOffBaseAverage](OnlineReachabilityPreservers/LocalOffBaseAverage.lean) proves the full off-base expectation. The cyclic source-membership inference in Lemma 35 has a [checked counterexample](OnlineReachabilityPreservers/SplitAudit.lean). [LocalOnBaseCounting](OnlineReachabilityPreservers/LocalOnBaseCounting.lean) handles on-base targets after a near predecessor via source-restricted suffixes. [LocalFullOnBaseCounting](OnlineReachabilityPreservers/LocalFullOnBaseCounting.lean) counts targets before a near predecessor via half-3 and half-4-bridge exclusions and combines both directions. With unique intersections, the uniform caps and the inductive envelope, [LocalOnlineAverage](OnlineReachabilityPreservers/LocalOnlineAverage.lean) proves both terms for all \(Q_2\) tuples and the full \(Q\) expectation with the paper's exponents and without logarithmic loss. |
| Lemma 37 and Theorem 38 | [OnlineBound](OnlineReachabilityPreservers/OnlineBound.lean) compares the lower and upper \(Q\)-bounds with \(h\asymp p/(\ell d^2)\), including \(h>\ell\) and \(h>d\). [OnlineArithmetic](OnlineReachabilityPreservers/OnlineArithmetic.lean) absorbs the two lower-order terms. [LocalOnlineBound](OnlineReachabilityPreservers/LocalOnlineBound.lean) proves the corrected update with unique intersections and all finite iterates for arbitrary simple paths with the half-bridge exclusion through four. [LocalOnlineLimit](OnlineReachabilityPreservers/LocalOnlineLimit.lean) proves the unrestricted limiting bound with a single slack function tending to zero in \(n\) and one constant uniform in both \(n\) and \(p\). [OnlineSharp](OnlineReachabilityPreservers/OnlineSharp.lean) gives the unrounded graph rate. |
| Lemmas 40–42 and Theorem 43 | [LocalOfflineCounting](OnlineReachabilityPreservers/LocalOfflineCounting.lean) proves Lemma 41's off-base branching uniqueness and injection into the sampled path pairs in local orders. [OfflineMoment](OnlineReachabilityPreservers/OfflineMoment.lean) checks the logarithmic moment from subfamily incidence bounds. [LocalOfflineMoment](OnlineReachabilityPreservers/LocalOfflineMoment.lean) applies it to the actual local-order samples. [OfflineArithmetic](OnlineReachabilityPreservers/OfflineArithmetic.lean) checks the three-term comparison with third term \(n^{1/(b+1)}p^{(2b+1)/(2b+2)}\). [LocalOfflineBound](OnlineReachabilityPreservers/LocalOfflineBound.lean) gives the unrestricted update and a constant uniform over all iterations. At the limit Theorem 43 holds for arbitrary simple paths with the exact exponent \(1/\sqrt2\) and zero exponent slack. |

For Lemmas 23 and 39, the [component-cut theorems](OnlineReachabilityPreservers/ComponentSplitCleaning.lean)
cover possibly cyclic simple paths whose visits to each strongly connected
component of the precedence graph have length at most \(\lfloor M/p\rfloor\).
For \(M\) at least both positive budgets, they retain \(M/16\) within both
original budgets and all four frozen caps. The full exclusion remains at
the input cutoff and can hold at every size. The half exclusion uses
the original parent order and also needs capped input degrees, cutoff at most
four, or full exclusion through two less than its cutoff.
The same bridge conclusions hold if each visit fits the larger limit
\(\lfloor4M/p\rfloor\). Counting adjacent pieces permits the larger
limit with \(M/54\) retention, both original budgets, and all four
frozen caps. If visits longer than that cap hold at most \(M/56\) of the
mass, [deleting the long visits](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1072)
preserves the bridge exclusions and leaves all remaining visits within it.
The original caps and both budgets still hold in a witness with at least
\(M/108\) mass, with the same degree condition in half mode.
An additional [ordered-cut criterion](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1333)
excludes returns across each cut within \(\max(0,k-3)\) precedence edges.
For fixed cutoff \(k\),
[no precedence cycle of length at most \(k-2\)](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1596)
implies this criterion. Half exclusion in the degree split itself only
needs the absence of cycles through \(k-3\). In either bridge mode the
resulting factor-four block cleaning
retains \(M/16\) for simple paths with mass at least both positive budgets,
with both budgets and all four original-average caps. The
[deletion variant](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1644)
retains \(M/32\) under the same original budgets and caps when rowwise
deletions of at most \(M/18\) incidences remove the short cycles. Longer
cycles may remain in both variants. The [width-cut condition](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1581)
requires the bounded-return exclusion only for pairs across the actual
factor-four cuts. The earlier half-bridge degree-split result uses one of the
[four sufficient conditions](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1550).
[A separate degree-split condition](OnlineReachabilityPreservers/BridgeVertexProjection.lean)
excludes walks of length at most \(\max(0,k-3)\) between distinct copies
of one vertex in the copied rows. This suffices because erasing closed
sections preserves the last arc whenever the terminal projected corner
is unique in the chain. With the width-cut condition it gives the
same [\(M/16\) guarantee](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1885).
The [actual-piece criterion](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2142)
tests for returns across the same width cuts using only strict comparisons
on copied pieces. It retains at least \(M/16\) within both original budgets
and all four frozen caps in both modes.
Half mode still requires a sufficient degree-split condition. The
[checked example](OnlineReachabilityPreservers/ActualPieceReturnAudit.lean)
passes the copied test at cutoff seven and fails the original test.
[The earlier-block degree test](OnlineReachabilityPreservers/BackwardCopyReturns.lean)
rules out only copied returns from later to earlier blocks of one
vertex within \(\max(0,k-3)\) steps. With the actual-piece width test
it gives the same \(M/16\) guarantee in half mode. The example has a
short forward return and passes the earlier-block test.
[Safe boundaries on the copied rows](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2236)
give \(M/54\) with both original budgets and all four frozen caps
when every run fits the factor-four width and the degree split
preserves the requested exclusion. If each run fits the original
mean path length rounded down, the bound is
[\(M/16\)](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2251).
The [same twelve-vertex example](OnlineReachabilityPreservers/ActualPieceReturnAudit.lean)
has an original run of length six and copied runs of length at most one.
[Removing long copied runs](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2352)
keeps the original degree labels and safe boundaries fixed.
When the removed runs hold at most \(M/56\), it gives \(M/108\)
with both budgets and all four frozen caps, under the same
degree-split premise in either mode.
[Clipping each run to the original width](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2530)
charges only its excess. The exact excess sum can replace the deleted
mass in the \(M/56\) condition and yields the same \(M/108\) retention guarantee,
both original budgets, and all four frozen caps.
[Targeted deletions from the fixed degree copies](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2620)
test the width cuts on the surviving paths. If those cuts pass and
at most \(M/18\) incidences were deleted, the result gives
\(M/32\) with both original budgets and all four frozen caps under
the same degree-split premise in either mode.
The [same two tests on retained degree copies](OnlineReachabilityPreservers/BackwardCopyReturns.lean#L249)
also work for half exclusion when the unmodified copies fail it.
Passing the earlier-block test certifies half exclusion on the retained
copied rows. Passing the width test preserves it on the resulting
pieces. The frozen guarantee stays \(M/32\) at loss at most \(M/18\).
Arbitrary monotone ranks at terminal incidences suffice for the
earlier-block proof. Require the copied rows to project to the original
vertex lists in order. With at most \(4n/3\) copy labels and original
degree caps, passing the two
return tests gives the same frozen \(M/16\) guarantee and both budgets.
[Ranked degree rows](OnlineReachabilityPreservers/BackwardCopyReturns.lean#L269).
Selected safe arrival gaps give one way to produce these ranks. The
first and last rows of a possible backward return must straddle a
chosen gap. Counting occupied labels and checking the copy loads and
actual path pieces gives the same frozen guarantee.
[Safe degree gaps](OnlineReachabilityPreservers/BackwardCopyReturns.lean#L447).
When each safe degree run fits the original mean degree rounded down,
packing by its start count ensures the degree and support bounds without
additional load or label-count hypotheses. The width-piece test still
applies to the resulting rows. [Packed degree runs](OnlineReachabilityPreservers/PackedDegreeGaps.lean#L236).

The path-side result starts with admissible simple copied rows of mass
\(M\) at least both positive budgets. The rows have at most \(4n/3\)
labels and meet the original degree cap. Choose path gaps with no
backward return of at most
\(\max(0,k-3)\) edges in the precedence graph of those rows. If every
run fits the original mean length rounded down, greedy packing keeps
both original budgets, all four frozen caps and at least \(M/16\) of
original mass in either bridge mode.
[Chosen path gaps](OnlineReachabilityPreservers/PackedDegreeGaps.lean#L274).

The two packings compose. The original simple rows exclude the chosen
bridges through \(k\) and their mass \(M\) is at least both positive budgets.
Choose degree runs of size at most \(\lfloor M/n\rfloor\) and then path runs of
size at most \(\lfloor M/p\rfloor\) on the resulting rows. Half mode requires
each chosen degree gap to pass the earlier-copy return test on the
original graph. In both modes the path test uses the full precedence
graph of the resulting copied rows.
Packing preserves the full original mass. Restricting the supports and
peeling give at least \(M/16\) with both budgets and all four frozen caps.
[Compose the two packings](OnlineReachabilityPreservers/PackedDegreeGaps.lean#L295).

The mean-run and factor-four run bounds can both fail. On \(2m-1\)
vertices, take one row of increasing even labels and the \(2m-2\) rows
\([i,i-1]\) for \(i>0\). The simple paths have unique intersections, mass
\(5m-4\), degree at most three, and full bridge exclusion at every cutoff.
At cutoff \(k\ge 5\), a two-edge return through an odd vertex crosses
each interior gap of the even row. Every safe choice leaves a run of
length \(m\). The prescribed degree stride keeps each vertex in copy block
zero, so the obstruction persists for every choice of degree gaps. For
\(m\ge 10\) the original upper width is at most nine. A separate low-mass
construction achieves the frozen caps, both budgets, and at least
\(M/8\) for \(m>0\) and \(k\ge 2\).
[Forced run after degree packing](OnlineReachabilityPreservers/ForcedPathReturnRuns.lean#L303) · [Separate frozen witness](OnlineReachabilityPreservers/ForcedPathReturnRuns.lean#L353).

A rank test on the actual pieces can handle those returns. The parent
rows exclude the selected bridges through \(k\). Every strict comparison
in a piece occurs in its parent. Require rank to increase weakly along
every surviving comparison and distinct pieces of one parent to have
disjoint sets of ranks. For a river
comparison that strictly increases rank, rule out a detour of at most
\(k-1\) edges in the precedence graph which omits that piece. Any bridge
through \(k\) would then stay at one rank. Its arc and river labels project
to distinct parent rows, preserving the cutoff in both modes when the
pieces retain parent arrival order. The forced-run family preserves both
exclusions in the standard contiguous blocks at each fixed width of at
least two. For
\(m\ge 10\) and \(k\ge 5\), the original-width split passes the rank test
and still contains the two-edge return across its first width cut.
[Rank test](OnlineReachabilityPreservers/BridgeRiverRanks.lean#L43) · [The original-width split](OnlineReachabilityPreservers/ForcedPathReturnRuns.lean#L560).

The rank condition has a finite component test. Start with the actual
piece comparisons. Add the reverse of each possible river comparison
whose endpoints have a detour of at most \(k-1\) edges in the graph
omitting that piece. A suitable rank exists exactly when different
pieces of one parent meet disjoint strongly connected components of
this graph. Start with simple paths of mass \(M\) at least both positive
budgets. If degree copying preserves the chosen exclusion and its
original-width pieces pass the component test, the cleaned witness meets
both budgets and all four frozen caps and keeps at least \(M/16\) in either
mode.
[Rank existence](OnlineReachabilityPreservers/RiverDetourComponents.lean#L99) · [Frozen cleaning from the component test](OnlineReachabilityPreservers/RiverDetourComponents.lean#L148).

Each bridge through \(k\) lies in one component of the constraint graph.
If different pieces of the same parent meet that component, test short
returns using only the vertices and comparisons in the component.
The return radius is \(\max(0,k-3)\) and the comparisons between pieces
use the copied parent rows. Start with simple paths, positive budgets and
mass \(M\) at least both budgets. With admissible degree copies, passing
this test at the two original widths preserves either bridge exclusion
and gives a frozen witness with mass at least \(M/16\), both budgets and
all four caps.
[Restriction proof](OnlineReachabilityPreservers/BridgeRiverRanks.lean#L103) · [Component return test](OnlineReachabilityPreservers/RiverDetourComponents.lean#L171) · [Frozen witness](OnlineReachabilityPreservers/RiverDetourComponents.lean#L192).

A separate projection works for disjoint pieces that may interleave
within their parent rows. Require each original comparison between
different pieces of the same parent to have no projected return within
\(\max(0,k-3)\) edges. The lift takes the detour after its last
visit to the river parent, then shortcuts other repeated parents
in their row order. It preserves the river parent and the last
arc parent, so the same cutoff holds in full mode and in half
mode when pieces follow their parents’ arrival order.
[Return condition](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2639) · [Bridge projection](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2649) · [Full bridge exclusion](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2762) · [Half-bridge exclusion](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2779).

For the vertex-copy step, the two copies of a repeated projected corner
must be nonconsecutive along the detour and cannot be the two river
endpoints. The first and last arcs of the closed projected part are on
distinct rows. The interior return takes at most \(\max(0,k-4)\) steps
in the original precedence graph. If the copies agree at the ends
of every such short return and all comparisons project to their original
rows, each bridge through the cutoff projects with distinct corners and
the same arc and river labels. This preserves either exclusion.
[Agreement of vertex copies](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2798) · [Lift with distinct projected corners](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2807) · [Preservation in either mode](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2871).

For simple rows admissible at the chosen cutoff, group the incident rows
at each vertex so the first and last rows of each tested short return are
together. Assume the groups
are disjoint and fit the degree width. Choose a valid partition with the
minimum number of groups and use the groups as copies. Every original
row is recovered by projection, each degree is within the width, and at
most one copy of each vertex is at or below half the width. For simple
input, the copies preserve the chosen full or half exclusion.
[Short-return pairs of incident rows](OnlineReachabilityPreservers/ShortReturnVertexPacking.lean#L14) · [Bounded degree groups](OnlineReachabilityPreservers/ShortReturnVertexPacking.lean#L21) · [Admissible capped degree copies](OnlineReachabilityPreservers/ShortReturnVertexPacking.lean#L140).

Start with simple rows whose mass \(M\) is at least both positive
budgets. If standard degree copying at the original width preserves
the cutoff, protect the endpoints of each row comparison with a
backward return through \(\max(0,k-3)\) in the copied precedence graph.
If each protected support fits the original path width, pack it
into block zero and keep the row order within each piece. This
keeps every incidence before trimming and yields the indexed
\(M/16\) witness with the cutoff, both budgets and all four frozen caps.
[Protected vertices](OnlineReachabilityPreservers/HalfFiveTerminalPacking.lean#L471) · [Preservation through the cutoff](OnlineReachabilityPreservers/HalfFiveTerminalPacking.lean#L499) · [Frozen witness at both original widths](OnlineReachabilityPreservers/HalfFiveTerminalPacking.lean#L528).

For simple rows already admissible at the given cutoff, the protected
endpoints can be placed in several groups per row. Assume a disjoint
partition within the path width, with both endpoints of every tested
comparison in one group. A minimum-cardinality partition has at most
one piece of length at most half the width per parent. Filtering each
row by its group keeps the original order, every incidence and every
vertex degree. It preserves the given full or half cutoff, with the
pieces in parent arrival order in half mode.
[Partition constraints](OnlineReachabilityPreservers/ShortReturnPiecePacking.lean#L107) · [Minimum-size partition](OnlineReachabilityPreservers/ShortReturnPiecePacking.lean#L89) · [Degree-preserving pieces](OnlineReachabilityPreservers/ShortReturnPiecePacking.lean#L295).

For simple input of mass \(M\) at least both positive budgets, apply
the grouping to admissible standard degree copies at the original
width. If each copied row admits the partition at the original path
width, the full degree blocks and the pieces above half the path
width give quadratic loss bounds for the two support trims. Their
individual losses are at most \(M/12\) and \(M/8\). After frozen peeling,
the indexed witness has mass at least \(M/4\), both budgets, all four
caps and the original full or half cutoff.
[Two support trims](OnlineReachabilityPreservers/FrozenQuadraticTrimming.lean#L154) · [Frozen quarter-mass witness](OnlineReachabilityPreservers/ShortReturnPiecePacking.lean#L410).

The two support trims also apply when the degree groups have varying
sizes. Assume simple admissible copies of mass \(M\) at least both
positive budgets, with all degrees within the original width. At most
\(n\) copy labels may have degree at or below half that width. If the
copied rows admit the short-return
path partition at the original path width, each support trim loses at
most \(M/8\). The later peeling uses the two original lower caps and
leaves a frozen witness of mass at least \(M/4\) within both budgets.
[Separate heavy-group thresholds](OnlineReachabilityPreservers/FrozenQuadraticTrimming.lean#L85) · [Frozen cleaning from both grouped profiles](OnlineReachabilityPreservers/ShortReturnVertexPacking.lean#L246).

The path-group bound can be checked on the original rows. Exact row
projection sends every copied return and its linked component to the
original graph. Projection is injective on each copied row, so its
component size cannot grow. For simple admissible input of mass \(M\)
at least both positive budgets, bounded degree groups at the original
degree width and original row components within the original path
width give a frozen \(M/4\) witness outright. Both budgets, all four caps
and the chosen cutoff hold in either exclusion mode.
[Component size does not increase under row copying](OnlineReachabilityPreservers/ShortReturnPieceComponents.lean#L160) · [Frozen cleaning under both original-width tests](OnlineReachabilityPreservers/ShortReturnVertexPacking.lean#L308).

The degree grouping premise has a finite component test too. For each
original vertex, connect any two incident rows that start and end a
tested short return there. A partition respecting those links exists
at the degree width exactly when each component fits. If both the
degree and path components fit their original widths, the on-input
tests give the frozen indexed quarter-mass witness at the chosen cutoff.
[Components and bounded partitions](OnlineReachabilityPreservers/ShortReturnPieceComponents.lean#L72) · [Graph of linked incident rows](OnlineReachabilityPreservers/ShortReturnVertexPacking.lean#L334) · [Exact degree component criterion](OnlineReachabilityPreservers/ShortReturnVertexPacking.lean#L356) · [Frozen witness from both finite tests](OnlineReachabilityPreservers/ShortReturnVertexPacking.lean#L374).

For distinct nonempty simple inputs with positive budgets and mass
\(M\) at least the vertex budget, the same tests apply at every
admissible cutoff of at least two. The literal transfer gives
a distinct nonempty witness of mass at least \(M/8\), within both original
budgets and all four original caps, preserving the chosen cutoff.
[Frozen cleaning for distinct nonempty paths](OnlineReachabilityPreservers/ShortReturnDistinctCleaning.lean#L10).

Restricting simple rows to sublists can only shrink the two component
graphs and their components. Delete each incidence for which either
original component exceeds its width. The restricted rows satisfy
both component bounds at those same widths. Retained mass plus the
number of deleted incidences equals the original mass. An incidence
with two oversized components contributes one to the loss.
[Exact mass of removed incidences](OnlineReachabilityPreservers/ShortReturnOverflow.lean#L92) · [Retained mass plus removed mass](OnlineReachabilityPreservers/ShortReturnOverflow.lean#L99) · [Both component bounds after deletion](OnlineReachabilityPreservers/ShortReturnOverflow.lean#L108).

The two support trims can use the smaller retained mass in their
quadratic loss bounds while keeping the original widths. For simple
admissible input of mass \(M\) at least both positive budgets, a
sublist restriction that retains at least \(2M/3\) and satisfies both
component tests at the original widths yields an indexed witness of
mass at least \(M/18\) with both budgets, the chosen cutoff and all four
frozen caps. In particular this applies when the original oversized
components account for at most \(M/3\) deleted incidences.
[Grouped width trimming after earlier losses](OnlineReachabilityPreservers/ShortReturnVertexPacking.lean#L222) · [Frozen witness from a two-thirds restriction](OnlineReachabilityPreservers/ShortReturnOverflow.lean#L158) · [Frozen witness from the overflow bound](OnlineReachabilityPreservers/ShortReturnOverflow.lean#L200).

Within a connected component, keep the first elements in the finite
order up to the prescribed width. Disjointness ensures that a component
of size \(s\) keeps exactly \(\min(s,w)\) elements at width \(w\). The loss
over all distinct components is the sum of their excesses above \(w\).
[Bounded selection from each component](OnlineReachabilityPreservers/ShortReturnPieceComponents.lean#L233) · [Exact selection size per component](OnlineReachabilityPreservers/ShortReturnPieceComponents.lean#L245) · [Mass lost to component excess](OnlineReachabilityPreservers/ShortReturnPieceComponents.lean#L268).

For simple rows, first clip each degree component to the vertex width
by keeping a bounded number of its row labels. Compute the path
components and clip them to the path width. Both component bounds
hold on the final sublists. The total loss is the degree excess on
the original rows plus the path excess after the degree restriction.
[Exact degree-component loss](OnlineReachabilityPreservers/ShortReturnComponentClipping.lean#L63) · [Exact path-component loss](OnlineReachabilityPreservers/ShortReturnComponentClipping.lean#L90) · [Successive clipping with both bounds](OnlineReachabilityPreservers/ShortReturnComponentClipping.lean#L146).

For simple admissible input with mass \(M\) at least both positive
budgets, compute the successive component excesses at the original
widths. If their sum is at most \(M/3\), the indexed frozen witness
has mass at least \(M/18\), both budgets, all four original caps and
the chosen cutoff. The same guarantee holds for literal distinct
nonempty input and output at cutoff at least two.
[Indexed excess criterion](OnlineReachabilityPreservers/ShortReturnComponentClipping.lean#L174) · [Literal excess criterion](OnlineReachabilityPreservers/ShortReturnComponentClipping.lean#L202).

For two fixed partitions of the same finite incidence set, a deleted
incidence can spend one unit of excess in both of its classes. A shared
deletion set may use at most the original excess in each class of either
partition. There is a deletion set meeting both fixed widths within a
given budget exactly when the total of the two excesses is at most
that budget plus the size of some shared deletion set. This comparison
uses the original class labels throughout.
[Exact criterion for two partitions](OnlineReachabilityPreservers/SharedCapacityClipping.lean#L87).

The maximum cardinality of a feasible shared set is attained over the
finite powerset. Its value is at most each separate excess sum.
A budget suffices exactly when it is at least the sum of the two
excesses minus that maximum, and a valid deletion set attains this count.
The labels and widths are fixed in the optimization.
[Maximum shared credit](OnlineReachabilityPreservers/SharedCapacityOptimum.lean#L30) · [Bounds on the credit](OnlineReachabilityPreservers/SharedCapacityOptimum.lean#L53) · [Budget equivalence](OnlineReachabilityPreservers/SharedCapacityOptimum.lean#L72) · [Attained minimum](OnlineReachabilityPreservers/SharedCapacityOptimum.lean#L91).

Apply the fixed-partition criterion to the degree and path components
of the original simple admissible rows. An incidence has one class on
each side. The two class-excess sums are the original short-return
excesses at the two widths. If a shared set spends at most each class's
original excess and the combined excess is at most
\(\lfloor M/3\rfloor\) plus its size, delete at most
\(\lfloor M/3\rfloor\) incidences to fit both original component widths.
The recomputed components on the retained rows fit as well. With
positive budgets and original mass \(M\) at least both budgets, this
gives a frozen \(M/18\) witness with the same cutoff, both budgets and
all four caps. Feasible literal distinct nonempty input also gives a
distinct nonempty witness at cutoff at least two.
[Degree class excess](OnlineReachabilityPreservers/ShortReturnSharedClipping.lean#L106) · [Path class excess](OnlineReachabilityPreservers/ShortReturnSharedClipping.lean#L119) · [Shared deletion certificate](OnlineReachabilityPreservers/ShortReturnSharedClipping.lean#L131) · [Indexed frozen witness](OnlineReachabilityPreservers/ShortReturnSharedClipping.lean#L224) · [Literal frozen witness](OnlineReachabilityPreservers/ShortReturnSharedClipping.lean#L245).

For simple input rows at a fixed cutoff, each recomputed degree or path
class after rowwise deletion lies within one original class. Total excess
on each side therefore cannot
increase at a fixed width. When deletions spend at most the original
excess in each class of both fixed partitions, the two fixed excess sums
decrease by exactly the number of deletions. Recomputing the components
reduces each excess by at least that much and can reduce it further by
splitting a class.
[Fixed-label accounting](OnlineReachabilityPreservers/SharedCapacityClipping.lean#L150) · [Excess under refinement](OnlineReachabilityPreservers/SharedCapacityClipping.lean#L167) · [Excess under sublists](OnlineReachabilityPreservers/ShortReturnExcessRefinement.lean#L63) · [Excess saved after recomputation](OnlineReachabilityPreservers/ShortReturnExcessRefinement.lean#L78).

An arbitrary rowwise restriction of simple admissible input can precede
component clipping. Compute both clips at the original widths after
the restriction. Charge the original mass lost in the first deletion,
the degree excess of the restriction and the path excess after degree
clipping. If the total charge is at most a third of the original mass,
the frozen witness keeps at least \(M/18\), the chosen exclusion and
all four caps within both original positive budgets. The original
mass must be at least both budgets. Using the two recomputed excesses
before either clip also suffices, since degree clipping cannot increase
path excess. The successive version gives a literal distinct nonempty
witness for feasible literal input at cutoff at least two.
[Exact successive excess expression](OnlineReachabilityPreservers/ShortReturnClippingAfterDeletion.lean#L10) · [Clipping after a restriction](OnlineReachabilityPreservers/ShortReturnClippingAfterDeletion.lean#L19) · [Both excesses before the clips](OnlineReachabilityPreservers/ShortReturnClippingAfterDeletion.lean#L46) · [Literal witness after a restriction](OnlineReachabilityPreservers/ShortReturnClippingAfterDeletion.lean#L75).

A seven-vertex spine with its six adjacent backward darts attaches at
vertex zero to a ten-leaf bidirected star. With padding for indexed
rows, the original budgets are 48 and 59, the mass is 59, and both
frozen widths are four. The rows exclude every full bridge. At cutoff
seven its center degree class has size 22 and the spine path class has
size seven. They share at most one incidence, so capping both original
classes requires at least 20 deletions, exceeding the one-third deletion
allowance of 19. Delete the incidence of vertex three on the reverse row from
four to three. The recomputed path excess is zero and the degree
excess is at most 18. The initial deletion and both clips now fit the
budget, giving a frozen \(M/18\) witness at any chosen full cutoff
within both original budgets and all four caps.
[Original widths](OnlineReachabilityPreservers/ShortReturnRecomputedExample.lean#L24) · [Original full exclusion](OnlineReachabilityPreservers/ShortReturnRecomputedExample.lean#L178) · [Fixed-class lower bound](OnlineReachabilityPreservers/ShortReturnRecomputedExample.lean#L436) · [Path excess after one deletion](OnlineReachabilityPreservers/ShortReturnRecomputedExample.lean#L215) · [Frozen full witness](OnlineReachabilityPreservers/ShortReturnRecomputedExample.lean#L256).

Arbitrary initial sublists can also precede the shared deletion test.
At the original widths, compute both component excesses on the
retained rows and choose a feasible shared set there. Add the initial
mass lost to the two new excesses, then subtract the shared set size.
If the resulting charge is at most \(\lfloor M/3\rfloor\), the frozen
witness retains at least \(M/18\) with the chosen exclusion, both
original positive budgets and all four caps. The simple admissible
original input must have mass at least both budgets. For feasible
literal distinct nonempty input, the retained witness can also be
distinct and nonempty at cutoff at least two.
[Each excess bounds the shared set](OnlineReachabilityPreservers/ShortReturnSharedClipping.lean#L171) · [Restriction at prescribed widths](OnlineReachabilityPreservers/ShortReturnSharedClipping.lean#L188) · [Shared excess after a restriction](OnlineReachabilityPreservers/ShortReturnSharedClipping.lean#L269) · [Literal recomputed shared witness](OnlineReachabilityPreservers/ShortReturnSharedClipping.lean#L307).

When differently labelled row families can meet only at one fixed
common vertex, any bridge stays within its river's family. The first and last
steps outside that family would require the shared vertex at two
different corners. Combining such families preserves either bridge
exclusion through any common cutoff with the original arrival order.
[Localize a bridge at a one-vertex intersection](OnlineReachabilityPreservers/BridgeAtJoint.lean#L13) · [Preserve both exclusions](OnlineReachabilityPreservers/BridgeAtJoint.lean#L56).

A checked shared-deletion instance attaches two reversed length-15
rows and a 10-leaf bidirected star at their common center. The original
budgets are 57 and 22, the mass is 70, and the two widths are four and
twelve. It excludes every full bridge. At cutoff seven the sum of the
original excesses is at least 24, above the deletion budget of 23.
There is a deletion set of size 22 that leaves all degrees at most four
and all lengths at most twelve. The fixed-partition equivalence gives
a shared certificate at every cutoff. This supplies a frozen
\(M/18\) witness with the chosen full cutoff, both original budgets
and all four caps.
[Original full exclusion](OnlineReachabilityPreservers/ShortReturnSharedExample.lean#L194) · [Original widths](OnlineReachabilityPreservers/ShortReturnSharedExample.lean#L202) · [Shared certificate at budget 22](OnlineReachabilityPreservers/ShortReturnSharedExample.lean#L264) · [Frozen full witness](OnlineReachabilityPreservers/ShortReturnSharedExample.lean#L281) · [Failure of separate excess charging](OnlineReachabilityPreservers/ShortReturnSharedExample.lean#L429).

For simple rows, standard degree copying preserves full exclusion
through any chosen cutoff. For such input that excludes full bridges
through the cutoff and has mass at least both positive budgets,
the original path-component bound alone gives the frozen quarter-mass
witness. A restriction retaining at least two thirds of the original mass and
passing the same path test also suffices for a frozen \(M/18\) witness.
In particular it suffices that original path excess is at most \(M/3\).
The latter conclusion has a literal distinct nonempty version at
cutoff at least two, with the same budgets, cutoff and four frozen caps.
[Full cleaning with the original path bound](OnlineReachabilityPreservers/ShortReturnFullCleaning.lean#L11) · [Full cleaning after a path-only restriction](OnlineReachabilityPreservers/ShortReturnFullCleaning.lean#L28) · [Full cleaning from path excess](OnlineReachabilityPreservers/ShortReturnFullCleaning.lean#L47) · [Literal full-bridge witness](OnlineReachabilityPreservers/ShortReturnFullCleaning.lean#L62).

The path-component criterion also applies in half mode whenever standard
degree copying preserves half exclusion by the existing sufficient test.
The degree test holds when the precedence graph has no cycle of length
at most \(k-3\), when \(k\le4\), when full bridges are excluded
through \(k-2\), or when every degree is already within the original width.
For a simple admissible input with positive budgets and mass at least
both budgets, the original path components fitting the original width
give a frozen witness of mass at least \(M/4\). Restricting to sublists
that retain at least \(2M/3\) and pass both the degree-safety and path
tests gives mass at least \(M/18\). Clipping at most \(M/3\) by path
excess alone guarantees this bound when the original degree test holds,
since that test survives taking sublists at the original width. At
\(k\ge2\), the path-excess result also gives a distinct nonempty
witness for a feasible literal input.
[Degree test](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1550) · [Degree test after sublists](OnlineReachabilityPreservers/ShortReturnStandardCleaning.lean#L11) · [Original path room](OnlineReachabilityPreservers/ShortReturnStandardCleaning.lean#L52) · [Path room after restriction](OnlineReachabilityPreservers/ShortReturnStandardCleaning.lean#L126) · [Path-excess witness](OnlineReachabilityPreservers/ShortReturnStandardCleaning.lean#L148) · [Literal path-excess witness](OnlineReachabilityPreservers/ShortReturnStandardCleaning.lean#L172).

Another path test keeps the labels of the original degree copies after
deletion. For positive budgets and original mass \(M\) at least both
budgets, require a simple copied restriction of mass \(K\ge2M/3\) that
excludes the selected bridges through the cutoff. Require its path
components, computed on the surviving copies, to fit the original width.
The original degree profile supplies a fixed vertex support and loses
at most \(M/12\).
The path support loses at most \(K^2/(8M)\). Together they retain at
least \(19M/36\) before enforcing the lower caps, giving a frozen
witness of mass at least \(M/36\) within both original budgets and all
four caps. Initial deletion and subsequent path clipping can share the
one-third loss budget. Full exclusion on the original rows certifies
the initial copies. In half mode, start with half exclusion on the
original rows. The earlier-copy return test on the surviving copies
then certifies their half exclusion before clipping.
[Fixed-copy restriction](OnlineReachabilityPreservers/ShortReturnFixedCopyCleaning.lean#L33) · [Shared loss budget](OnlineReachabilityPreservers/ShortReturnFixedCopyCleaning.lean#L174) · [Full test on the copied graph](OnlineReachabilityPreservers/ShortReturnFixedCopyCleaning.lean#L209) · [Half exclusion on retained copies](OnlineReachabilityPreservers/ShortReturnFixedCopyCleaning.lean#L233).

The component clipping loss is optimal among subsets with at most the
given width in each original component. A nondecreasing vertex rank on
every strict comparison is one way to bound that loss. A comparison
with a backward return has equal ranks at its endpoints, so each
short-return component lies within one rank class. If a rowwise selection
keeps at most the original path width per rank class, component clipping
keeps at least as much mass. For a simple full-bridge-free input through
the chosen cutoff with mass at least both positive budgets, a selection
of at least two thirds of the original mass on the standard degree
copies gives a frozen \(M/36\) witness with both budgets, all four caps
and full exclusion through that cutoff.
[Optimal clipping for fixed components](OnlineReachabilityPreservers/ShortReturnRankedExcess.lean#L12) · [Rank bound on total excess](OnlineReachabilityPreservers/ShortReturnRankedExcess.lean#L51) · [Frozen full-bridge witness from copied ranks](OnlineReachabilityPreservers/ShortReturnRankedExcess.lean#L92).

A second full-mode example uses indexed rows with budgets 51 and 23, two opposing
length-21 rows, and three singleton incidences for each of seven
vertices between those rows. Its mass is 63 and its frozen widths are
four and ten. The two long original path components each have size 21
at cutoff seven, so their combined excess is at least 22. This exceeds
one third of the mass. Standard degree copying assigns different
labels on the two long rows at those seven vertices. A nondecreasing
rank on the copied rows lets a bounded selection keep 55 incidences,
so the copied path excess is at most eight at every cutoff. The
original rows exclude every full bridge and the copied path criterion
gives a frozen witness at any chosen cutoff within both original
budgets and all four caps.
[Original widths](OnlineReachabilityPreservers/ShortReturnCopiedRankExample.lean#L23) · [Full exclusion](OnlineReachabilityPreservers/ShortReturnCopiedRankExample.lean#L54) · [Original path test fails](OnlineReachabilityPreservers/ShortReturnCopiedRankExample.lean#L144) · [Copied path excess bound](OnlineReachabilityPreservers/ShortReturnCopiedRankExample.lean#L248) · [Frozen full witness](OnlineReachabilityPreservers/ShortReturnCopiedRankExample.lean#L260).

The bidirected 23-leaf star has one row per dart, 24 vertices and 46
rows of mass 92. Every full bridge is excluded. Its original widths
are 15 for degree and eight for path length. At cutoff seven, the
center has a single degree component of size 46. Its excess of 31
already exceeds one third of the total mass. The path components
fit, so the full-mode path test gives the original-budget quarter-mass
witness at cutoff seven.
[Full exclusion at every cutoff](OnlineReachabilityPreservers/ShortReturnFullCleaningStar.lean#L68) · [The center component](OnlineReachabilityPreservers/ShortReturnFullCleaningStar.lean#L140) · [Original widths](OnlineReachabilityPreservers/ShortReturnFullCleaningStar.lean#L144) · [Failure of the two-sided excess test](OnlineReachabilityPreservers/ShortReturnFullCleaningStar.lean#L151) · [Full frozen witness at cutoff seven](OnlineReachabilityPreservers/ShortReturnFullCleaningStar.lean#L171).

The path-partition premise has an exact finite test. Within one row,
link the endpoints of every comparison with a short backward return.
Each connected component must lie in one group of any valid partition.
When every component fits the width, the components themselves give a
valid partition. For admissible standard degree copies at the original
width, this test at the original path width gives the same indexed
\(M/4\) witness in either mode.
[Graph of linked endpoints](OnlineReachabilityPreservers/ShortReturnPieceComponents.lean#L125) · [Exact component criterion](OnlineReachabilityPreservers/ShortReturnPieceComponents.lean#L144) · [Frozen quarter-mass witness](OnlineReachabilityPreservers/ShortReturnPieceComponents.lean#L198).

A six-vertex family with twelve indexed rows and mass twelve has one
increasing row, three disjoint backward pairs and eight empty labels.
The original degree and path widths are eight and four. At cutoff
four, all six vertices of the long row are protected, so a single
protected block would overflow. Each connected group has at most two
vertices at every cutoff. With the same widths, the partition method
gives the frozen quarter-mass witness at every full cutoff.
[Full exclusion before splitting](OnlineReachabilityPreservers/ShortReturnPieceComponentExample.lean#L43) · [Component width bound](OnlineReachabilityPreservers/ShortReturnPieceComponentExample.lean#L96) · [Single-block limit](OnlineReachabilityPreservers/ShortReturnPieceComponentExample.lean#L146) · [Frozen witness at every full cutoff](OnlineReachabilityPreservers/ShortReturnPieceComponentExample.lean#L159).

An eight-vertex example shows a limit of the disjoint-component rank test.
Its seven original rows exclude full bridges through three. Standard
width-two blocks form a directed cycle. Each vertex starts a strict
comparison in only one piece, so the pieces exclude full bridges at
every cutoff. The two pieces of the first parent share an SCC in the
detour constraint graph at every cutoff. The example uses a supplied
width of two. Its original factor-four cap is nine.
[Original exclusion](OnlineReachabilityPreservers/RiverDetourRankLimits.lean#L27) · [All-size exclusion after the split](OnlineReachabilityPreservers/RiverDetourRankLimits.lean#L64) · [Component test failure](OnlineReachabilityPreservers/RiverDetourRankLimits.lean#L72).

The same limitation occurs at the prescribed path width. Use
\(2m+16\) vertices and \(2m+3\) rows. Put two portions of eight consecutive
vertices of a directed cycle in one row. Each step on the two connecting
chains has its own row. Each chain has \(m+1\) edges, and the original
system excludes full bridges through \(m+1\). The mass is \(4m+20\) and for
\(m\ge 27\) the original factor-four path width is eight. Splitting the
original rows at that width preserves full exclusion at every size.
The two pieces of the central row share a component of the constraint
graph at every cutoff.
[Original exclusion](OnlineReachabilityPreservers/LongRankCriterionCycle.lean#L215) · [Original path width and component test](OnlineReachabilityPreservers/LongRankCriterionCycle.lean#L495).

The original factor-four degree width is seven. Every vertex has degree
at most three, so it keeps its block-zero label. The degree copies exclude
full bridges through \(m+1\). After splitting at width eight, the pieces
exclude full bridges at every size and the same two pieces still share a
component of the constraint graph. Restricting the supports of the pieces
and peeling gives a frozen witness of mass at least \(M/16\), with
both original budgets and all four caps.
[Admissibility and component test at both widths](OnlineReachabilityPreservers/LongRankCriterionCycle.lean#L706) · [Frozen witness from the original widths](OnlineReachabilityPreservers/LongRankCriterionCycle.lean#L731).

A finer finite graph joins each possible river’s start to every vertex on
a detour walk of at most \(k-1\) steps that omits the river piece. Treat these
links as undirected. Every bridge through \(k\) lies in one component.
The components refine those of the earlier graph. Check short returns
within these smaller components, or require distinct pieces of one
parent to meet disjoint components. With admissible degree copies and
the same simple input, mass and budget conditions, the short-return
test gives the frozen \(M/16\) witness at the original widths in either
mode. At both prescribed widths in the long-cycle family, each vertex
starts comparisons in only one piece. The finer graph therefore has
no edges at any cutoff and the distinct pieces pass its separation test.
[Bounded detour graph](OnlineReachabilityPreservers/RiverDetourVertices.lean#L43) · [Bridge localization](OnlineReachabilityPreservers/RiverDetourVertices.lean#L92) · [Component refinement](OnlineReachabilityPreservers/RiverDetourVertices.lean#L132) · [Frozen witness](OnlineReachabilityPreservers/RiverDetourVertices.lean#L209) · [Exact long-cycle separation](OnlineReachabilityPreservers/LongRankCriterionCycle.lean#L758).

The full bridges through \(k\) give exact constraints on the arrival
order. Require the river to precede the final arc of each such bridge.
There is a half-\(k\)-free ordering of all the rows exactly when the
directed graph of these constraints is acyclic. At the two original
widths, an acyclic graph on the pieces permits a new arrival order
without losing incidences. For simple input with mass \(M\) at least both
positive budgets, the reordered pieces give a half-\(k\)-free witness of
mass at least \(M/16\) within both original budgets and all four frozen caps.
[Exact order constraint](OnlineReachabilityPreservers/HalfBridgeArrivalOrder.lean#L56) · [Frozen cleaning after reordering](OnlineReachabilityPreservers/HalfBridgeArrivalOrder.lean#L228).

Taking sublists of simple pieces can only remove arrival constraints.
Keep the original degree copies and path blocks when deleting incidences.
If the surviving pieces have acyclic constraints through \(k\) and
the deletion costs at most \(M/18\), reordering, restriction and peeling
retain \(M/32\) with both original budgets and all four frozen caps.
[Constraint monotonicity](OnlineReachabilityPreservers/HalfBridgeArrivalOrder.lean#L87) · [Frozen cleaning after arrival deletions](OnlineReachabilityPreservers/HalfBridgeArrivalOrder.lean#L248).

For simple input of mass \(M\) at least both positive budgets, discard
unused copy and row labels when both occupied supports fit. Restricting
the labels preserves acyclicity and every retained incidence. For mass
\(K\) with \(a\) occupied vertices and \(b\) nonempty rows, peeling retains at least
\(K-aM/(4n)-bM/(4p)\). At the original widths with acyclic constraints and
both occupied supports fitting, losing at most \(M/4\) still gives an
indexed witness with at least \(M/4\), both budgets and all four frozen caps.
[Acyclicity under restriction](OnlineReachabilityPreservers/HalfBridgeArrivalOrder.lean#L268) · [Peeling with occupied supports](OnlineReachabilityPreservers/HalfBridgeArrivalOrder.lean#L289) · [Quarter-loss guarantee at the original widths](OnlineReachabilityPreservers/HalfBridgeArrivalOrder.lean#L335).

An arrival constraint survives an incidence deletion exactly when some
pre-deletion bridge on the pieces retains every required corner occurrence.
Fix any injective ranking of the pieces. It respects the surviving constraints
exactly when the deletions hit every original bridge whose final arc ranks
earlier than its river. If the deletions hit every such bridge through \(k\)
and cost at most \(M/18\) actual incidences at the original widths, the
indexed half-\(k\)-free witness retains at least \(M/32\), both original
budgets and all four frozen caps.
[Survival of an arrival constraint](OnlineReachabilityPreservers/HalfBridgeArrivalRepair.lean#L35) · [Exact cover for a ranking](OnlineReachabilityPreservers/HalfBridgeArrivalRepair.lean#L62) · [Frozen cleaning from an incidence cover](OnlineReachabilityPreservers/HalfBridgeArrivalRepair.lean#L83).

Choose a set of arrival edges whose removal makes the graph acyclic.
For each chosen edge, delete on its final arc piece every vertex shared
with its river piece. Each bridge giving the edge uses one of those
occurrences. The surviving graph is a subgraph of the graph with the
chosen edges removed. If the sum of the selected intersection sizes
is at most \(M/18\), this gives the indexed \(M/32\) guarantee for simple
input of mass at least both positive budgets, with all four frozen caps.
[Count of erased incidences](OnlineReachabilityPreservers/HalfBridgeArrivalRepair.lean#L137) · [Surviving constraints](OnlineReachabilityPreservers/HalfBridgeArrivalRepair.lean#L146) · [Frozen cleaning from selected edges](OnlineReachabilityPreservers/HalfBridgeArrivalRepair.lean#L169).

Start with simple rows excluding half-bridges through five. Each copied
comparison projects to a comparison on the same original row. The
sufficient rank test at each vertex compares the river and final arc
of a full three-bridge ending there and the start and return rows of
a two-step return. Weak increase on these edges preserves half-five
exclusion when a vertex and rank determine its copy. Every assignment
in this test is constant on each strongly connected component. The
component ranks distinguish all different components.
[Terminal constraint graph](OnlineReachabilityPreservers/HalfFiveTerminalRank.lean#L13) · [Half-five copy preservation](OnlineReachabilityPreservers/HalfFiveTerminalRank.lean#L158) · [Forced equalities within components](OnlineReachabilityPreservers/HalfFiveTerminalRank.lean#L174) · [Exact component ranks](OnlineReachabilityPreservers/HalfFiveTerminalRank.lean#L215).

The explicit rank assignment copies each occurrence to its vertex and
assigned rank. An example on six rows already excludes half-bridges at
every size. A three-bridge and a two-step return force equal ranks for
two rows at vertex 2. The assigned ranks at that vertex decrease on the
two last rows, both of which end a comparison there. The local test
still gives half-five exclusion on the copied family.
[Vertex copying by rank](OnlineReachabilityPreservers/HalfFiveTerminalRank.lean#L238) · [Original exclusion](OnlineReachabilityPreservers/HalfFiveTerminalRankExample.lean#L35) · [Rows in the same terminal component](OnlineReachabilityPreservers/HalfFiveTerminalRankExample.lean#L65) · [Half-five exclusion after copying](OnlineReachabilityPreservers/HalfFiveTerminalRankExample.lean#L77) · [Ranks decreasing in arrival order](OnlineReachabilityPreservers/HalfFiveTerminalRankExample.lean#L84).

A four-row family on six vertices excludes all full bridges. Its first
two rows share vertices 0 and 1 in reverse order. At each of these
vertices, return edges put both rows in one strongly connected component.
Every assignment passing the terminal rank test therefore gives these
two rows two common copied vertices. The test by itself can preserve
half-five exclusion while leaving repeated intersections.
[Original full exclusion](OnlineReachabilityPreservers/HalfFiveTerminalRankCoincidence.lean#L28) · [Two terminal cycles](OnlineReachabilityPreservers/HalfFiveTerminalRankCoincidence.lean#L41) · [Forced common copies](OnlineReachabilityPreservers/HalfFiveTerminalRankCoincidence.lean#L55).

The degree-copy test can use a smaller graph. Keep both rank comparisons
only for a three-bridge ending at the vertex followed by a two-step
return to it, with five distinct rows and the returning row earlier
than the river. Every projected half-five obstruction produces this
pattern. The same weak-rank inequalities still preserve half-five
exclusion. The smaller graph is empty at any vertex with no full
three-bridge ending there, including every vertex of the four-row example.
[Collision patterns](OnlineReachabilityPreservers/HalfFiveTerminalRank.lean#L31) · [Subgraph of the broad test](OnlineReachabilityPreservers/HalfFiveTerminalRank.lean#L63) · [Half-five preservation with the smaller graph](OnlineReachabilityPreservers/HalfFiveTerminalRank.lean#L253) · [Empty smaller graph in the example](OnlineReachabilityPreservers/HalfFiveTerminalRankCoincidence.lean#L78).

For simple half-five-free input, an explicit degree-copy assignment
preserves half-five exclusion exactly when it realizes none of the
projected terminal patterns. A pattern is realized when ranks match
at all five joins, including the two joins with the river, and the
two projected terminal copies have distinct ranks. Lean lifts each
realized pattern to a half-five bridge and recovers a realized pattern
from each forbidden bridge among the copies.
[Realized joins](OnlineReachabilityPreservers/HalfFiveTerminalRank.lean#L325) · [Lift to a forbidden half-five](OnlineReachabilityPreservers/HalfFiveTerminalRank.lean#L370) · [Exact copy criterion](OnlineReachabilityPreservers/HalfFiveTerminalRank.lean#L449).

At each vertex, put the rows involved in any projected collision constraint
first in its degree packing order. If those rows fit into one block of
the original width, all collision rank inequalities hold. Each copy degree
is within the cap, and projection recovers every original row. For simple
half-five-free input of mass at least both positive budgets with path
lengths already within the original cap, the construction gives an indexed
witness of mass at least \(M/4\) with both budgets and all four frozen caps.
[Constrained rows](OnlineReachabilityPreservers/HalfFiveTerminalPacking.lean#L18) · [Degree cap](OnlineReachabilityPreservers/HalfFiveTerminalPacking.lean#L135) · [Half-five exclusion](OnlineReachabilityPreservers/HalfFiveTerminalPacking.lean#L148) · [Frozen witness with capped path lengths](OnlineReachabilityPreservers/HalfFiveTerminalPacking.lean#L174).

To handle long rows after degree packing, protect both endpoints of each
comparison reversed on another copied row. Put the protected vertices
first in the packing order, then keep the original order within each piece.
If the protected vertices of every row fit the path width, the pieces
preserve half-five exclusion in parent arrival order. When both protected
supports fit their widths, these two packings keep every incidence before
restriction and peeling. For simple half-five-free input of mass at least
both positive budgets, the indexed witness has both original budgets,
all four frozen caps and mass at least \(M/16\).
[Protected path vertices](OnlineReachabilityPreservers/HalfFiveTerminalPacking.lean#L332) · [Half-five path splitting](OnlineReachabilityPreservers/HalfFiveTerminalPacking.lean#L375) · [Exact mass](OnlineReachabilityPreservers/HalfFiveTerminalPacking.lean#L362) · [Frozen cleaning with both packings](OnlineReachabilityPreservers/HalfFiveTerminalPacking.lean#L433).

The usual nested split example can be padded to six vertices and ten
indexed rows with mass ten. Two extra vertices belong only to the
long row and seven labels have empty rows. The original family excludes
full bridges at every size. Its prescribed widths are six for degree
and four for length. The original order of the resulting pieces contains
a half-four bridge. At every cutoff at least four, the arrival graph
has exactly one constraint, from the river on row \([2,1]\) to the first
piece of the long row. Reordering, restricting the supports and peeling
give the frozen witness at every cutoff. The earlier midpoint example
has cyclic constraints at cutoff four and admits no new order.
[Fixed-order half-four bridge](OnlineReachabilityPreservers/HalfBridgeArrivalOrderAudit.lean#L172) · [Exact single constraint](OnlineReachabilityPreservers/HalfBridgeArrivalOrderAudit.lean#L178) · [Frozen witness at the original widths](OnlineReachabilityPreservers/HalfBridgeArrivalOrderAudit.lean#L212) · [Cyclic midpoint example](OnlineReachabilityPreservers/HalfBridgeArrivalOrderAudit.lean#L230).

On this same six-vertex example, packing the reversed corners
keeps both prescribed widths and the original arrival order. The
packed pieces exclude half-bridges through five and give the frozen
witness of mass at least \(10/16\) with both budgets and all four caps.
[Prescribed packings](OnlineReachabilityPreservers/HalfFiveTerminalPackingExample.lean#L53) · [Ordinary split and packed pieces](OnlineReachabilityPreservers/HalfFiveTerminalPackingExample.lean#L72) · [Frozen witness](OnlineReachabilityPreservers/HalfFiveTerminalPackingExample.lean#L82).

The midpoint obstruction also occurs at both prescribed widths in a
literal family. Add one extra vertex to the split row and 41 distinct
singleton rows. The input has 49 vertices and 45 distinct nonempty
rows of mass 56. It excludes half-bridges through four and both
factor-four widths are four. On the resulting pieces, the size-three
and size-four bridges impose a directed two-cycle. Every arrival order
fails at cutoff four and above. Four disjoint two-vertex rows give a
separate literal witness of mass eight, full exclusion at every size,
both original budgets and all four frozen caps.
[Literal input parameters](OnlineReachabilityPreservers/HalfBridgeArrivalObstruction.lean#L23) · [Original half-four exclusion](OnlineReachabilityPreservers/HalfBridgeArrivalObstruction.lean#L88) · [Cyclic constraints at both widths](OnlineReachabilityPreservers/HalfBridgeArrivalObstruction.lean#L177) · [Separate literal witness](OnlineReachabilityPreservers/HalfBridgeArrivalObstruction.lean#L193).

Deleting vertex 5 from the row \([2,5]\) leaves mass 55 and removes the
size-three constraint. The size-four bridge still violates the original
arrival order. From cutoff four onward its river-to-final-arc comparison
is the only constraint. The new order after this deletion gives an
indexed witness at every cutoff, with mass at least \(56/32\), both
original budgets and all four frozen caps.
[Retained mass](OnlineReachabilityPreservers/HalfBridgeArrivalObstruction.lean#L355) · [Half-four bridge in the retained order](OnlineReachabilityPreservers/HalfBridgeArrivalObstruction.lean#L321) · [Exact retained constraint](OnlineReachabilityPreservers/HalfBridgeArrivalObstruction.lean#L328) · [Frozen witness after reordering](OnlineReachabilityPreservers/HalfBridgeArrivalObstruction.lean#L367).

In the indexed convention, pad the four midpoint rows with eight empty
labels. The input has seven vertices, twelve row labels and mass 14.
It excludes half-bridges through four. At its original degree and path
widths eight and four, two bridges impose opposite arrival orders.
The loss bound \(M/18\) allows zero deletions in this example, so
every sublist family within that loss bound still has cyclic constraints
at cutoff four and above. The unrestricted half-four cleaning result
supplies a separate witness at cutoff four.
[Input parameters](OnlineReachabilityPreservers/HalfBridgeArrivalBudgetAudit.lean#L14) · [Original half-four exclusion](OnlineReachabilityPreservers/HalfBridgeArrivalBudgetAudit.lean#L19) · [Failure of the small-deletion premise](OnlineReachabilityPreservers/HalfBridgeArrivalBudgetAudit.lean#L86) · [Unrestricted half-four cleaning](OnlineReachabilityPreservers/FrozenHalfFourCleaning.lean#L469).

The same conditional \(M/16\) and [\(M/32\) after rowwise deletions](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1623)
keep both budgets and all four original-average caps.
Alternatively, use each row's last safe boundary as its rank. A cut is
safe when no return of at most \(\max(0,k-3)\) precedence edges connects a
later vertex to an earlier vertex across that cut. This condition permits
cuts between runs even when a fixed-width cut crosses a short return.
Assume simple input with the matching bridge exclusion through \(k\),
positive budgets, and incidence mass \(M\) at least both budgets. In half
mode the degree split still uses one of the four sufficient conditions.
Packing the runs gives [\(M/16\) retention](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1808) when each
run fits into \(\lfloor M/p\rfloor\) and [\(M/54\) retention](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1790) when each
fits into \(\lfloor 4M/p\rfloor\). If longer runs carry at most \(M/56\) of the
mass, [pruning the original runs gives \(M/108\)](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1846) with the degree
condition on the retained rows in half mode. Each bound uses both original
budgets and all four original-average caps.
The unrestricted cyclic results at higher half cutoffs and the remaining
finite full cutoffs stay open.

For Lemmas 23 and 39, the [common-order extremal theorem](OnlineReachabilityPreservers/CommonOrderExtremal.lean)
uses a finite maximum. For every positive pair of budgets and either
bridge exclusion it gives one subsystem with both budgets and all four
caps, retaining at least one sixteenth of the maximum.

For any cutoff \(k\ge3\), the full extremum with four vertices and five paths
is exactly eleven incidences and the half extremum is exactly twelve. Both
witnesses have distinct nonempty rows and satisfy their respective exclusions
at every cutoff. The verified upper bounds allow empty rows and repeated
singletons and apply to families at or below both budgets. This
establishes a finite difference between the half and full extrema underlying
Lemmas 23 and 39. The constant-factor comparison for unbounded budgets in
the literal Lemma 39 remains open.
[Full upper bound](OnlineReachabilityPreservers/FourVertexBridgeExtrema.lean#L289)
· [Full witness](OnlineReachabilityPreservers/FourVertexBridgeExtrema.lean#L316)
· [Half upper bound](OnlineReachabilityPreservers/HalfSaturatedComparisons.lean#L183)
· [Half witness](OnlineReachabilityPreservers/FourVertexBridgeExtrema.lean#L372).

At half cutoff three, let \(L\) be the length of the latest nontrivial
row on \(n\) vertices. For each consecutive comparison of that row and
each outside vertex, at least one of the two comparisons in the detour
is absent. The candidates for different consecutive comparisons and outside
vertices are distinct. For simple rows of lengths \(\ell_i\), this gives
\(\sum_i \binom{\ell_i}{2}+(L-1)(n-L)\le n(n-1)\).
[Exact comparison count](OnlineReachabilityPreservers/HalfLatestRowComparisons.lean#L69)
· [Missing detour](OnlineReachabilityPreservers/HalfLatestRowComparisons.lean#L92)
· [Latest-row bound](OnlineReachabilityPreservers/HalfLatestRowComparisons.lean#L118).

For the remaining case of the half upper bound, suppose a row spans the
vertices and every directed comparison occurs. For three vertices in the
spanning row's order, the reverse comparisons must share one row. With
three distinct reverse rows, the last-arc rule gives opposite arrival
requirements on two of them. The reverse comparison of the spanning row's
endpoints therefore belongs to a second spanning row. Every other row has
length at most one, since the two spanning rows supply both directions of
every comparison.
[Reverse triangle](OnlineReachabilityPreservers/HalfSaturatedComparisons.lean#L16)
· [Second spanning row](OnlineReachabilityPreservers/HalfSaturatedComparisons.lean#L69)
· [Other rows are short](OnlineReachabilityPreservers/HalfSaturatedComparisons.lean#L47).

The cited Bridge Girth construction is ordered by slope. All-arcs-earlier
exclusion holds on every rectangular lattice in the construction. The
three-layer example has a half-3-bridge, so the construction leaves the
half-bridge-free benchmark in the literal Lemma 39 unresolved.
[Generic lattice proof](OnlineReachabilityPreservers/OrderedLatticeBridgeAudit.lean#L45)
· [Three-layer example](OnlineReachabilityPreservers/OrderedLatticeBridgeAudit.lean#L139).

At diagonal-scale budgets, Theorem 38 gives one constant \(K\) with upper
bound \(Km^{13/10}\) whenever both budgets are at most \(m\). The cited
all-arcs-earlier convention allows \(t^3\) distinct nonempty lattice rows
of length \(t+1\) on \(2(t+1)t^2\) vertices. The lattice uses slopes
zero through \(t-1\), which shift to one through \(t\) by adding the
layer to the height. At those budgets its mass is at least a constant
times \(t^{1/10}\) times every half-four-free mass. The comparison holds
against families at or below each
budget, including repeated and empty indexed rows. This establishes an
unbounded gap between the ordered-girth and last-arc conventions. The
literal full-versus-half comparison from Lemma 39 remains open in general.

[Diagonal upper bound](OnlineReachabilityPreservers/OrderedLatticeAsymptoticGap.lean#L14)
· [Distinct lattice rows](OnlineReachabilityPreservers/OrderedLatticeAsymptoticGap.lean#L55)
· [Polynomial gap](OnlineReachabilityPreservers/OrderedLatticeAsymptoticGap.lean#L70)
· [Unbounded gap](OnlineReachabilityPreservers/OrderedLatticeAsymptoticGap.lean#L129).

With at least three layers, four slopes and three starts, every reordering
of the complete slope lattice contains a half-three bridge. The slope-one
and slope-two lines that meet at layer two are each the river of a full
three-bridge whose last arc is the other line. The slope-zero and slope-three
first arcs give the two conflicting ordering constraints.
[Obstruction for every arrival order](OnlineReachabilityPreservers/OrderedLatticeBridgeAudit.lean#L160).

The same polynomial gap holds with Theorem 29's heights and positive slopes
at \(n=2\ell^3, p=\ell^3\). The code translates each height by its layer
index. On the actual lines the height is the start plus the layer index
times the positive slope, within \(2\ell^2\) heights. The bijection preserves
all comparisons and row labels. Each of the \(\ell^3\) distinct nonempty
lines has length \(\ell\). There is one constant for the comparison against
every half-four-free family within both budgets, for every \(\ell\ge1\).
[Height translation](OnlineReachabilityPreservers/PositiveSlopeLattice.lean#L17)
· [Line coordinates](OnlineReachabilityPreservers/PositiveSlopeLattice.lean#L31)
· [Gap at the cited dimensions](OnlineReachabilityPreservers/PositiveSlopeLattice.lean#L68).

The last-arc half and full extrema are within a fixed factor in two
budget regimes. For positive \(n,p\), cutoff \(k\ge2\), and an integer
\(a\ge3\), assume \(2n(n-1)\le a(a-1)p\) or both \(k\ge3\) and
\(p(p-1)\le a(a-3)n\). The length and degree moment bounds give
\(H(n,p,k)\le a\max(n,p)\). The full maximum is at least both budgets,
so \(H(n,p,k)\le a\beta(n,p,k)\). Full exclusion also gives
\(\beta(n,p,k)\le H(n,p,k)\). This works for the indexed extrema and,
when the full exact counts are feasible, the literal distinct nonempty
extrema. A fixed nonnegative integer bound \(C\) on \(n(n-1)/p\)
or on \(p(p-1)/n\) in the corresponding regime permits \(a=C+3\).
[Budget ratios](OnlineReachabilityPreservers/UnbalancedBridgeExtrema.lean#L19)
· [Half mass bound](OnlineReachabilityPreservers/UnbalancedBridgeExtrema.lean#L38)
· [Indexed comparison](OnlineReachabilityPreservers/UnbalancedBridgeExtrema.lean#L59)
· [Literal exact-count comparison](OnlineReachabilityPreservers/UnbalancedBridgeExtrema.lean#L75).

At cutoffs through two the half and full exclusions coincide for every
family of simple rows. At any input cutoff of at least two, literal half
feasibility supplies distinct nonempty full-free rows within both budgets at
every cutoff. A spanning row suffices when \(p\le n\). Otherwise the first
two vertices of each nonsingleton row and the original singletons form a
distinct half-free family with mean length at most two. Its mass is at
least \(p\), and the short-row construction yields a full witness of mass
at least \(\max(n,p)/8\). With either unbalanced-budget inequality above,
the full witness has mass at least \(H(n,p,k)/(8a)\) at a literal half
maximum. This comparison uses a full witness with at most the given
budgets and needs only half feasibility.
[Equivalence through two](OnlineReachabilityPreservers/LiteralFullBridgeBudget.lean#L12)
· [Full witness from half feasibility](OnlineReachabilityPreservers/LiteralFullBridgeBudget.lean#L24)
· [Unbalanced-budget comparison](OnlineReachabilityPreservers/LiteralFullBridgeBudget.lean#L98).

With positive budgets and \(k\ge2\), a literal half-free input of mass
\(n\le M\le8\max(n,p)\) has one literal output that excludes full bridges
at every size and meets all four original-average caps. The output mass is
in \([M/8,M]\) and its counts are at most \(n,p\). At the literal half
maximum, the mass bound follows from \(\min(n,p)\le8\), \(n(n-1)\le28p\),
or both \(k\ge3\) and \(p(p-1)\le40n\), with only literal half feasibility
at the exact counts. These cases give Lemma 39 with its printed half
benchmark and caps at the starting averages.
[Simultaneous full witness](OnlineReachabilityPreservers/LiteralFrozenFullLowMass.lean#L13)
· [Literal extremal witness](OnlineReachabilityPreservers/LiteralFrozenFullLowMass.lean#L51).

For every positive pair of budgets and \(k\ge4\), Lean proves
\(H(n,p,k)\le Cn^{7/50+\varepsilon(n)}\beta_\infty(n,p)\) in the indexed
convention, with one constant \(C\) and nonnegative \(\varepsilon(n)\to0\).
Here \(\beta_\infty\) excludes full bridges at all sizes. Through the
independence upper direction, the three lattice lower bounds give full
mass of order at least the largest of \(n^{2/3}p^{1/2}\),
\(n^{1/2}p^{2/3}\), and \(n^{2/5}p^{3/4}\) in the range \(n\ge2\),
\(p\le n^2\). The comparisons with the two powers of Theorem 38 use
the thresholds \(p=n\) and \(p=n^{6/5}\). The linear mass bound handles
the other budgets. For literal half input at the same cutoff, a distinct
nonempty full witness at or below both counts keeps the same power
comparison and all four caps at its own averages. The constant-factor
bound in general remains open.
[Indexed power comparison](OnlineReachabilityPreservers/HalfFullLatticeComparison.lean#L129)
· [Literal witness and output caps](OnlineReachabilityPreservers/HalfFullLatticeComparison.lean#L213).

At full cutoff three, a distinct nonempty simple family with exactly \(p\) rows
on \(n\) available vertex labels exists precisely when
\(p\le n+2\lfloor n/2\rfloor\lceil n/2\rceil\). Any larger full cutoff has
the same upper bound. The first steps of the longer rows are distinct
and have no transitive triangle. Balanced bipartite steps in both
directions and singleton rows attain the capacity at cutoff three.
[First-step count](OnlineReachabilityPreservers/FullThreeLiteralFeasibility.lean#L178)
· [Exact cutoff-three feasibility](OnlineReachabilityPreservers/FullThreeLiteralFeasibility.lean#L313).

The cutoff-three capacity supplies a literal family of mass \(p\) within
both budgets with full exclusion at every size. Its ordered pairs all go
across the balanced parts in one direction, and it also uses singleton
rows. At full cutoff \(k\ge3\), for \(q=\min(n,p)\) and input mass \(M\),
restrict one support and keep its distinct longer rows, or use this
family of mass \(p\). The larger mass \(W\) satisfies
\(\min(k,q)M\le2qW\) and \(W\le M\). When \(p\le n\), keeping whole original
rows gives \(\min(k,q)M\le qW\). These comparisons preserve both budgets,
literal nonempty distinct rows, and full exclusion at all sizes.
[Mass \(p\) construction](OnlineReachabilityPreservers/FullThreeLiteralFeasibility.lean#L398)
· [All-size mass comparison](OnlineReachabilityPreservers/LiteralFullCutoffComparison.lean#L78)
· [Whole-row comparison](OnlineReachabilityPreservers/LiteralFullCutoffComparison.lean#L13).

At full exclusion of all sizes, the exact domain has
\(p\le n+\max(2(n-1),\lfloor n^2/4\rfloor)\) for \(n\ge1\), and \(p=0\)
for \(n=0\). It is also the domain at every full cutoff covering at least
one whole budget. The selected first arcs have no substitute routes
within the graph they form. With \(c\)
strongly connected components, two connector forests account for at most
\(2(n-c)\) arcs. The condensation is acyclic and has no transitive
triangle, so its underlying graph contributes at most
\(\lfloor c^2/4\rfloor\) arcs. The bidirectional star and the one-way
balanced bipartite construction attain the two alternatives with all
singletons available. This gives exact feasibility under full exclusion.
[First-arc representation](OnlineReachabilityPreservers/FullThreeLiteralFeasibility.lean#L118)
· [Detour exclusion](OnlineReachabilityPreservers/AllSizeLiteralFeasibility.lean#L16)
· [Arc bound](OnlineReachabilityPreservers/EssentialArcCount.lean#L173)
· [Exact all-size feasibility](OnlineReachabilityPreservers/AllSizeLiteralFeasibility.lean#L112)
· [Finite cutoff covering a budget](OnlineReachabilityPreservers/AllSizeLiteralFeasibility.lean#L137).

For every full cutoff at least three, the number and incidence mass of
simple indexed rows of length at least three are both \(o(n^2)\), uniformly in the row
budget. The first three vertices define edge-disjoint triangles on
three copies of the vertex set. Full-two and full-three exclusion give
exactly those triangles. Triangle removal controls their number,
and the squared-length bound and Cauchy–Schwarz control their mass.
Hence the total incidence mass is at most \(2p+o(n^2)\).
[Long-row count](OnlineReachabilityPreservers/FullThreeLongRows.lean#L89)
· [Long-row incidence mass](OnlineReachabilityPreservers/FullThreeLongRows.lean#L173)
· [Total incidence mass](OnlineReachabilityPreservers/FullThreeLongRows.lean#L198).

At \(p\le\lfloor n^2/4\rfloor\), a one-way bipartite family of exactly
\(p\) distinct pairs gives mass \(2p\) and excludes full bridges at every
size. Thus the literal and indexed full extrema are between \(2p\)
and \(2p+o(n^2)\) for all \(k\ge3\) in this range. The long-mass bound
extends uniformly over smaller vertex budgets \(v\le n\). If \(M>8p\)
and \(M\ge\eta n^2\), the original lower cap \(M/(4p)\) requires every
output row to be long. For each fixed \(\eta>0\) and positive integer
\(r\), the resulting full incidence mass is below \(M/r\) for large
enough \(n\), independently of the output row count. The half-side
density bound below rules out these inputs at unbounded vertex budgets.
[Uniform bound](OnlineReachabilityPreservers/FullThreeFrozenMassAudit.lean#L13)
· [Conditional obstruction](OnlineReachabilityPreservers/FullThreeFrozenMassAudit.lean#L35)
· [Pair-capacity sharpness](OnlineReachabilityPreservers/FullThreeFrozenMassAudit.lean#L70).

The full-three mass of rows of length at least three is also
\(o(n\sqrt p)\) as \(p\) grows, uniformly in the vertex count and over
every output budget at most \((n,p)\). On three tagged copies of the
vertices each row contributes a complete tripartite block of side
\(\lfloor L/3\rfloor\). All triangles belong to one row, and the cyclic
addition construction packs a squared side length of edge-disjoint
triangles per row. Triangle removal controls the squared third widths
when all rows are at most a sufficiently small fraction of \(n\), and
thus the squared lengths of the rows of length at least three. Rows
above the fraction add \(O(n)\) mass. For \(M>8p\) and \(M\ge\eta n\sqrt p\), all full
witnesses through size three satisfying the original lower length cap
have mass below \(M/r\) at sufficiently large \(p\), for fixed
\(\eta>0\) and positive integer \(r\). This extension of the obstruction
uses both output budgets and is conditional on the starting parameters.
The half-side density bound below also rules out these inputs at
unbounded path budgets.
[Long-row estimate](OnlineReachabilityPreservers/FullThreeBlockMass.lean#L278)
· [Uniform estimate](OnlineReachabilityPreservers/FullThreeBlockMass.lean#L361)
· [Stronger lower-cap obstruction](OnlineReachabilityPreservers/FullThreeBlockMass.lean#L389).

For any half cutoff \(k\ge3\), the first triples of long rows give
edge-disjoint positive matchings in the bipartite first-to-middle graph,
one matching per last vertex. The three parts each use at most the
original vertex budget. Conversely, a family of positive matchings with
disjoint edges gives distinct simple length-three rows with all-size
half exclusion on the disjoint union of the parts. For fixed final
vertex, an unmatched edge between two matched endpoints forces the
left endpoint's row to precede the right endpoint's row. Existence of
an order meeting the constraints is equivalent to existence of the
positive weights.
The result concerns the count of rows of length at least three.
[Arbitrary half input](OnlineReachabilityPreservers/PositiveMatchingHalfRows.lean#L308)
· [Weights from the arrival order](OnlineReachabilityPreservers/PositiveMatchingHalfRows.lean#L195)
· [All-size half construction](OnlineReachabilityPreservers/PositiveMatchingHalfRows.lean#L138).

A quadratic shift construction supplies many such matchings. Use all
\(N^d\) shift vectors with coordinates in \(\{0,\ldots,N-1\}\).
For the source \((x,z)\) use the inner box of size \(dN^{d+2}\);
the target for shift \(a\) is \((x+a,z+\|a\|^2)\) in the outer
box. For a candidate label \(c\), the two endpoint weights on an
edge of shift \(a\) sum to \(1-2\|a-c\|^2\), positive exactly
at \(a=c\). Every fiber has the same cardinality and the fibers are
pairwise edge-disjoint. The tagged half family has
\(p=dN^{2d+2}\) distinct rows of length three, with half exclusion
at every cutoff. At fixed positive \(d\), the ambient vertex budget is of
order \(N^{d+2}\), so its mass is at least a constant times
\(n^{2-2/(d+2)}\) along this sequence. Here \(M=3p\).
[Positive shift matching fibers](OnlineReachabilityPreservers/QuadraticShiftHalfRows.lean#L182)
· [Exact half witness](OnlineReachabilityPreservers/QuadraticShiftHalfRows.lean#L200)
· [Integer-power mass bound](OnlineReachabilityPreservers/QuadraticShiftHalfRows.lean#L237).

The entire long mass admits the same reduction up to a factor of five.
Splitting into all complete contiguous triples and preserving parent
order keeps the size-three exclusions. For row lengths \(L_i\), there
are exactly \(\sum_i\lfloor L_i/3\rfloor\) triples. The half case gives
disjoint positive matching fibers and the full case gives edge-disjoint
triangles with no accidental triangle. The latter is the induced
matching setting of Bridge Girth v4 Theorem 81. If a half family had
\(M\ge\eta n^2\) and \(M>8p\), its triples would give at least
\(\eta n/8\) positive matching fibers of size at least \(\eta n/8\).
The regularity argument below bounds the total mass of such fibers.
[Half long-mass reduction](OnlineReachabilityPreservers/ThreeBlockMatchingReduction.lean#L66)
· [Full long-mass reduction](OnlineReachabilityPreservers/ThreeBlockMatchingReduction.lean#L81)
· [Linear fiber sizes](OnlineReachabilityPreservers/ThreeBlockMatchingReduction.lean#L143).

For any \(\varepsilon>0\) and sufficiently large \(n\), positive matching
families on two \(n\)-vertex sides with at most \(n\) colors have at most
\(\varepsilon n^2\) edges. Sort each color by left weight with distinct
tie-breaking indices. A backwards cross edge between distinct matches
would have positive weight for that color and violate its matching
property. Apply Szemerédi regularity to the underlying bipartite graph.
An edge in a retained dense regular pair must have either fewer than
\(\lceil\delta|U|\rceil\) later matching edges on its left part \(U\) or
fewer than \(\lceil\delta|W|\rceil\) earlier matching edges on its right
part \(W\). Otherwise the two endpoint subsets form a forbidden empty
rectangle. The count charges each extreme set once per part.
For arbitrary simple half input at cutoffs of at least three, the
entire long-row incidence mass is therefore \(o(n^2)\), with the
threshold uniform in the row budget. If \(M>8p\), then \(M=o(n^2)\) as
\(n\) grows, and \(M=o(n\sqrt p)\) as \(p\) grows, uniformly in \(n\).
The second assertion uses the necessary path density below and
\(p\le n^2\) from the pair bound. Both conditional counterexample regimes
above are now excluded. The general constant-factor comparison in
the literal Lemma 39 remains open.
[Matching density](OnlineReachabilityPreservers/PositiveMatchingDensity.lean#L174)
· [Long-row mass](OnlineReachabilityPreservers/PositiveMatchingDensity.lean#L249)
· [Total mass](OnlineReachabilityPreservers/PositiveMatchingDensity.lean#L275)
· [Large vertex budgets](OnlineReachabilityPreservers/PositiveMatchingDensity.lean#L288)
· [Large path budgets](OnlineReachabilityPreservers/PositiveMatchingDensity.lean#L301).

For any fixed positive density threshold \(\delta\) and error
\(\varepsilon\), \(p\ge\delta n^2\) gives half mass at most
\((2+\varepsilon)p\) for simple indexed input and sufficiently large \(n\), uniformly over
half cutoffs at least three. With \(p\le\lfloor n^2/4\rfloor\), the
all-size full-free system of \(p\) distinct two-vertex rows has exact
mass \(2p\). Every simple indexed half input has mass at most
\((1+\varepsilon)2p\), using the error \(2\varepsilon\) in the half bound. For the
original-average version of the literal Lemma 39, positive quadratic
path density alone gives \(M\le3p\) at any feasible exact-count half
maximum and sufficiently large \(n\). The low-mass construction yields
distinct nonempty simple rows within both budgets, with mass in
\([M/8,M]\), the four original caps, and full exclusion at every size.
[Relative mass bound](OnlineReachabilityPreservers/DensePathBudgetFrozenFull.lean#L14)
· [Pair-capacity comparison](OnlineReachabilityPreservers/DensePathBudgetFrozenFull.lean#L29)
· [Literal frozen comparison](OnlineReachabilityPreservers/DensePathBudgetFrozenFull.lean#L51).

In simple indexed half input at any cutoff at least three, the mass of
rows of length at least three is \(o(n\sqrt p)\) as the path budget grows.
The threshold is uniform in \(n\) and in the cutoff. Restrict to just
those rows with the original order. Their count \(p'\) is at most \(n^2\)
by comparison uniqueness, and is at least \(\eta\sqrt p\) if they carry
mass \(\eta n\sqrt p\). The upstream bound then gives \(p'\ge\delta n^2\)
for a positive \(\delta\) depending on \(\eta\). The regularity estimate bounds their mass by \(2p'+o(n^2)\),
while each retained row has length at least three. The result gives
an \(\eta n\sqrt p+C_\eta n\) bound at all budgets and an
\(\eta n\sqrt p\) bound within all smaller budgets for sufficiently large
outer \(p\). Adding the short rows yields total \(2p+o(n\sqrt p)\).
[Large path budget](OnlineReachabilityPreservers/HalfThreeLongMassScale.lean#L13)
· [Uniform bound with a linear term](OnlineReachabilityPreservers/HalfThreeLongMassScale.lean#L87)
· [Both smaller budgets](OnlineReachabilityPreservers/HalfThreeLongMassScale.lean#L107)
· [Total half mass](OnlineReachabilityPreservers/HalfThreeLongMassScale.lean#L132).

The hexagonal grid uses integer points with \(0\le x,y\le2w-2\) and
\(w-1\le x+y\le3(w-1)\), for \(w\ge1\). Lines keep \(x\), \(y\), or \(x+y\)
fixed and are oriented respectively down, right, and up-left. Distinct
rows sharing a corner have different orientations. An arc with both
river endpoints must have its direction, and the other two directions
cannot form a two-step detour in the river direction. Every vertex lies
on one line from each family. This gives exactly \(3(2w-1)\) indexed rows,
length in \([w,2w-1]\), vertex budget at most \((2w-1)^2\), and mass
three times the vertex count. Full exclusion holds through size three.
[Grid definition](OnlineReachabilityPreservers/FullThreeHexGrid.lean#L29)
· [Full-three proof](OnlineReachabilityPreservers/FullThreeHexGrid.lean#L117)
· [Degree three](OnlineReachabilityPreservers/FullThreeHexGrid.lean#L137)
· [Line lengths](OnlineReachabilityPreservers/FullThreeHexGrid.lean#L177)
· [Exact mass](OnlineReachabilityPreservers/FullThreeHexGrid.lean#L261).

At cutoff three, the original-average form of the literal Lemma 39
holds for \(0<p\), \(8p\le n\), and \(p(p-1)\le108n\), when an exact
literal half family is feasible. For its maximum \(M\), if \(M\le8n\),
use the low-mass literal witness. Otherwise the half degree moment
implies \(p^2>40n\) and \(M\le12n\). Use width \(w=\lceil M/(4p)\rceil\).
The moment and budget bounds yield \((2w-1)^2\le n\) and
\(3(2w-1)\le p\). Pack disjoint grid copies up to the smaller capacity.
The retained mass is in \([M/8,M]\), all four starting-average caps
hold, and the output rows are distinct, nonempty and simple. The
regular-copy argument works for any full-three-free seed family with
uniform degree, the prescribed length range, and the stated budget
and original-mass inequalities.
[Moment estimate](OnlineReachabilityPreservers/FullThreeHexGridCleaning.lean#L14)
· [Disjoint regular copies](OnlineReachabilityPreservers/FullThreeHexGridCleaning.lean#L69)
· [Hexagonal witness](OnlineReachabilityPreservers/FullThreeHexGridCleaning.lean#L173)
· [Literal Lemma 39 in this range](OnlineReachabilityPreservers/FullThreeHexGridCleaning.lean#L186).

At every half cutoff \(k\ge3\), simple indexed families have
\(M\le8(n+p)\) or \(M^3\le1024(np)^2\), hence mass
\(O((np)^{2/3}+n+p)\). Later branches cannot share an upstream vertex
before their respective intersections with the base row. After
pruning to unique intersections, count incidences with both large
arrival rank at the vertex and large position in the row. Each such
incidence specifies several earlier bases and upstream vertices, and
each resulting pair has a unique source. This gives the bound directly
for locally ordered rows. For fixed \(\eta>0\), if a half input at
large \(p\) has \(M\ge\eta n\sqrt p\), it has \(p\ge\delta n^2\) for a
constant \(\delta>0\) depending only on \(\eta\). This identifies the
path-density regime required by the \(n\sqrt p\)-scale obstruction.
[Mass estimate](OnlineReachabilityPreservers/HalfThreeUpstreamMass.lean#L347)
· [Necessary density](OnlineReachabilityPreservers/HalfThreeUpstreamMass.lean#L378).

At positive budgets \(n\le Cp\) and \(p\le Cn\) for a fixed
\(C\ge1\), Lemma 39 with its literal \(H\) benchmark holds at cutoff
three with the four caps at the witness's own averages. A finite-field
line family gives a literal full-three witness with both budgets and
mass between \(M/[16(8C)^2]\) and \(M\) for any positive-mass simple
half input excluding through size three. Every line has \(q\) points and each vertex lies on
exactly \(q\) lines. There are no repeated lines and no size-three
incidence cycle by Vandermonde independence. The construction uses a
power of two \(q\) with \(q^3\le\min(n,p)\) and \(q^4\le M\) when the
smaller budget is at least eight and \(M\ge16\). Either side fixes the
scale. The remaining positive-mass cases use one row on \(\min(n,M)\)
vertices. The result applies at the literal half maximum whenever
the exact positive literal budgets are feasible.
[Regular field family](OnlineReachabilityPreservers/WengerThreeRows.lean#L128)
· [Comparable-budget Lemma 39 case](OnlineReachabilityPreservers/WengerThreeRows.lean#L242).

For positive budgets and any half cutoff at least three, counting all
thresholds together improves the mass estimate to
\((M-2(n+p))_+^3\le48(np)^2\). The shifted estimate gives an exact
starting-average case of the literal Lemma 39 at \(n=p=q^3\), for a
finite field of order \(q\ge11\), with cutoff three. The literal half
maximum exists and satisfies \(q^4\le M\le4q^4\). Use the field family
on the same exact budgets. Its degrees and lengths are all \(q\),
between a quarter and four times the starting averages \(M/q^3\).
Its mass is \(q^4\) and lies in \([M/4,M]\).
[Refined half bound](OnlineReachabilityPreservers/HalfThreeUpstreamMass.lean#L324)
· [Literal frozen case at the half maximum](OnlineReachabilityPreservers/FrozenWengerThree.lean#L90).

The same exact-budget witness covers all finite field orders \(q\).
For \(q\ge5\), the latest-hit estimate uses \(4n+p\le q^4\) and
\((np)^2=(q^4)^3\) at \(n=p=q^3\). For \(q=2,3,4\), the
pair-count quadratic and \(2q^3\le4q(4q-1)\) give
\(M\le4q^4\). This proves the cutoff-three starting-average
case at every equal field cube, with mass \(q^4\) between
\(M/4\) and \(M\).
[Half mass at every field cube](OnlineReachabilityPreservers/AllFieldCubeFrozenFullThree.lean#L14)
· [Literal witness at every field cube](OnlineReachabilityPreservers/AllFieldCubeFrozenFullThree.lean#L48).

The starting-average case of literal Lemma 39 at cutoff three also
holds for all equal budgets \(n=p\ge256^3\). Count only the latest
common vertex on the later row for each pair of intersecting rows.
Every skipped choice is charged to a different earlier incidence.
At any half cutoff at least three and each \(T\ge0\), the resulting
bound on the original mass is
\((M-\lfloor M/(T+1)\rfloor-((T+1)n+p))_+^3\le6(np)^2\).
Taking \(T=15\) and \(q=2^{\lfloor\log_8 n\rfloor}\) gives
\(M\le4nq\). The literal maximum exists, and one or two disjoint
field copies with singleton padding give \(q^4\le M\) and \(nq\le4M\).
One full-three field copy then fits both budgets, meets the four
starting-average caps, and has mass \(W=q^4\) in \([M/32,M]\).
[Latest common vertex bound](OnlineReachabilityPreservers/HalfThreeUpstreamMass.lean#L541)
· [Equal-budget literal frozen case](OnlineReachabilityPreservers/EqualBudgetFrozenFullThree.lean#L44).

The same cutoff-three conclusion covers nearby budgets
\(b=\min(n,p)\ge512^3\) and \(a=max(n,p)\) with \(64a\le65b\).
With \(q=2^{\lfloor\log_8 b\rfloor}\), the latest-common-vertex
estimate bounds every half-three-free mass by \(4bq\). Up to three
disjoint field copies fit the smaller budget, and the remaining path
labels can be filled by distinct singletons using the original vertex
budget. This supplies exact half feasibility and bounds
\(q^4\le M\) and \(aq\le4M\) at the literal maximum. One full-three
copy then lies within both budgets, has mass in \([M/32,M]\), and
satisfies all four starting-average caps.
[Half mass at nearby budgets](OnlineReachabilityPreservers/NearBudgetFrozenFullThree.lean#L13)
· [Exact singleton padding](OnlineReachabilityPreservers/ExtremalCopyBounds.lean#L272)
· [Nearby-budget literal frozen case](OnlineReachabilityPreservers/NearBudgetFrozenFullThree.lean#L71).

For \(b\ge1024^3\) and \(2a\le3b\), the cutoff-three result
retains at least \(M/16\). In a field of order \(Q\), restrict both
the layers and slope labels to width \(w\). The regular full-three
family has \(v=wQ^2\) vertices and paths, and mass \(vw\).
Choose the power-of-two field so that \(v\le b\le4v\)
and \(16b\le65w^3\). The latest-hit bound gives \(M\le4bw\).
Using \(\lfloor b/v\rfloor\) disjoint copies and distinct singleton
padding gives an exact eligible half family with mass at least
\(bw/2\), supplying the upper caps at both starting averages.
One restricted field family satisfies all four bounds at the
literal maximum and fits both budgets.
[Restricting layers and slopes](OnlineReachabilityPreservers/WengerThreeRows.lean#L430)
· [Half mass at ratio at most three halves](OnlineReachabilityPreservers/ComparableFrozenFullThree.lean#L21)
· [Starting caps at comparable large budgets](OnlineReachabilityPreservers/ComparableFrozenFullThree.lean#L124).

For \(b\ge8192^3\) and \(a\le2b\), use separate layer and slope
widths \(\ell,d\) in a field of order \(Q\). The regular full-three
family and its transpose have budgets \((\ell Q^2,dQ^2)\) and the
reverse pair, with common mass \(\ell dQ^2\).
Choose \(Q,d\) using the larger budget and leave one layer out
when selecting \(\ell\). When \(p\ge n\), a balanced two-layer
family on the reserved labels supplies the remaining short rows.
Its vertex labels are disjoint from the restricted field family. When
\(p\le n\), distinct singleton padding suffices. The latest-hit
estimate bounds the literal half maximum by both \(4bd\) and
\(4a\ell\). Together with the exact padded family, this gives all
four starting-average caps. The restricted full family fits both
budgets and has mass in \([M/16,M]\).
[Independent layer and slope widths](OnlineReachabilityPreservers/WengerThreeRows.lean#L367)
· [Half mass at ratio at most two](OnlineReachabilityPreservers/FactorTwoFrozenFullThree.lean#L15)
· [Starting caps at ratio at most two](OnlineReachabilityPreservers/FactorTwoFrozenFullThree.lean#L220).

For a field of order \(q\), take \(\nu\) outside the image of
\(z\mapsto z^2+z\) and use slope \((s,t,s^2+st-\nu t^2)\).
The points have four coordinates, and each line is specified by the
two slope parameters and three translations. Any pair of distinct
points has at most one common line. If three distinct lines meet
pairwise at three distinct points, the first-coordinate increments
give a nonzero quadratic value that must vanish. This rules out
incidence cycles of lengths four and six, and proves full-three
exclusion in both incidence orientations regardless of row order.
The regular lengths and degrees are \(q,q^2\) and \(q^2,q\),
respectively. At \(q\ge5\) and either exact budget
\((q^4,q^5)\) or \((q^5,q^4)\), the literal half maximum \(M\)
at cutoff three lies between \(q^6\) and \(4q^6\). The regular
family has mass \(q^6\) on the original budgets and meets all four
starting-average caps.
[Quadratic construction and its transpose](OnlineReachabilityPreservers/QuadraticThreeRows.lean#L152)
· [Half mass at quadratic budgets](OnlineReachabilityPreservers/QuadraticThreeRows.lean#L179)
· [Quadratic-budget literal frozen case](OnlineReachabilityPreservers/QuadraticThreeRows.lean#L205).

For \(q\ge16\), the cutoff-three claim extends to the rectangles
\(N\le n\le9N/8\), \(P\le p\le9P/8\) above either quadratic
budget \((N,P)\). Take \(q-1\) first-coordinate layers in the
quadratic construction. In the point-to-line count with
\((N,P)=(q^4,q^5)\), the unused layer frees \(q^3\) vertex labels
for a disjoint family of short rows, enough to reach the exact row
count \(p\). In the transposed counts, the unused row labels fit
distinct singleton padding. Both exact-count candidates have mass
at least \(q^5(q-1)\). The latest-hit bound gives
\(M\le4q^5(q-1)\), where \(M\) is the literal half maximum.
The restricted full witness meets the four starting-average caps and
has mass \(q^5(q-1)\) between \(M/4\) and \(M\).
[Restricted field layers](OnlineReachabilityPreservers/QuadraticThreeRows.lean#L247)
· [Full disjoint union](OnlineReachabilityPreservers/FullDisjointUnion.lean#L121)
· [Half mass near quadratic budgets](OnlineReachabilityPreservers/QuadraticBudgetFrozenFullThree.lean#L15)
· [Literal frozen case near quadratic budgets](OnlineReachabilityPreservers/QuadraticBudgetFrozenFullThree.lean#L120).

Over a field of order \(q\), an affine Hermitian construction in a
quadratic extension has \(q^7\) point labels and \(q^8\) line labels.
Each line contains \(q^2\) points and each point lies on \(q^3\)
lines. Two distinct points determine at most one line. Points on
the same line are Hermitian orthogonal. A three-line incidence
triangle would require two orthogonal normalized line directions
through one point. The resulting norm identity equates their slope
coordinates, so the lines coincide. Both incidence orientations
therefore exclude full bridges through three. For \(q\ge3\) the
exact literal half maximum at either budget is at most \(4q^{10}\),
and the full witness has mass \(q^{10}\) and all four
starting-average caps.
[Hermitian construction and its transpose](OnlineReachabilityPreservers/HermitianThreeRows.lean#L305)
· [Half mass at Hermitian budgets](OnlineReachabilityPreservers/HermitianThreeRows.lean#L352)
· [Hermitian-budget literal frozen case](OnlineReachabilityPreservers/HermitianThreeRows.lean#L376).

At every cutoff \(k\ge2\) and prime field order \(q\), the first
\(k-1\) slope moments give regular distinct nonempty rows on the
exact budgets \((q^k,q^k)\). Order each row by its first
coordinate in \(\{0,\ldots,q-1\}\). In a putative bridge, group
the signed first-coordinate differences by slope. There are at
most \(k\) distinct slopes, so the first \(k\) moment equations
force every grouped coefficient to vanish. The first arc has
a different slope from the river. The sum of the positive
increments of its slope is strictly between zero and \(q\),
giving a contradiction in the prime field. The mass is \(q^{k+1}\)
and all degrees and lengths equal \(q\). The exact statement
excludes every cutoff \(c\) with \(\min(c,q)\le k\), including
all cutoffs when \(q\le k\). This supplies regular full witnesses
and a lower bound on the full extremum at those budgets.
[Regular full witnesses at prescribed cutoffs](OnlineReachabilityPreservers/PrimeMomentFullRows.lean#L238).

The literal exact-count domains differ. At four vertices and eleven rows,
the half family consists of four singletons and seven directed comparisons.
Three comparisons leave vertex zero early in the arrival order. The other
four form a bidirectional star on the remaining vertices. This family
excludes half-bridges at every size. For full exclusion through at least
size four, there are at most four singleton and six longer rows. Seven
longer rows would have seven distinct first steps and a reciprocal pair.
Contracting that pair exposes a shortcut on three or four original
vertices, supported by distinct rows. Thus the exact full extremum has
no eligible family at these counts. Lemma 39 asks for an output within
the budgets, which allows smaller full families at the same input counts.
[Half witness](OnlineReachabilityPreservers/FourVertexLiteralFeasibility.lean#L34)
· [Full count bound](OnlineReachabilityPreservers/FourVertexLiteralFeasibility.lean#L322)
· [Exact feasibility separation](OnlineReachabilityPreservers/FourVertexLiteralFeasibility.lean#L408).

Here \(\ell,d\) are average path length and vertex degree and \(H\) is the
half-bridge-free extremal function. The analogous full bridge-free function is \(\beta\).
See [source notes](SOURCE_NOTES.md) for explicit discrepancies and the distinction between a
false intermediate assertion and an incomplete proof step.

## Repository provenance

The starting upstream revision was `7bacf7871a0dddd88d72e1ab50a219967e9464f4`.
All fetched heads and commit/path histories were searched for the paper title,
arXiv ID, and relevant path names. The existing
[reachability contracts](https://github.com/gbodwin/paper-formalizations/tree/94dcaef65d355cc1dd8f071eaeb0789fee60ed4e)
and [half-cover](https://github.com/gbodwin/paper-formalizations/tree/a12bcc14266a97efeb9c62006bb414d8f59b7a5f)
are for *A Note on Distance-Preserving Graph Sparsification*. Its later
[SCC quotient](https://github.com/gbodwin/paper-formalizations/blob/11690f560db73f1f05ef121d5687a1e088168482/A%20Note%20on%20Distance-Preserving%20Graph%20Sparsification/SlackSparsification/SCCQuotient.lean)
and [internal connector](https://github.com/gbodwin/paper-formalizations/blob/1f4df0b5e56e2e60ff763986179d9abd39e0db09/A%20Note%20on%20Distance-Preserving%20Graph%20Sparsification/SlackSparsification/SCCInternal.lean)
give reusable reachability arguments, phrased there over an undirected ambient graph
and oriented arcs. Their offline sourcewise bound does not supply an online algorithm.
No existing Site in the owner's PaperLab listing matched the target title.
The [publications entry](https://gregbodwin.com/publications/index.html) had an arXiv
link and no Lean link at the start of this work.
