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
| Theorems 8 and 21 | Same new online unit-cost directed Steiner forest result, randomized polynomial time and competitive ratio \(O(n^{3/5+\varepsilon})\). Theorem 21 uses the early-pair algorithm of [21], all-pairs thick-demand hitting, the thin-pair online rounding from the [24] framework, the two orientations of Theorem 2, and Lemmas 20 and 22. | [The full online algorithm](OnlineReachabilityPreservers/SteinerComplete.lean) checks the expected \(O(n^{3/5+\varepsilon})\) rate against any feasible offline solution on a fixed demand trace, including zero optimum and repeated requests. The first block of distinct non-self requests is chosen independently of the random seeds. Correctness and monotonicity hold on every realization. Formal end-to-end runtime remains open. |
| Theorem 9 | A DAG algorithm lifts to general digraphs by SCC contraction, adding at most \(2n\) edges via one in-tree and one out-tree per component. Needs online composition, representative edges, and a budget monotone in demand and endpoint counts. Keeping isolated labels preserves the vertex count. | [SCC lift with exact overhead](OnlineReachabilityPreservers/DagReduction.lean) and prefix monotonicity proved for a DAG algorithm on arbitrary lists. The distinct-demand lift keeps first occurrences after SCC projection. Lean checks preservation of every original request, prefix monotonicity, and the same budget with the \(2n\) overhead when the bound is monotone in the projected demand and endpoint counts. A [separately metered reference](OnlineReachabilityPreservers/AlgorithmSearchWork.lean) returns the same stable deduplication result using at most \(p^2\) pair-equality tests on one \(p\)-entry projected trace. |
| Algorithms 1 and 2, Lemma 10 | Forward and backward growth prefer a previously bought feasible edge at every vertex. Ordered compression keeps new-edge tails and the terminal in the forward case, or the origin and new-edge heads in the backward case. The family is acyclic, its size is exactly \(m+p\) on reachable processed requests starting with an empty preserver, and it excludes bridges with the first or last arc earlier than the river, respectively. | [Growth](OnlineReachabilityPreservers/Growth.lean) and [ordered compression](OnlineReachabilityPreservers/Bridges.lean) checked. |
| Theorem 11 | DAG upper bound for both endpoint promises. The printed proof uses Lemmas 12 and 13 when the average degree is large. | [Both orientations](OnlineReachabilityPreservers/Restricted.lean) use a direct count of collisions between new-edge tails, which uses the same earlier-edge conflicts as the forbidden-bridge proof and handles shared endpoints. The exact bound also covers small average degree. |
| Lemma 12 | Reverse-arrival insertion has a path with at least \(\ell/4\) vertices of degree at least \(d/4\) at insertion. | [Checked](OnlineReachabilityPreservers/RestrictedIncidence.lean) for any positive-mass finite family. The degree counts the current path and all previously inserted paths. The statement uses exact integer inequalities with denominators cleared. |
| Lemma 13 | For distinct sink-restricted requests and sufficiently large average degree, the compressed size satisfies \(\ell d\le O(\lvert S\rvert)\). | [Checked](OnlineReachabilityPreservers/RestrictedIncidence.lean) with constant 24 and \(d\ge2\), by combining the exact new-edge-tail estimate with \(p\le n\lvert S\rvert\). The checked argument uses the compressed mass including the terminal of each request. |
| Lemma 14, cited [8] | Independence lemma connects bridge-free path systems to extremal offline preserver size. The constructive direction uses minimally necessary edges and shortcutting, with tightness in the extremal sense. | The [DAG upper direction](OnlineReachabilityPreservers/OfflineIndependence.lean) and [exact acyclic lower construction](OnlineReachabilityPreservers/AcyclicOverlay.lean) are checked. The [general upper direction](OnlineReachabilityPreservers/OfflineBridgeExtremalUpper.lean#L56) bounds the actual lifted preserver by \(3M\) for positive budgets, with \(|E(H)|+p\le M+2n\) and \(M\) the unrestricted fully bridge-free maximum in the indexed simple-path convention. The [acyclic extremal lower bound](OnlineReachabilityPreservers/OfflineDemandLower.lean) uses exactly the original vertex and distinct-demand counts. The exact-count DAG lower constructions use Definition 1, which permits padding with unreachable pairs. The [ordered-block reduction](OnlineReachabilityPreservers/OfflineOrderedBlocks.lean) gives an exact-count DAG lower bound within factor \(12b\) of the mass of any simple nonempty full-bridge-free family whose paths each have at most \(b\) increasing blocks in one order. One common numbering with at most one descent per path gives factor 24. If that numbering exists after pruning opposite intersections, the original mass is bounded within factor 48. [Coordinate triangles](OnlineReachabilityPreservers/TriangularCoordinatePaths.lean#L485) give fully bridge-free families requiring arbitrarily many blocks in any common numbering after pruning. The [subsequence reduction](OnlineReachabilityPreservers/OfflineOrderedBlocks.lean#L69) also uses the total mass retained by arbitrary increasing subsequences in a common order. The [component-visit construction](OnlineReachabilityPreservers/OfflineOrderedBlocks.lean#L184) keeps one vertex per strongly connected component of the precedence graph on each path. If each path meets each component in at most \(b\) vertices, it gives factor \(12b\), with the exact original vertex and distinct-demand counts. One vertex per visit can lose an arbitrarily large factor even after opposite pruning. If the incidence mass satisfies \(M\le C(n+J)\), where \(J\) counts all path-component visits, the [aggregate lower construction](OnlineReachabilityPreservers/OfflineComponentOrders.lean#L240) gives factor \(14C\) for \(n\ge 2\) and \(1\le p\le n^2\). It selects either the spanning path or the component-visit graph. The bound follows by summing [linear incidence caps](OnlineReachabilityPreservers/OfflineComponentOrders.lean#L270) in the separate components and gives [factor \(28C\)](OnlineReachabilityPreservers/OfflineComponentOrders.lean#L308) when the caps are applied after opposite pruning. A [lattice family with private return paths](OnlineReachabilityPreservers/OverlayLowerAudit.lean#L509) gives arbitrarily large \(M/(n+J)\) even after pruning, with every path in one precedence component. A uniform bound on the mass retained by independently ordered subsequences within each component would extend to the whole family. [Component proofs](OnlineReachabilityPreservers/OfflineComponentOrders.lean) The [converse in two demand regimes](OnlineReachabilityPreservers/OfflineConverseRegimes.lean) allows cyclic simple path systems with no full bridge through size four and proves the bound when \(p^2\le K n\) or \(n^2\le Kp\), with factor \(C K\). It combines Theorem 43 with linear lower constructions. The overlay uniqueness step fails [even with unique intersections](OnlineReachabilityPreservers/UniqueSplitAudit.lean). The [unbounded gap for the cited overlay](OnlineReachabilityPreservers/OverlayLowerAudit.lean) shows that even a constant-factor edge lower bound can fail for that graph and those endpoint demands. The [acyclic lattice family](OnlineReachabilityPreservers/OverlayLowerAudit.lean) forces \(L^7\) edges on \(4(L+1)L^5\) vertices with exactly \(L^6\) distinct feasible demands for \(L\ge1\). The [all-sizes lattice lower bound](OnlineReachabilityPreservers/OfflineLatticeLower.lean) gives a DAG forcing \(\Omega(n+p+n^{2/3}p^{1/2})\) edges at every exact count \(n\ge 2\), \(1\le p\le n^2\). A [multidimensional lattice](OnlineReachabilityPreservers/OverlayLowerAudit.lean) uses one coordinate for the squared norm of the slope vector. For any positive number of free slope coordinates, Lean fits the grid to the exact vertex and demand budgets. With \(d-1\) slope coordinates the [lower rate](OnlineReachabilityPreservers/OfflineLatticeLower.lean) is \(n^{2/(d+1)}p^{(d-1)/d}\) for \(d\ge2\), with a constant depending on \(d\). The [all-range comparison with a polynomial loss](OnlineReachabilityPreservers/OfflineConverseRegimes.lean) combines three lattice rates with Theorem 43. Its loss factor is \(C n^{(7-8/\sqrt{2})/10}\). At \(p=n^{6/5}\), the unrestricted collection of normalized lattice powers is bounded by \(n^{13/10}\), which is attained by the two- and three-coordinate rates. The unrestricted converse with a constant factor remains open. |
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
lower bound when the late phase starts. Formal runtime remains open.

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

The [reverse-search tally](OnlineReachabilityPreservers/DeterministicListWork.lean#L585)
also charges list-cell inspection and construction and loop control. The
[SCC preparation tally](OnlineReachabilityPreservers/SccListWork.lean#L405)
extends this model to the transpose, component labels, and exact
duplicate-free quotient.

The [forward-run tally](OnlineReachabilityPreservers/DeterministicListWork.lean#L716)
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

The [incremental thin evaluator](OnlineReachabilityPreservers/SteinerThinReplay.lean#L631)
initializes one dense load table for a nonempty thin run, carries it
forward through the thin requests inside each evaluated late prefix, and
uses the rounded graph already computed for the final check when all checks
pass. The
[thin work bound](OnlineReachabilityPreservers/SteinerThinReplay.lean#L700)
covers that initialization, indexed updates on separating cuts, and
indexed rounding with repeated doubling. The [late equality](OnlineReachabilityPreservers/SteinerLateReplay.lean#L284)
preserves the rounded graph and previous search tally for every trace,
including the missed-thick fallback. The [complete replay specification](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L825)
preserves every earlier record and the evaluation count for every fixed
bit sample. With reachable requests, the [prefix bound](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L887)
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
[thin bound](OnlineReachabilityPreservers/SteinerThinReplay.lean#L724)
uses the feasible trace's bound on the number of calls. The [complete replay](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L905)
includes this charge in the fixed-height polynomial and returns the same
prefix graphs on feasible traces. The [record equality](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L842)
also holds on exhaustion and infeasible traces.

The [capacity preparation](OnlineReachabilityPreservers/SeparatorWork.lean#L803)
initializes one pair table per cut search and evaluates a capacity once
for each arc in the demand interval. The [residual scan](OnlineReachabilityPreservers/SeparatorWork.lean#L894)
reads the stored capacity and signed flow at each ordered pair and constructs
the exact residual graph. It reuses one list of pair addresses across
augmentations and the final source-side search. The [separator specification](OnlineReachabilityPreservers/SeparatorWork.lean#L1084)
preserves the returned cut and the earlier search tally for every load
function. The additional work bound uses the load exponents' bound along
feasible thin traces. The [complete prefix theorem](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L951)
includes these charges in a fixed-height polynomial on feasible traces.

The [list route search](OnlineReachabilityPreservers/AssignmentListRouteWork.lean)
builds the same hop-decreasing graph and selects the same shortest route
in every residual graph. It uses the reachable list both to select the
route and to recover the previous successor-test count. The previous arc
inspection count is recovered from the two arc counts and the search depth.
The [cut comparison](OnlineReachabilityPreservers/SeparatorWork.lean#L1240)
also meters finding the terminal source side from the reversed residual
list. It returns the previous cut and search tally for every capacity
table and augmentation supply. The [complete prefix theorem](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L996)
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
The [complete prefix theorem](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1058)
includes these charges in the fixed-height polynomial on feasible traces.

The late phase also scans the stored arc list to choose the least sampled
hub for each non-self arrival and build the two ordered hub-leg lists.
The same list drives the short-circuit test for a missed thick demand.
The replay has the same graph and search records and the same number of
evaluations for all inputs. On feasible traces, the fixed-height
polynomial includes the new interval and trace-list operations.
[Hub selection and fallback scans](OnlineReachabilityPreservers/SteinerLateIntervalWork.lean)
· [Complete prefix bound](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1139).

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
· [Complete prefix bound with routing](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1440).

The outer union uses a single filter of the late graph against the early
arc set and a disjoint list append. Both operations have explicit
word counts. The complete evaluator uses this union at each evaluated prefix. All graph and search records and the evaluation
count agree with the earlier replay for every input. The fixed-height
bound includes the new union on feasible traces. Early weighted work,
the remaining thin service operations, other container operations, bit
costs, and native costs remain open.
[Exact metered union](OnlineReachabilityPreservers/SteinerPhaseUnionWork.lean#L70)
· [Unchanged records](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1397)
· [Complete prefix bound](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1459).

The weighted run can also consume a supplied list of all ordered pairs
with each pair listed once. It stores accepted cuts in reverse order
for charge reads and returns them in their original order. The
[weighted history evaluator](OnlineReachabilityPreservers/SteinerWeightedChargeWork.lean)
proves equality of all charge values and the full cut list at the
same scale and fuel. Its bound includes explicit membership scans,
charge reads, integer capacity arithmetic with doubling, outgoing
cut selection, and the earlier residual search counts. The proof
also bounds each read of a returned charge. Constructing the list
for the metric forest and threading the evaluator through complete
early replay remain open.

The [integer magnitude bounds](OnlineReachabilityPreservers/SteinerIntegerBounds.lean)
control the signed flow entries by the augmentation supply, the thin
capacities by twice the number of arcs, and the weighted capacities by
four times the forest scale plus one. The [weighted numerator bound](OnlineReachabilityPreservers/SteinerRoundedCapacities.lean)
is \((4S+1)c\) with positive scale \(S\), cost \(c\), and the checked load cap.
The forest threshold operands are
polynomial in the scale. The thin rounding comparison on each feasible
prefix has an operand bound of \((5n+4)\cdot 2|E|\).

## Appendix dependencies

For Lemmas 23 and 39, the [contiguous six-bridge lift](OnlineReachabilityPreservers/CyclicSplits.lean)
uses the original relative order of pieces in addition to the mirrored-cut
condition. It assumes full exclusion through size three. With unique
intersections and mass at least both positive input counts, the
[checked width-block cleaning](OnlineReachabilityPreservers/ContiguousSixCleaning.lean)
preserves full exclusion through size six with both original budgets and
all four frozen caps, retaining at least one sixteenth of the input mass.
The half-bridge version at size six requires full exclusion through size
four for the vertex-copy step. The general cyclic existence claims remain
open. The size-seven counterexample below applies to the printed midpoint
split. The factor-four block split before trimming and peeling also creates
a full size-seven bridge in the dense branch on a simple input with unique
intersections, all-size full exclusion, and zero pruning loss.
[Dense width-block counterexample](OnlineReachabilityPreservers/FrozenWidthSplitAudit.lean#L558).

At full cutoff six, [output-average cleaning](OnlineReachabilityPreservers/LocalAverageCleaning.lean)
starts at the unrestricted maximum over indexed simple paths. It retains
at least \(M/392\) of the maximizing mass \(M\), keeps both budgets, and
meets all four factor-four caps around the cleaned witness's own averages.
The same construction preserves half exclusion through six for an input
that also excludes full bridges through four and whose mass is at least
both positive budgets. At full cutoff six, the unrestricted statement with
the original fixed averages remains open.

An opposite-neighbor link joins consecutive common vertices of two
oppositely ordered paths. In an input excluding full bridges through size
three, a simple cycle of \(r\) links produces a full bridge of size at most
\(r\). At full cutoff \(k\ge3\), every cycle has length greater than \(k\).
The existing pruning charges each removed incidence to a distinct link
using half exclusion through size two. With full exclusion at every size,
the link graph is a forest and the loss is at most \(n-1\) for \(n>0\).
[Cycle bound](OnlineReachabilityPreservers/OppositeLinkForest.lean#L327)
· [Finite cutoff](OnlineReachabilityPreservers/OppositeLinkForest.lean#L406)
· [Charge in half mode](OnlineReachabilityPreservers/OppositeLinkForest.lean#L464)
· [Pruning bound](OnlineReachabilityPreservers/OppositeLinkForest.lean#L524).

For simple paths with full exclusion through six or half exclusion through
four, let \(E\) count these links. If \(M\ge8E\) and the mass \(M\) is
at least both positive budgets, there is a cleaned family within both
budgets with the input's cutoff and bridge mode, all four original-average
caps, and mass at least \(M/32\).
[Full cutoff six](OnlineReachabilityPreservers/ContiguousSixCleaning.lean#L136)
· [Half cutoff four](OnlineReachabilityPreservers/ContiguousHalfCleaning.lean#L335).

For an input excluding full bridges at every size, the same size-six
cleaning conclusion holds at every mass at least both positive budgets.
The lower-mass case uses explicit witnesses. The larger-mass case uses the
forest bound and the original cap widths.
[All-size input](OnlineReachabilityPreservers/ContiguousSixCleaning.lean#L151).

| Source | Mathematical obligation |
| --- | --- |
| Definition 2 | Half-\(k\)-bridge-free means no bridge of size at most \(k\) whose last arc precedes the river. |
| Lemmas 23 and 39 | [Acyclic cleaning](OnlineReachabilityPreservers/BalancedRegularization.lean) checks both original budgets, all four degree and length caps, and retention of at least one sixteenth of the original mass when the mass is at least both original counts. It preserves the bridge exclusions at every size. [Local cleaning](OnlineReachabilityPreservers/LocalBalancedRegularization.lean) gives the same budgets and caps through size four under unique intersections and through size three for arbitrary simple paths with mass at least both counts. For simple paths excluding half-bridges through size four whose mass is at least twice both counts, [opposite-intersection pruning](OnlineReachabilityPreservers/OppositeIntersectionPruning.lean) followed by local cleaning gives both original budgets, at least one thirty-second of the mass, lower caps at one eighth of the original averages and upper caps at four times those averages. It preserves the half exclusion and preserves full exclusion when the input has it. The [pruning bound with first incidences](OnlineReachabilityPreservers/OppositeIntersectionPruning.lean) retains at least \((M+s)/2\) incidences, where \(s\) is the number of original nonempty paths. At a maximum with positive vertex budget, \(s=p\). [Two opposite rows](OnlineReachabilityPreservers/OppositePruningGain.lean) attain equality for every positive vertex count. If every original path is nonempty, the pruned paths satisfy both upper caps, and the original mean path length is at most \(C\), the [frozen peeling argument](OnlineReachabilityPreservers/LocalFrozenCleaning.lean) yields both budgets, all four original-average caps, and retention at least \(M/(2C)\). [Output-average cleaning](OnlineReachabilityPreservers/LocalAverageCleaning.lean) gives a witness at the unrestricted size-four maximum in either bridge mode. It meets both budgets, retains at least one 392nd of the maximizing mass, and keeps all four factor-four caps relative to the witness's averages. [Full-bridge cleaning with frozen averages](OnlineReachabilityPreservers/LocalFrozenCleaning.lean) retains at least one 119th of the maximum without unique intersections, within both original budgets and all four original-average caps at full bridge cutoffs three through five. When the mass lies between the larger budget and eight times it, the [low-mass witnesses](OnlineReachabilityPreservers/LocalFrozenLowMass.lean) retain at least one eighth of the mass and meet both budgets and all four original-average caps. They exclude every full bridge, and apply to both modes for simple families excluding half-bridges at a cutoff of at least two. This includes every unrestricted maximum when either positive budget is at most eight. [Length truncation](OnlineReachabilityPreservers/LocalFrozenCleaning.lean) and [a common vertex partition](OnlineReachabilityPreservers/VertexPartitionCleaning.lean) give both budgets, all four frozen caps and mass at least \(M/16\) when the length-capped subsystem fits both original budgets and still has at least \(3M/4\) incidences. Keeping the pieces of a common partition preserves both bridge exclusions at every cutoff. The subsequent vertex split is justified for full bridges at every cutoff and for half-bridges through size four. Already capped degrees also suffice at any cutoff. Both shared partitions can also be applied together. The [occupied-support cleaning theorem](OnlineReachabilityPreservers/CommonPartitionCleaning.lean) preserves mass and both exclusions at every cutoff while splitting every incidence by its path and vertex parts. It counts only occupied copies and pieces, using the number of incident parts of each original vertex and each original path. If the full mass meets the two upper caps after partitioning and each occupied support fits within four thirds of its original budget, a restriction to both budgets has all four frozen caps and at least \(M/16\) mass. The common-partition proof also gives an explicit grouping criterion in terms of occupied input supports, upper-cap capacities, and the numbers of opposite groups. [Ordered-path cleaning](OnlineReachabilityPreservers/ContiguousHalfCleaning.lean) retains \(M/16\) and all four frozen caps through size four by splitting, restriction, and peeling for simple paths with positive budgets and mass at least both counts, when there are no two distinct partners reversing strictly nested intervals with the inner partner later than the split parent. For any fixed ordered disjoint split, half-4 exclusion is equivalent to the absence of a nested reversal whose required four steps all survive in the pieces. [Synchronized cleaning](OnlineReachabilityPreservers/LocalFrozenCleaning.lean) keeps both budgets, all four original caps and at least \(M/119\) for simple systems with a half cutoff from three through five that also exclude full bridges through size three. A collision under the degree-split projection would erase at least two steps and leave a forbidden full bridge. Mirrored path cuts then preserve the half exclusion up to size five. The [average-width examples](OnlineReachabilityPreservers/AverageSplitAudit.lean) exhibit the failure after the printed mean-width midpoint procedure terminates and after the exact factor-four-width block split. The same audit proves that every arrival permutation of one fully bridge-free family still has the nested obstruction. The general half-bridge case of the frozen caps at cutoff four and the arbitrary-cutoff cyclic statements remain open. The printed path split can create a [half-7-bridge with unique intersections](OnlineReachabilityPreservers/UniqueSplitAudit.lean). The degree split can create a [half-5-bridge without unique intersections and a half-6-bridge with unique intersections](OnlineReachabilityPreservers/VertexSplitAudit.lean). The same split preserves full exclusion at all sizes. |
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
frozen caps. The unrestricted cyclic result remains open.

For Lemmas 23 and 39, the [common-order extremal theorem](OnlineReachabilityPreservers/CommonOrderExtremal.lean)
uses a finite maximum. For every positive pair of budgets and either
bridge exclusion it gives one subsystem with both budgets and all four
caps, retaining at least one sixteenth of the maximum.

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
