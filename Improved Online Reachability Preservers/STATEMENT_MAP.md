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
| Theorem 1 | Adaptive deterministic polynomial-time pairwise online bound. The sharp terms are \(n^{(2+\alpha)/(3+\alpha)+o(1)}p^{2/(3+\alpha)}\) and \(n^{2-2\alpha+o(1)}p^\alpha\), with \(+n\) and \(\alpha\in(0.700,0.701)\) the middle root of the printed cubic. The rounded upper bound is \(O(n^{.72}p^{.56}+n^{.6}p^{.7}+n)\). Uses Theorem 9, Lemma 10, and Appendix A through Theorem 38. | [Both edge bounds](OnlineReachabilityPreservers/OnlineSharp.lean) hold at every prefix on general digraphs. A single function of the vertex count with limit zero supplies the unrounded slack uniformly over demand counts. Formal runtime remains open. |
| Theorem 2 | One of the two endpoint promises \(P\subseteq S\times V\) and \(P\subseteq V\times S\). Adaptive deterministic bound \(O(\sqrt{np\lvert S\rvert}+n)\) on general digraphs, including prefixes, with no advance knowledge of \(S,p\). Uses Theorems 9 and 11. | [Both orientations](OnlineReachabilityPreservers/DagReduction.lean) proved on general digraphs with an explicit finite edge bound. Formal runtime certification pending. |
| Theorem 3, cited [8] | Lower bound \(\Omega((np)^{2/3}+n)\) against the stronger adversary that starts with an empty graph and inserts edges before each demand. Definition 18 of [8](https://arxiv.org/pdf/2212.11944v4) gives the game, Theorem 29 gives the lattice, and Lemma 45 states a general transfer. | [Checked](OnlineReachabilityPreservers/StrongAdversary.lean) for exact counts \(n\ge2\) and \(1\le p\le n^2\), with distinct feasible demands and constant 576. The proof forces every edge of each revealed line directly from its slope. |
| Theorem 4 | Offline deterministic polynomial-time pairwise bound \(O(n^{3/4}p^{1/2}+n^{2-\sqrt2+o(1)}p^{1/\sqrt2}+n)\), also rounded to \(O(n^{.75}p^{.5}+n^{.59}p^{.71}+n)\). Uses the independence construction in Lemma 14 and the Appendix B extremal estimate, with degeneracies and the additive \(p\) handled in the graph bound. | [Both edge bounds](OnlineReachabilityPreservers/OfflineSharp.lean) hold for the constructed preserver on general digraphs. The limiting bound holds with zero exponent slack. Formal runtime remains open. |
| Theorem 5 | Both Theorems 1 and 2 transfer to preassigned simple paths, either with the total \(p\) known or with the arrival index \(i\) as a path-selection input. In the restricted case \(S\) is given. Uses Theorems 15 and 16. Fully non-adaptive path selection with neither parameter is left open. | The [pairwise rates](OnlineReachabilityPreservers/PairwiseNonAdaptive.lean) and [both endpoint promises](OnlineReachabilityPreservers/RestrictedNonAdaptive.lean) are checked for both models on general digraphs. The [path lift](OnlineReachabilityPreservers/PathAssignments.lean) uses a subset of the shared connectors in each simple path. Formal runtime remains open. |
| Theorems 6 and 7, cited [1,15,21] | Prior offline approximation with \(\min(n^{4/7+\varepsilon},p^{1/2+\varepsilon})\) and online competitive ratio \(\widetilde O(p^{1/2+\varepsilon})\) from [21]. | Cited background |
| Theorems 8 and 21 | Same new online unit-cost directed Steiner forest result, randomized polynomial time and competitive ratio \(O(n^{3/5+\varepsilon})\). Theorem 21 uses the early-pair algorithm of [21], all-pairs thick-demand hitting, the thin-pair online rounding from the [24] framework, the two orientations of Theorem 2, and Lemmas 20 and 22. | [The full online algorithm](OnlineReachabilityPreservers/SteinerComplete.lean) checks the expected \(O(n^{3/5+\varepsilon})\) rate against any feasible offline solution on a fixed demand trace, including zero optimum and repeated requests. The first block of distinct non-self requests is chosen independently of the random seeds. Correctness and monotonicity hold on every realization. Formal end-to-end runtime remains open. |
| Theorem 9 | A DAG algorithm lifts to general digraphs by SCC contraction, adding at most \(2n\) edges via one in-tree and one out-tree per component. Needs online composition, representative edges, and a budget monotone in demand and endpoint counts. Keeping isolated labels preserves the vertex count. | [SCC lift with exact overhead](OnlineReachabilityPreservers/DagReduction.lean) and prefix monotonicity proved for a DAG algorithm on arbitrary lists. The distinct-demand lift keeps first occurrences after SCC projection. Lean checks preservation of every original request, prefix monotonicity, and the same budget with the \(2n\) overhead when the bound is monotone in the projected demand and endpoint counts. A [separately metered reference](OnlineReachabilityPreservers/AlgorithmSearchWork.lean) returns the same stable deduplication result using at most \(p^2\) pair-equality tests on one \(p\)-entry projected trace. |
| Algorithms 1 and 2, Lemma 10 | Forward and backward growth prefer a previously bought feasible edge at every vertex. Ordered compression keeps new-edge tails and the terminal in the forward case, or the origin and new-edge heads in the backward case. The family is acyclic, its size is exactly \(m+p\) on reachable processed requests starting with an empty preserver, and it excludes bridges with the first or last arc earlier than the river, respectively. | [Growth](OnlineReachabilityPreservers/Growth.lean) and [ordered compression](OnlineReachabilityPreservers/Bridges.lean) checked. |
| Theorem 11, Lemmas 12 and 13 | DAG restricted bound. Lemma 12 selects a path with many high-incidence vertices in reverse-arrival insertion. Lemma 13 groups later incidences by sink and uses forbidden ordered 2- and 3-bridges. Exact counting of new-edge tails gives the same bound and handles the shared-endpoint case explicitly. | [Both cases](OnlineReachabilityPreservers/Restricted.lean) checked with the exact incidence argument. |
| Lemma 14, cited [8] | Independence lemma connects bridge-free path systems to extremal offline preserver size. The constructive direction uses minimally necessary edges and shortcutting, with tightness in the extremal sense. | The [DAG upper direction](OnlineReachabilityPreservers/OfflineIndependence.lean) and [exact acyclic lower construction](OnlineReachabilityPreservers/AcyclicOverlay.lean) are checked. The SCC lift applies the acyclic upper bound to general digraphs. The [acyclic extremal lower bound](OnlineReachabilityPreservers/OfflineDemandLower.lean) uses exactly the original vertex and distinct-demand counts. The [converse in two demand regimes](OnlineReachabilityPreservers/OfflineConverseRegimes.lean) allows cyclic simple path systems with no full bridge through size four and proves the bound when \(p^2\le K n\) or \(n^2\le Kp\), with factor \(C K\). It combines Theorem 43 with linear lower constructions. The overlay uniqueness step fails [even with unique intersections](OnlineReachabilityPreservers/UniqueSplitAudit.lean). The [unbounded gap for the cited overlay](OnlineReachabilityPreservers/OverlayLowerAudit.lean) shows that even a constant-factor edge lower bound can fail for that graph and those endpoint demands. The [acyclic lattice family](OnlineReachabilityPreservers/OverlayLowerAudit.lean) forces \(L^7\) edges on \(4(L+1)L^5\) vertices with exactly \(L^6\) distinct feasible demands for \(L\ge1\). The [all-sizes lattice lower bound](OnlineReachabilityPreservers/OfflineLatticeLower.lean) gives a DAG forcing \(\Omega(n+p+n^{2/3}p^{1/2})\) edges at every exact count \(n\ge 2\), \(1\le p\le n^2\). The unrestricted converse for all demand counts remains open. |
| Algorithm 3 and Theorem 15 | For a deterministic current-state path rule with a uniform prefix budget \(F\) at \(p>0\), buy paths with more than \(F/p\) missing edges before assigning the remaining paths against the frozen graph. Fewer than \(p\) such purchases, and any \(p\) preassigned paths have union size at most \(2F\). Use the allowed demand domain for the restricted case. | [Checked](OnlineReachabilityPreservers/KnownBudget.lean), with strict integer comparison and preservation of the rule's paths. |
| Algorithms 4–5 and Theorem 16 | Precompute Algorithm 3 at positive dyadic budgets \(q\) starting at a linear-cost threshold. The arrival index chooses its first covering budget. Footnote 4 requires the sum of dyadic bounds to be dominated by the final term and bounded doubling of the bound. For \(p\) below the starting threshold, use the linear term directly. Domains and planned budgets can be capped by the finite pair population or the number of distinct arrivals. | [Checked](OnlineReachabilityPreservers/IndexSensitive.lean) under the two growth inequalities specified by footnote 4, with explicit constants and executable dyadic selection. |
| Theorems 17–19 and Lemma 20 | Prior algorithm of [24] and its early- and thin-demand routines. Lemma 20 lower-bounds OPT by a constant times \(\sqrt p\) for distinct nontrivial demands via terminal incidence. | [Lemma 20](OnlineReachabilityPreservers/SteinerCounting.lean) checks \(p\le \mathrm{OPT}^2\) for sets and for nontrivial online traces. [Cut covering](OnlineReachabilityPreservers/SteinerThinCover.lean) and [fixed-threshold rounding](OnlineReachabilityPreservers/SteinerThinRound.lean) prove irrevocable thin-demand feasibility and expected edge cost on fixed traces of distinct non-self thin requests. The [separator](OnlineReachabilityPreservers/SteinerCutFlow.lean) uses bounded unit augmentations. The [early rooted-tree comparison](OnlineReachabilityPreservers/SteinerJunction.lean) checks distinct roots and rooted route prefixes. The [height-reduction interval bound](OnlineReachabilityPreservers/SteinerHeightIntervals.lean) and [fractional forest run](OnlineReachabilityPreservers/SteinerForestNetwork.lean) are checked. The [integral early algorithm](OnlineReachabilityPreservers/SteinerEarlyRound.lean) supplies the early routine for Theorems 8 and 21. |
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
A binary search returns the canonical rank of any present key with at most
as many key comparisons as the bit length of the array size. Inverse ranks
read the corresponding stored position.
The [bit cursor](OnlineReachabilityPreservers/SteinerBitCursor.lean) reads
the requested positions directly, with a tail-recursive word accumulator. The
[cursor decoder](OnlineReachabilityPreservers/SteinerBitSeed.lean) agrees with
the list decoder on the sampled seed, rejection counts, unread suffix,
and failure. The cached replay uses the cursor from position zero. Integer
arithmetic, finite container operations, and full execution time still
require certification.
The [preassigned-path counter](OnlineReachabilityPreservers/AssignmentSearchWork.lean)
combines the calls made by quota certification and path selection with the
arc inspections and successor tests in each base rule and lifted path.
This covers known totals and arrival indices in all three endpoint scopes.
The indexed pairwise evaluator returns the ordinary union of all assigned
paths in one prefix and sums their search work. The quota count is bounded
by a polynomial in the graph sizes and the known total or current index.
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
arithmetic coordinate count. Index construction, the arithmetic in index
lookups, and the time cost of the remaining container operations still need bounds.
The [integer magnitude bounds](OnlineReachabilityPreservers/SteinerIntegerBounds.lean)
control the signed flow entries by the augmentation supply, the thin
capacities by twice the number of arcs, and the weighted capacities by
four times the forest scale plus one. The [weighted numerator bound](OnlineReachabilityPreservers/SteinerRoundedCapacities.lean)
is \((4S+1)c\) with positive scale \(S\), cost \(c\), and the checked load cap.
The forest threshold operands are
polynomial in the scale. The thin rounding comparison on each feasible
prefix has an operand bound of \((5n+4)\cdot 2|E|\).

## Appendix dependencies

| Source | Mathematical obligation |
| --- | --- |
| Definition 2 | Half-\(k\)-bridge-free means no bridge of size at most \(k\) whose last arc precedes the river. |
| Lemmas 23 and 39 | [Acyclic cleaning](OnlineReachabilityPreservers/BalancedRegularization.lean) checks both original budgets, all four degree and length caps, and retention of at least one sixteenth of the original mass when the mass is at least both original counts. It preserves the bridge exclusions at every size. [Local cleaning](OnlineReachabilityPreservers/LocalBalancedRegularization.lean) gives the same budgets and caps through size four under unique intersections and through size three for arbitrary simple paths with mass at least both counts. For simple paths excluding half-bridges through size four whose mass is at least twice both counts, [opposite-intersection pruning](OnlineReachabilityPreservers/OppositeIntersectionPruning.lean) followed by local cleaning gives both original budgets, at least one thirty-second of the mass, lower caps at one eighth of the original averages and upper caps at four times those averages. It preserves the half exclusion and preserves full exclusion when the input has it. [Output-average cleaning](OnlineReachabilityPreservers/LocalAverageCleaning.lean) gives a witness at the unrestricted size-four maximum in either bridge mode. It meets both budgets, retains at least one 392nd of the maximizing mass, and keeps all four factor-four caps relative to the witness's averages. [Full-bridge cleaning with frozen averages](OnlineReachabilityPreservers/LocalFrozenCleaning.lean) retains at least one 119th of the maximum without unique intersections, within both original budgets and all four original-average caps at full bridge cutoffs three through five. The half-bridge case of the frozen caps at cutoff four and the arbitrary-cutoff cyclic statements remain open. The printed path split can create a [half-7-bridge with unique intersections](OnlineReachabilityPreservers/UniqueSplitAudit.lean). The degree split can create a [half-6-bridge with unique intersections](OnlineReachabilityPreservers/VertexSplitAudit.lean), despite preserving full exclusion at all sizes. |
| Definition 3 and Lemma 24 | In a triple of distinct path indices, the middle path meets \(\pi_1\) before meeting \(\pi_3\), with \(\pi_3\) earlier in arrival order than the middle path. [CyclicIntersections](OnlineReachabilityPreservers/CyclicIntersections.lean) proves the fiber bound for arbitrary simple paths and the left and right order properties when a witness is chosen for each middle path. The right order becomes strict under full bridge-freeness. Multiple witnesses for one middle path can occur. [IntersectionOrder](OnlineReachabilityPreservers/IntersectionOrder.lean) proves uniqueness under a common vertex order for the incidence counts downstream. |
| Lemmas 25–27 | The corrected tail inequality is checked in [SourceAudit](OnlineReachabilityPreservers/SourceAudit.lean). [GeneralInitial](OnlineReachabilityPreservers/GeneralInitial.lean) proves the chain lower count for distinct path triples and the initial \(O(n+(np)^{2/3}+p)\) incidence bound for arbitrary ordered simple paths. Opposite-intersection pruning provides unique witnesses before counting, and every retained triple is a triple in the original paths. [PairwiseInitial](OnlineReachabilityPreservers/PairwiseInitial.lean) uses the same threshold argument in the common-order case. |
| Lemma 28 | Close pairs in the ordered \(R\)-fibers charge into sampled branching subsystems. For \(\ell\ge h\ge Cp/(\ell d^2)\), the mean \(Q\)-count is \(\Omega(h\sum_R\lvert R\rvert^2/(\ell p))\). [LocalBranching](OnlineReachabilityPreservers/LocalBranching.lean) proves the finite lower comparison and its dense normalization for local path orders with unique intersections. Every online charge with its right endpoint on the base has its left start before that endpoint on the base. The full-bridge-free charges have both endpoints off the base. [BranchWindow](OnlineReachabilityPreservers/BranchWindow.lean) supplies the common scaling arithmetic. The right-side distance uses the two distinct middle paths. |
| Lemmas 29–31 | [Weak majorization](OnlineReachabilityPreservers/Majorization.lean) and its [integral version](OnlineReachabilityPreservers/IntegralMajorization.lean) are checked. [SecondMoment](OnlineReachabilityPreservers/SecondMoment.lean) proves the acyclic second-moment estimate with explicit constants from the inductive size bound on subfamilies. The proof sorts the path indices and bounds clipped powers. |
| Lemmas 32–33 | [LocalBranchingDegrees](OnlineReachabilityPreservers/LocalBranchingDegrees.lean) checks the count for all long paths in the actual predecessor subsystem and for the subset of base paths avoiding the fixed vertex. It gives the expected high-degree count for thresholds above the envelope constant and the deterministic incidence bound. Each path has its own order. The branching identity uses unique intersections. |
| Lemmas 34–36 | [LocalBranchingDegrees](OnlineReachabilityPreservers/LocalBranchingDegrees.lean) bounds \(Q_1\) by weighted middle-path squares in local orders. [LocalOffBaseMoment](OnlineReachabilityPreservers/LocalOffBaseMoment.lean) checks the dyadic triangle inequality and each sampled moment in the actual subsystems. [LocalOffBaseAverage](OnlineReachabilityPreservers/LocalOffBaseAverage.lean) proves the full off-base expectation. The printed source inference has a [checked counterexample](OnlineReachabilityPreservers/SplitAudit.lean). [LocalOnBaseCounting](OnlineReachabilityPreservers/LocalOnBaseCounting.lean) handles on-base targets after a near predecessor via source-restricted suffixes. [LocalFullOnBaseCounting](OnlineReachabilityPreservers/LocalFullOnBaseCounting.lean) counts targets before a near predecessor via half-3 and half-4-bridge exclusions and combines both directions. With unique intersections, the uniform caps and the inductive envelope, [LocalOnlineAverage](OnlineReachabilityPreservers/LocalOnlineAverage.lean) proves both terms for all \(Q_2\) tuples and the full \(Q\) expectation with the paper's exponents and without logarithmic loss. |
| Lemma 37 and Theorem 38 | [OnlineBound](OnlineReachabilityPreservers/OnlineBound.lean) compares the lower and upper \(Q\)-bounds with \(h\asymp p/(\ell d^2)\), including \(h>\ell\) and \(h>d\). [OnlineArithmetic](OnlineReachabilityPreservers/OnlineArithmetic.lean) absorbs the two lower-order terms. [LocalOnlineBound](OnlineReachabilityPreservers/LocalOnlineBound.lean) proves the corrected update with unique intersections and all finite iterates for arbitrary simple paths with the half-bridge exclusion through four. [LocalOnlineLimit](OnlineReachabilityPreservers/LocalOnlineLimit.lean) proves the unrestricted limiting bound with a single slack function tending to zero in \(n\) and one constant uniform in both \(n\) and \(p\). [OnlineSharp](OnlineReachabilityPreservers/OnlineSharp.lean) gives the unrounded graph rate. |
| Lemmas 40–42 and Theorem 43 | [LocalOfflineCounting](OnlineReachabilityPreservers/LocalOfflineCounting.lean) proves Lemma 41's off-base branching uniqueness and injection into the sampled path pairs in local orders. [OfflineMoment](OnlineReachabilityPreservers/OfflineMoment.lean) checks the logarithmic moment from subfamily incidence bounds. [LocalOfflineMoment](OnlineReachabilityPreservers/LocalOfflineMoment.lean) applies it to the actual local-order samples. [OfflineArithmetic](OnlineReachabilityPreservers/OfflineArithmetic.lean) checks the three-term comparison with third term \(n^{1/(b+1)}p^{(2b+1)/(2b+2)}\). [LocalOfflineBound](OnlineReachabilityPreservers/LocalOfflineBound.lean) gives the unrestricted update and a constant uniform over all iterations. At the limit Theorem 43 holds for arbitrary simple paths with the exact exponent \(1/\sqrt2\) and zero exponent slack. |

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
