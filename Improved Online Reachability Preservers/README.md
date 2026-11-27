# Improved Online Reachability Preservers

Lean formalization of [Bodwin–Le, arXiv:2410.20471v1](https://arxiv.org/abs/2410.20471v1).

## Checked results

- [`forwardPath_spec`](OnlineReachabilityPreservers/Growth.lean) proves the
  forward path specification, including priority for previously purchased edges.
  The reachability computation is exact. Each path search uses at most `n` steps.
- [`compressed_total`, `no_earlier_first_arc`, and `no_earlier_last_arc`](OnlineReachabilityPreservers/Bridges.lean)
  cover the counting identity and ordered bridge exclusions in Lemma 10.
  An unreachable request can be represented by a singleton terminal with no purchase.
- [`theorem11_sinks` and `theorem11_sources`](OnlineReachabilityPreservers/Restricted.lean)
  prove a DAG bound of `n + sqrt(2npσ)`. Each collision of purchased edge
  tails is charged to its earlier round and later sink.
- [`theorem9_lift`, `theorem2_sources`, and `theorem2_sinks`](OnlineReachabilityPreservers/DagReduction.lean)
  extend to arbitrary finite directed graphs. The Lean functions take the input graph
  and the revealed prefix. The proof uses `S` only to bound the actual output by
  `3n + sqrt(2npσ)`, with `σ = |S|`. The functions retain all previously bought
  edges and preserve original reachability for every demand in the prefix.
- [Theorem 3](OnlineReachabilityPreservers/StrongAdversary.lean) verifies the
  edge-insertion adversary's lower bound for exact counts `n ≥ 2` and
  `1 ≤ p ≤ n²`. A fixed trace reveals lattice lines in slope order. Serving
  a line's request forces every edge on that line, and earlier purchases
  remain in the final preserver. The proof includes the linear term, integer
  parameter rounding, and padding to exactly `p` distinct requests.
- [`theorem15_known_budget`](OnlineReachabilityPreservers/KnownBudget.lean) verifies
  the known-budget path assignment and the factor-two union bound.
  [`theorem16_index_sensitive`](OnlineReachabilityPreservers/IndexSensitive.lean)
  verifies dyadic assignment using the two growth inequalities in footnote 4.
  The search examines `i.log2 + 2` levels at zero-based index `i`.
- [`theorem5_sinks_known_p`, `theorem5_sources_known_p`, `theorem5_sinks_indexed`, and `theorem5_sources_indexed`](OnlineReachabilityPreservers/RestrictedNonAdaptive.lean)
  verify the endpoint-restricted size and path guarantees of Theorem 5 on
  general digraphs. Write `F = n + floor(sqrt(2npσ))`. The guarantees are
  `2n + 2F` with known `p` and `2n + 48F` with the arrival index, where `p`
  is the prefix length in the indexed bound. The preserver is precisely the
  union of the assigned simple paths, and the assignments give prefix monotonicity.
- [`theorem5_pairwise_rounded` and `theorem5_pairwise_limiting_rate`](OnlineReachabilityPreservers/PairwiseNonAdaptive.lean)
  prove both pairwise rates for both assignment models. The executable rules
  find a certified integer budget by simulating the expensive-pair phase.
  The real-valued rates bound the budget in the proof. The indexed rule uses
  dyadic quotas starting at `Nat.sqrt n + 1` and is correct at every prefix.
- [The Steiner hit phase](OnlineReachabilityPreservers/SteinerHubs.lean)
  proves the exact uniform sample failure count for a fixed pair and an
  inverse-power failure bound over all thick pairs. The complete evaluator
  uses a draw count computed by integer arithmetic. It serves both hub legs
  in original edges with prefix monotonicity and checks the logarithmic
  competitive contribution at the thresholds of Theorem 21.
- [The thin-demand fractional cover](OnlineReachabilityPreservers/SteinerThinCover.lean)
  checks capacity doubling on the local directed cuts. Every request's cuts
  remain covered, and the capacity sum is bounded by
  `1 + OPT * (1 + floor(log₂ |E|))` after normalization when `|E| > 0`.
  [The rounded preserver](OnlineReachabilityPreservers/SteinerThinRound.lean)
  uses a single independent integer threshold per edge. It is correct at
  every prefix, uses a graph purchase on failure, and has the expected
  logarithmic-factor thin-demand edge bound on a fixed distinct trace.
  The [cut separator](OnlineReachabilityPreservers/SteinerCutFlow.lean)
  uses at most `|E|` unit augmentations. When it stops early the residual
  reachable set supplies a violating cut. Lean checks the augmentation and
  doubling counts.
- [The Steiner phase composition](OnlineReachabilityPreservers/SteinerAssembly.lean)
  starts empty, serves every revealed demand, and preserves every purchased
  edge. The [full online algorithm](OnlineReachabilityPreservers/SteinerComplete.lean)
  uses a seed-independent cutoff on distinct non-self requests and
  proves \(O(n^{3/5+\varepsilon})\) expected competitiveness on every
  fixed feasible demand sequence, against any offline solution.
  Every realization serves all prefixes. Formal end-to-end runtime remains open.
- [The late-phase exponent bound](OnlineReachabilityPreservers/SteinerRate.lean)
  uses integer thresholds for \(n^{6/5}\) and \(n^{3/5}\). It absorbs both
  logarithmic losses and the bad-hub cost into \(O(n^{3/5+\varepsilon})\)
  times the offline solution size, with the early purchases kept explicit.
- [The rooted-tree comparison](OnlineReachabilityPreservers/SteinerJunction.lean)
  checks an offline junction cover of cost at most
  `3 * (floor(sqrt p) + 1) * OPT` for unit-cost demands. Heavy edges supply
  roots that cover many requests. Light edges are charged by their path loads.
  Merging pieces at the same root preserves their service without increasing
  cost. The [height-reduction count](OnlineReachabilityPreservers/SteinerHeightIntervals.lean)
  bounds the number of child blocks whose parent straddles either boundary
  of a terminal interval. The [ordered routes](OnlineReachabilityPreservers/SteinerRootOrder.lean)
  show that the terminals using any original arc form such an interval.
  The [shortened routes](OnlineReachabilityPreservers/SteinerHeightBlocks.lean)
  concatenate back to the original routes and charge each original arc at
  most twice the branch count per level.
  The [inward metric tree](OnlineReachabilityPreservers/SteinerHeightTree.lean)
  is built from the graph, a root, and a depth limit. Expanded links
  preserve directed reachability at no more than their metric weight.
  The [forward embedding](OnlineReachabilityPreservers/SteinerHeightEmbedding.lean)
  places each original terminal at a template leaf. For at most \(k\)
  terminals and positive depth \(h\), the embedded cost is at most
  \(4h k^{1/h}\) times the original tree size. The
  [paired forest](OnlineReachabilityPreservers/SteinerHeightForest.lean)
  joins both sides at each root and gives a weighted offline comparator.
  Any selected group paths expand to the original demands at no more
  than the selected metric weight. The
  [forest network](OnlineReachabilityPreservers/SteinerForestNetwork.lean)
  applies the online cut run to these templates with the two current
  groups' directed attachments. It proves full flow for each demand
  and compares the fractional cost to any feasible original solution.
  [Integral rounding](OnlineReachabilityPreservers/SteinerEarlyRound.lean)
  uses independent finite thresholds, reuses the same seeds across
  prefixes, and retains all earlier purchases. The
  [explicit mean cost](OnlineReachabilityPreservers/SteinerOnlineRounding.lean)
  gives the finite early competitive estimate, with the rate conversion
  checked in [SteinerCompetitive](OnlineReachabilityPreservers/SteinerCompetitive.lean).
- [The weighted fractional cover](OnlineReachabilityPreservers/SteinerWeightedCover.lean)
  raises rational capacities as batches of cuts arrive. It verifies coverage
  and bounds both the update count and the cost against any fixed set that
  hits every cut. The competitive factor is logarithmic in the total
  positive integer edge weight. This implementation takes explicitly listed
  cuts, and its update count depends on the numeric weights.
  [Integer capacity rounding](OnlineReachabilityPreservers/SteinerRoundedCapacities.lean)
  adds at most one to the normalized objective. The
  [capacity separator](OnlineReachabilityPreservers/SteinerCutFlow.lean)
  takes a nonnegative integer cutoff. For distinct terminals it returns a
  violating cut or certifies a flow of the requested value. A certified
  integral flow decomposes into simple unit routes within the original
  arc capacities.
  The [weighted network run](OnlineReachabilityPreservers/SteinerWeightedNetwork.lean)
  uses the separator on each request's own free attachments. It preserves
  earlier flow certificates and bounds rounded fractional cost against a
  fixed integral solution.
- [Search-work certificates](OnlineReachabilityPreservers/SearchWork.lean)
  count the arc inspections in reverse search, the candidate tests in
  a greedy walk, and separator calls in the weighted forest. The
  [offline](OnlineReachabilityPreservers/OfflineIndependence.lean) and
  [quota](OnlineReachabilityPreservers/KnownBudget.lean) certificates
  count the reachability and path-rule calls in pruning and budget
  certification. The [seed representation](OnlineReachabilityPreservers/SteinerSeedCoordinates.lean)
  identifies early samples with independent finite grid choices and
  bounds the number of coordinates. The [Steiner prefix counter](OnlineReachabilityPreservers/SteinerCompleteReplay.lean)
  and [preassigned path counter](OnlineReachabilityPreservers/AssignmentSearchWork.lean)
  compose polynomial bounds for the measured searches. The
  [bit budget](OnlineReachabilityPreservers/SteinerSamplingWork.lean) bounds
  the expected number of fair bits for independent seed coordinates.
- The [Steiner bit decoder](OnlineReachabilityPreservers/SteinerBitSeed.lean)
  reads the early grid choices, hub draws, and thin rounding choices from
  consecutive pieces of one finite bit list. It returns the unread suffix
  and the rejection count of each draw. The [raw-prefix proof and replay](OnlineReachabilityPreservers/SteinerBitReplay.lean)
  factor each fixed-count fair-bit event, prove that successful consumed
  inputs are prefix-free, and pass the decoded seeds to the verified weighted
  prefix evaluator. [Summing the raw events](OnlineReachabilityPreservers/SteinerBitLaw.lean)
  recovers the uniform seed law and the expected competitive bound on fixed
  feasible traces. The [graph-based replay](OnlineReachabilityPreservers/SteinerBitOrders.lean)
  constructs the finite index orders for the early coordinates, vertices,
  and arcs. Under the [product fair-bit law](OnlineReachabilityPreservers/SteinerBitMeasure.lean),
  a finite prefix suffices almost surely. Lean checks the uniform seed law,
  the expected edge count, and the polynomial bound on expected bits read at
  fixed height. The [fixed-budget implementation](OnlineReachabilityPreservers/SteinerBitBudget.lean)
  reads from a single polynomial-length uniformly random bit word. Its budget
  uses a graph-specific upper bound on the expected number of bits consumed.
  If decoding exhausts the word, the algorithm buys the input graph on the first
  non-self request. This preserves every feasible prefix and adds at most one
  edge in expectation, retaining the same competitive exponent. A replay theorem
  returns these same prefix graphs and bounds its measured searches and table
  operations. The cached replay shares one distance table and forest plan
  across budget calculation, decoding, and evaluation. The
  [bit cursor](OnlineReachabilityPreservers/SteinerBitCursor.lean) reads only
  the requested positions of its finite bit function. The
  [seed decoder](OnlineReachabilityPreservers/SteinerBitSeed.lean) preserves
  the decoded seed, rejection counts, and unread suffix. The replay accounts for
  preparation even on the fallback branch, which scans requests in one pass.
  The [arithmetic history index](OnlineReachabilityPreservers/SteinerBitOrders.lean)
  gives the same seed coordinate order by ranking bounded histories one label
  at a time. Vertex and arc ranks use binary search in their sorted arrays,
  with at most one key comparison per bit of the array length. Full time
  certification remains open. The [paired forest construction](OnlineReachabilityPreservers/SteinerTemplatePreparationWork.lean)
  generates the roots and bounded histories once for indexed vertices.
  From a supplied distance table it produces the exact duplicate-free arc
  list with polynomial source-level work for each fixed height.
  The [list-backed preparation and replay](OnlineReachabilityPreservers/SteinerFinReplayWork.lean)
  builds that hop table from the input arcs, reuses one vertex enumeration,
  and preserves every fixed-budget prefix graph and the decoder work.
  Its polynomial includes the explicit table and forest construction
  and the previously measured searches and table reads.
  The [weighted evaluator](OnlineReachabilityPreservers/SteinerFinWeightedReplayWork.lean)
  also charges the pass that prices the forest arcs and computes the scale
  and fuel. The checked prefixes and prior work tallies agree.
  The [indexed replay](OnlineReachabilityPreservers/SteinerFinIndexedReplayWork.lean)
  builds the canonical arc array once and uses arithmetic vertex and
  early-coordinate ranks on `Fin n`. Lean bounds the construction,
  proves a word-work bound for individual rank computations, and preserves
  all earlier replay records.
  The [streaming trace replay](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean)
  prepares the phase cutoffs and hub set once, reuses previous results
  for repeats and self requests, and charges the phase splits and fallback
  pass while preserving every earlier record.
  The same replay can count early seed reads while keeping its previous
  graphs and search and weight-read tallies. The bound charges one unit
  for each gate read and each ancestor sample read after an open gate.
  After successful decoding, the replay pairs each arc with its
  threshold using two indexed reads. The late phase reuses those
  rows across prefixes, and the earlier graphs and search tallies agree.
  The rank-aware replay also charges the arithmetic rank of each early
  seed read and sums this work through forest rounding and the prefixes.
  The [one-pass threshold builder](OnlineReachabilityPreservers/SteinerThinReplay.lean)
  accounts for cache construction in the same word model. Its tally is
  \(11m+4\) for \(m\) arcs, including the indexed reads and list assembly.
  The [incremental thin evaluator](OnlineReachabilityPreservers/SteinerThinReplay.lean#L800)
  keeps one load table throughout each nonempty thin run within an
  evaluated late prefix. It advances the table for each thin request and
  reuses the rounded graph from the final check when all checks pass.
  The graph and search tally agree with those of the earlier evaluator.
  On a feasible trace, the [complete replay](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L902)
  returns every ordinary fixed-budget prefix graph and includes polynomial
  allowances for the measured work of both phases at each fixed height.
  The [indexed thin separator](OnlineReachabilityPreservers/SeparatorWork.lean#L668)
  keeps one signed flow table per cut search and preserves the selected
  cut and search tally. Its [full replay bound](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L920)
  adds initialization and updates on both orientations of each augmenting
  arc. The [replay with stored capacities](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L966)
  also prepares each active capacity once per cut search and charges both
  indexed reads at every pair in the residual scans. The [residual route replay](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1011)
  uses those lists to find the same shortest routes and the final reachable
  source side, with the existing search tally preserved. On feasible
  traces the fixed-height bound includes the work of those list searches.
  The [replay with prepared intervals](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1073)
  shares one duplicate-free arc list across the trace. Each thin request
  in an evaluated thin run prepares its interval once and reuses it for
  the cut searches and updates. The fixed-height bound includes those
  interval computations. A separate [thin replay](OnlineReachabilityPreservers/SteinerThinReplay.lean#L1069)
  also charges each service test using the arc list retained by rounding.
  It returns the same graph and ordinary inspection count for every
  trace, and the [feasible-trace bound](OnlineReachabilityPreservers/SteinerThinReplay.lean#L1097)
  includes the additional list work. The late replay uses the arc list for
  arrival classification, both ordered hub-leg lists, and the test for
  a thick miss. Its fixed-height bound charges these scans and trace-list
  operations on feasible traces. The older graph and search records and
  the evaluation count agree for all inputs.
  [Replay with late classification work](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1154).
  The list-backed hub replay shares an explicit vertex list with both
  orientations of the hub routing. It charges their reachability searches,
  merging the hub arcs, the service query at each hit, and merging the
  resulting hub and thin graphs. On feasible traces it returns the same
  prefix graphs and evaluation count in both seed branches. It uses a
  measured late word count alongside the earlier early search charge, and
  includes the earlier arc-inspection count for the rounded thin service
  tests.
  [Replay with list-backed hub routing](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1506).
  The outer union now filters the late graph against the early arc set
  and appends the disjoint remainder. The count includes each membership
  scan and the append. The replay keeps the same graph and search records
  and evaluation count, and its fixed-height feasible-prefix bound includes
  the new union. The remaining thin service operations, container work,
  bit costs, and native execution costs remain open.
  [Replay with the outer union charged](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1525).
  The weighted network evaluator now has a separate implementation that
  takes a complete list of ordered pairs and stores accepted cuts in a
  list. It charges the scans for free and paid arcs, the charge reads,
  the rounded capacity arithmetic, and the paid outgoing cut. It returns
  the same charge values and ordered cuts as the earlier weighted run.
  [Weighted charge history](OnlineReachabilityPreservers/SteinerWeightedChargeWork.lean).
  The early forest evaluator builds the complete duplicate-free key list
  once from its roots, sides, histories, and network labels. It uses the
  measured weighted solver at each metric prefix. The scale, original
  setup tallies, and rounded graph agree with the earlier evaluator. The
  ordinary search tally is no larger, and a separate fixed-height budget
  bounds the new weighted solver and the seed reads.
  [Forest pair keys](OnlineReachabilityPreservers/SteinerForestPairKeysWork.lean#L284)
  · [Weighted early evaluator](OnlineReachabilityPreservers/SteinerFinWeightedReplayWork.lean#L286).
  The complete prefix replay uses this early evaluator alongside the
  list-backed late phase and the metered outer union. Every prefix graph
  and the evaluation count agree with the earlier replay. The combined
  recorded work has a fixed-height polynomial bound on feasible traces.
  [Replay comparison](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1635)
  · [Bounded full-prefix replay](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1667).
  A measured forest-rounding evaluator can consume those charge reads.
  It counts the forest membership scans, weights and charges read by
  ancestor tests, and the capacity arithmetic. It returns the same
  rounded forest as the earlier rounding and separately bounds the seed
  reads.
  [Charge magnitude after the weighted run](OnlineReachabilityPreservers/SteinerWeightedChargeWork.lean#L629)
  · [Rounding with measured charge reads](OnlineReachabilityPreservers/SteinerRoundingWork.lean#L1468).
  The standalone cutoff evaluator computes powers by doubling and clips
  a strictly rounded capacity with at most as many halvings as the tier
  number. Its word bound includes the supplied reads and cutoff arithmetic. It can
  reuse the powers across cutoffs in the same rounding tier.
  [Capped dyadic capacity](OnlineReachabilityPreservers/SteinerRoundingWork.lean#L112)
  · [Cutoff arithmetic](OnlineReachabilityPreservers/SteinerRoundingWork.lean#L203).
  A separate evaluator constructs the actual ancestor prefixes,
  scans them for each minimum, and builds the parent history. Given
  the two powers, its cutoff agrees with the reference and its word
  bound includes those operations.
  [Exact ancestor rows](OnlineReachabilityPreservers/SteinerRoundingWork.lean#L276)
  · [Cutoff with measured ancestors](OnlineReachabilityPreservers/SteinerRoundingWork.lean#L429).
  The forest trials use these stored-history computations in every
  tier that passes its gate. Each check shares its two powers across
  thresholds and charges the parent arcs used for capacity lookups.
  The threshold work and seed reads have separate bounds. The trials choose the same links as the prior evaluator.
  [Measured tier arithmetic](OnlineReachabilityPreservers/SteinerRoundingWork.lean#L1503).
  The complete replay uses this charge reader in the early rounding
  phase. Its prefix graphs and evaluation count agree with the earlier
  replay. The measured polynomial includes these reads and the capacity
  rounding.
  [Early rounding preparation](OnlineReachabilityPreservers/SteinerFinWeightedReplayWork.lean#L397)
  · [Complete replay with charge reads](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1737).
  Given a complete list of distinct forest vertices, a measured attachment
  builder scans the two leaf groups together and counts both unions with
  the free arcs. It returns the same weighted requests in the same order.
  [Metered forest requests](OnlineReachabilityPreservers/SteinerForestAttachmentsWork.lean#L210).
  The complete replay takes the forest rows from its existing key
  enumeration and uses them for all evaluated early metric prefixes.
  Its prefix graphs and evaluation counts agree with the history replay,
  and the feasible-prefix polynomial includes the attachment work.
  [Shared forest rows and keys](OnlineReachabilityPreservers/SteinerForestPairKeysWork.lean#L236)
  · [Complete replay with attachment work](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1806).
  The weighted separator and forest rounding also meter both terminal
  labels and the stored-distance lookup when they query a weight. The
  original weight values, prefix graphs, and evaluation count are exact.
  The feasible-prefix work bound includes these queries.
  [Measured weight query](OnlineReachabilityPreservers/SteinerForestLabelWork.lean#L73)
  · [Complete replay with measured metric reads](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1867).
  A separate routine expands bought forest links from supplied template
  rows and the original arc list. It meters the membership scans, both
  labels of each expanded link, the exact original route selection, and
  the arc unions. When the supplied rows contain the bought links it
  returns the full expanded graph.
  [Measured expansion](OnlineReachabilityPreservers/SteinerForestExpansionWork.lean#L192).
  The complete replay reuses the original arcs and forest template for
  all early prefix expansions and the final expansion when validation
  succeeds. The same checks produce the same fallback decision, graphs,
  and replay evaluation count. Its feasible-prefix work bound includes
  the expansion.
  [Early expansion and validation](OnlineReachabilityPreservers/SteinerEarlyReplay.lean#L629)
  · [Complete replay with measured expansion](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1928).
  The measured early validation scans the supplied arcs for the expanded
  graph, runs the reverse reachability search, and tests the source. The
  feasible-prefix work bound covers these steps on every nonempty early prefix
  check, preserving the same graph and evaluation count.
  [Measured demand check](OnlineReachabilityPreservers/SteinerIntervalWork.lean#L298)
  · [Complete replay with measured early validation](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L1989).
  Early assembly extends the reversed request history and recovers each
  nonempty prefix with its final request. It records the checks and merges
  the bought links once all checks pass. The graph and ordinary search tally
  agree with those from the prefix table, and the feasible trace bound now
  includes this assembly inside the complete replay.
  [Measured prefix assembly](OnlineReachabilityPreservers/SteinerEarlyReplay.lean#L802)
  · [Complete replay with measured prefix assembly](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2050).
  Every reached early metric now uses the measured gates, ancestor
  cutoffs, and parent-arc keys from the forest trials. This uses the same
  weighted separator run and preserves the prefix graphs and evaluation
  count on every trace. The feasible-prefix polynomial includes the new
  charges.
  [Prepared arithmetic](OnlineReachabilityPreservers/SteinerFinWeightedReplayWork.lean#L805)
  · [Complete replay with measured rounding](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2111).
  A standalone list-backed rounding evaluator builds the trial and tier
  indices once, scans the stored links, and keeps each selected link once.
  With the full forest link list, it returns the same graph and bounds
  the assembly and seed reads.
  [Measured trial and tier rows](OnlineReachabilityPreservers/SteinerRoundingWork.lean#L1750).
  The complete replay shares the same list with the expansion step.
  Its prefix graphs and evaluation counts agree on every trace, and the
  feasible-prefix bound includes trial and tier enumeration and forest
  link selection.
  [Complete replay with list-backed trials](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2172).
  A standalone weighted residual search uses the stored capacity rows and
  an explicit vertex count. It measures the flow reads from the retained
  augmenting paths, the residual row scans, the route searches, and the
  final source-side search. It returns the same cut decision and vertex set.
  [Measured weighted residual search](OnlineReachabilityPreservers/SteinerWeightedChargeWork.lean#L872).
  The weighted cover now has an evaluator that supplies the same vertex
  count to every residual search. Using the complete key list, it returns
  the reference charges and accepted cuts in order. The proof bounds the
  run and the cost and magnitude of each charge read.
  [Weighted cover with residual rows](OnlineReachabilityPreservers/SteinerWeightedChargeWork.lean#L1018).
  The complete replay counts the forest vertex rows once and supplies
  the exact weighted-network depth to each early metric. The same
  accepted cuts give the same charge values and lookup costs, and all
  prefix graphs and evaluation counts agree with the earlier replay.
  The feasible-prefix bound includes the depth setup and weighted
  residual searches. The trial-count calculation still enumerates the
  original vertices at each reached metric. This enumeration, later
  service steps, and bit and native costs remain outside the bound.
  [Complete replay with measured weighted search](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2233).
  The [late evaluator](OnlineReachabilityPreservers/SteinerHubRouteWork.lean#L528)
  also uses the measured thin service tests. The [complete replay](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2330)
  combines this with the measured weighted search and preserves every
  previous record and evaluation count. Its [feasible-prefix bound](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2389)
  includes the added service work. The [measured trial-count replay](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2421)
  computes the early metric's count once by halving the supplied original
  vertex count. It retains the same prefix records and adds only the
  trial-count setup tally, bounded by \(7n+12\). Other arithmetic and
  bit and native execution costs remain outside this bound.
  The [thin arithmetic replay](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2520)
  also measures the update cap and the shared part of the rounding
  factor once. Each late call adds its cutoff to that stored offset.
  The [feasible-prefix bound](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2578)
  includes this setup and per-call work and keeps all prefix records
  and evaluation counts.
  A [binary setup evaluator](OnlineReachabilityPreservers/SteinerThinBitArithmeticWork.lean#L64)
  computes the same two thin parameters from canonical binary input
  lists. Its recorded bit-list work is polynomial in the two input
  lengths. The [binary trial-count evaluator](OnlineReachabilityPreservers/SteinerEarlyBitArithmeticWork.lean#L68)
  computes the early trial count with a polynomial bit-list tally as well.
  The [binary initializer](OnlineReachabilityPreservers/SteinerThinBitInitializationWork.lean#L85)
  builds the actual zero load table from binary dimensions. Its bound counts
  the cells, the numeric payload width, and the input word lengths.
  The [binary indexed load access](OnlineReachabilityPreservers/SteinerBinaryIndexedWork.lean#L112)
  agrees with thin load table reads and replacements. Its bound is polynomial
  in the address word lengths and the number of supplied cells. The
  [fixed-width binary cut evaluator](OnlineReachabilityPreservers/SteinerThinBitLoadWork.lean#L207)
  also charges the payload increments and gives the same loads after a
  duplicate-free cut when the values fit. The [binary thin rounding comparison](OnlineReachabilityPreservers/SteinerThinBitRoundingWork.lean#L79)
  shifts the sampled threshold right and compares it with the factor. Its
  tally is polynomial in the supplied word lengths even for very large shift
  values. The [binary threshold scan](OnlineReachabilityPreservers/SteinerThinBitScanWork.lean#L144)
  combines these tests with exact encoded load reads. It returns the same
  rounded arc set as the word-work evaluator on duplicate-free encoded rows.
  The [binary-label reachability evaluator](OnlineReachabilityPreservers/SteinerBinaryReachWork.lean#L186)
  agrees with the list demand test given injective bounded-width labels.
  It charges comparisons bit by bit and preserves the order of visited
  vertex lists. The [binary trial evaluator](OnlineReachabilityPreservers/SteinerThinBitServiceWork.lean#L79)
  uses the passing labels directly and agrees with the existing thin replay's
  miss flag on valid encoded inputs. On a supplied sequence of distinct-arc
  cuts and queries, the [binary trace evaluator](OnlineReachabilityPreservers/SteinerThinBitCutTraceWork.lean#L164)
  starts from zero and agrees on every miss flag and the ending indexed loads.
  The terminal multiplicity bound keeps all earlier updates within the
  payload width. A [planned step bound](OnlineReachabilityPreservers/SteinerThinBitCapacityPlanWork.lean#L44)
  lets the evaluator reserve a sufficient width before examining the cut trace.
  Given the encoded original and residual arcs, [outgoing-cut extraction](OnlineReachabilityPreservers/SteinerBinaryResidualCutWork.lean#L138)
  finds the residual source side and returns its outgoing original arcs in order.
  The [binary flow cut](OnlineReachabilityPreservers/SteinerBinaryFlowCutWork.lean#L151)
  also produces the residual arcs from a complete supplied table of unsigned
  capacities and signed flow entries. The tally includes both the arithmetic
  and label comparisons. The [binary unit update](OnlineReachabilityPreservers/SteinerBinaryFlowAugmentWork.lean#L155)
  applies a supplied path to the signed table and keeps each capacity word.
  The [terminal cut comparison](OnlineReachabilityPreservers/SteinerCutFlow.lean#L567)
  lets a cut implementation choose any valid augmenting paths. A valid flow
  that attains the supply or stalls gives the same reference result.
  The [binary route search](OnlineReachabilityPreservers/SteinerBinaryPathWork.lean#L297)
  finds a shortest simple path in supplied encoded arcs up to a specified depth.
  It uses the supplied arc order to choose among shortest paths. From a
  complete supplied capacity table, the [binary separator](OnlineReachabilityPreservers/SteinerBinaryFlowRunWork.lean#L249)
  starts with zero flow, applies its own augmentations, and agrees with the
  reference separator on whether it finds a cut and on the cut's arc set.
  The tally is polynomial in the numeric supply, table size, and word widths.
  [Capacity clipping](OnlineReachabilityPreservers/SteinerClippedFlowCut.lean#L13)
  preserves the exact reference response when each nonnegative capacity is
  capped at the supply. The [binary clipped power](OnlineReachabilityPreservers/SteinerBinaryClippedPowerWork.lean#L89)
  evaluates a capped power of two within the supplied word widths.
  The [binary demand interval](OnlineReachabilityPreservers/SteinerBinaryIntervalWork.lean#L138)
  obtains the exact ordered interval arcs from the supplied encoded graph.
  The [binary capacity scan](OnlineReachabilityPreservers/SteinerBinaryThinCapacityWork.lean#L87)
  forms the clipped capacities from the encoded load table for supplied
  arc keys. The [binary thin cut](OnlineReachabilityPreservers/SteinerBinaryThinCutWork.lean#L141)
  computes the interval, capacities, and reference outgoing cut from the
  original encoded graph and current binary load cells. The [binary thin loop](OnlineReachabilityPreservers/SteinerBinaryThinLoopWork.lean#L148)
  prepares the interval once and carries out each load update on the same
  represented table for one feasible demand with supplied fuel. The [binary fractional cover](OnlineReachabilityPreservers/SteinerBinaryThinCoverWork.lean#L155)
  initializes the zero table at a sufficient width and carries its state
  across all arrivals. The total number of updates is bounded by the
  reference load potential. The [binary rounded demand step](OnlineReachabilityPreservers/SteinerBinaryThinDemandWork.lean#L77)
  finishes the fractional updates for one arrival before it scans the
  supplied threshold rows and tests reachability in the resulting graph.
  With the rows for a fixed sample, the [binary thin run](OnlineReachabilityPreservers/SteinerBinaryThinRoundRunWork.lean#L198)
  starts at zero and returns the exact thin graph. An empty list gives an
  empty graph, any missed prefix selects the original graph, and otherwise
  the last rounded graph is returned. The [indexed sample entry](OnlineReachabilityPreservers/SteinerBinaryThinSampleWork.lean#L197)
  constructs these rows using the decoder's shared arc index and its stored
  thresholds. The [finite-input entry](OnlineReachabilityPreservers/SteinerBinaryFinInputWork.lean#L174)
  encodes the graph and requests and generates all ordered pairs from the
  supplied vertex list. The [typed output](OnlineReachabilityPreservers/SteinerBinaryFinOutputWork.lean#L155)
  decodes the selected arcs and assembles the reference thin graph. Its
  work bound uses the length of the original arc list. The [late evaluator](OnlineReachabilityPreservers/SteinerBinaryLateWork.lean#L27)
  combines that graph with the existing hub routes and preserves the thick
  full-graph fallback. Its bound adds the hub word work and the binary thin
  work. The [prepared late controls](OnlineReachabilityPreservers/SteinerBinaryLateControlsWork.lean#L88)
  compute the count words, rounding factor, and fuel for that evaluator.
  The [seeded replay with binary late rounds](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2796)
  runs that evaluator with the decoded thin sample at each prefix and
  keeps the measured early evaluator. It proves the exact reference graph
  at every feasible prefix, including the budget-exhaustion fallback.
  Its [whole-run tally](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2808)
  includes preparation, seed decoding, indexing, and the mixed work
  at every replayed prefix. A native execution bound remains open.
  In the early weighted cover, the [binary charge update](OnlineReachabilityPreservers/SteinerBinaryWeightedLoadWork.lean#L44)
  maintains the remainder, doubling factor, and exact weighted numerator
  for one paid edge, with a bound in the input word widths. The [binary weighted capacity](OnlineReachabilityPreservers/SteinerBinaryWeightedCapacityWork.lean#L129)
  rounds that numerator by the cost and caps the capacity at the supplied
  flow amount. The [weighted separator](OnlineReachabilityPreservers/SteinerBinaryWeightedCutWork.lean#L155)
  builds the capacities from the current pair states and request-local free
  arcs. It returns the same optional paid cut as the reference. The [table update](OnlineReachabilityPreservers/SteinerBinaryWeightedUpdateWork.lean#L138)
  advances the states selected by a supplied cut and preserves the ordered
  keys and labels. The [weighted loop](OnlineReachabilityPreservers/SteinerBinaryWeightedLoopWork.lean#L62)
  generates and applies those cuts successively for one demand. It returns
  the represented reference charges and the same chronological cuts.
  The [weighted trace](OnlineReachabilityPreservers/SteinerBinaryWeightedTraceWork.lean#L78)
  carries the updated table through every demand with its own free arcs.
  It returns the full reference cut history and final paid charges.
  The [binary initializer](OnlineReachabilityPreservers/SteinerBinaryWeightedInitWork.lean#L44)
  uses the supplied key and cost readers to build zero-charge rows. It
  derives the [reference scale and fuel](OnlineReachabilityPreservers/SteinerBinaryWeightedInitWork.lean#L170)
  from the total paid cost. The [weighted run from zero](OnlineReachabilityPreservers/SteinerBinaryWeightedRunWork.lean#L97)
  combines these steps and encodes typed requests with their own free arcs.
  Its work bound includes preparation and the full chronological cover.
  The [metric forest labels](OnlineReachabilityPreservers/SteinerBinaryForestLabelsWork.lean#L64)
  distinguish every network vertex and supply the exact network size.
  The rank uses the network tag, original root, side, and bounded history.
  The [binary fractional forest run](OnlineReachabilityPreservers/SteinerBinaryForestFractionalWork.lean#L154)
  builds the pair keys and each request's leaf attachments. With the
  prepared paid and free forest classes and the exact hop reader, it
  returns the reference fractional state and chronological cuts.
  The [weighted capacity reader](OnlineReachabilityPreservers/SteinerBinaryWeightedUnitsWork.lean#L87)
  searches those binary labels and returns the exact clipped capacity.
  The [ancestor cutoff lemma](OnlineReachabilityPreservers/SteinerBinaryWeightedUnitsWork.lean#L130)
  proves that clipping above a tier's cap preserves its rounding tests.
  The [forest rounding evaluator](OnlineReachabilityPreservers/SteinerBinaryForestRoundingWork.lean#L101)
  reads the supplied binary paid states and zero-cost forest arcs.
  With fixed trial samples it returns the reference rounded forest and
  counts the row work and seed reads separately.
  The [combined forest run](OnlineReachabilityPreservers/SteinerBinaryForestRunWork.lean#L46)
  feeds the final rows of the binary fractional trace into this evaluator.
  It gives the exact reference rounded forest and bounds both recorded
  tallies for the supplied typed forest data, hop reader, and trial samples.
  A [single weighted plan pass](OnlineReachabilityPreservers/SteinerWeightedPlanWork.lean#L116)
  keeps the original plan and the typed zero-cost rows. The
  [prepared early evaluator](OnlineReachabilityPreservers/SteinerFinWeightedReplayWork.lean#L1179)
  uses those rows, the finite hop table, and the measured trial count for
  binary forest calls. It returns the reference early prefix graph for the
  supplied trials, including the full-graph fallback on validation failure.
  The [seeded replay with both binary solvers](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2935)
  uses the same decoded sample for the early and late phases. On feasible
  traces it returns the reference fixed-budget graph at each prefix and
  preserves the number of evaluated prefixes, including on seed exhaustion.
  The [combined work theorem](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L3087)
  bounds every recorded field of this replay. It includes the shared
  preparation, seed decoding, prefix dispatch, and both solver phases
  in the mixed word and binary-list model.
  The [input-size bound](OnlineReachabilityPreservers/SteinerBinaryReplaySizeWork.lean#L26)
  depends only on the vertex and arc counts, raw arc list length, forest
  height, and demand count. The same theorem checks the reference graph
  at every feasible prefix and the exact evaluation count.
  At fixed forest height a [single polynomial](OnlineReachabilityPreservers/SteinerBinaryReplayAsymptotics.lean#L171)
  bounds the sum of the recorded work and the prescribed number of fair bits.
  The [executable competitive bound](OnlineReachabilityPreservers/SteinerBinaryReplayCompetitive.lean#L56)
  applies Theorem 21 to the final graph returned by this replay. Uniform
  fixed-length seeds give the claimed expected edge bound on every fixed
  feasible trace, against any offline subgraph that serves it.
  The [metered final result](OnlineReachabilityPreservers/SteinerBinaryReplayResultWork.lean#L68)
  also charges for counting the input arcs and scanning the retained
  records to return the final graph. Its recorded work and fair-bit supply
  obey a [fixed-height polynomial](OnlineReachabilityPreservers/SteinerBinaryReplayAsymptotics.lean#L194).
  The [arrival interface](OnlineReachabilityPreservers/SteinerBinaryArrivals.lean#L39)
  sees only the new request and its stored history, and reuses the same bit
  word for every prefix solve. Its [exact total](OnlineReachabilityPreservers/SteinerBinaryArrivals.lean#L92)
  charges every replay and the history reversal at each arrival.
  One [Theorem 21 statement](OnlineReachabilityPreservers/SteinerBinaryArrivals.lean#L188)
  gives feasibility, irrevocability, polynomial recorded work including the
  bit supply, and the expected edge bound on a fixed feasible trace.
  The [sampled arrival theorem](OnlineReachabilityPreservers/SteinerBinaryArrivals.lean#L329)
  starts from a stream of independent fair bits. It computes the exact bit
  budget from the input graph, draws that many bits into one array before
  any demand, and reuses the array throughout the run. Its fixed-height
  recorded work includes those initialization steps. The competitive
  expectation holds against any offline subgraph serving the fixed trace.
  The [raw arc-list entry point](OnlineReachabilityPreservers/SteinerRawArcRows.lean)
  constructs the graph before sampling, even when an arc occurs more than
  once. Its polynomial recorded-work bound includes that construction.
  The ingestion tally counts equality of finite vertex labels as a primitive.
- [The acyclic cleaning construction](OnlineReachabilityPreservers/BalancedRegularization.lean)
  retains at least a sixteenth of the incidence mass within the original vertex
  and path budgets. In the dense regime it proves the lower and upper caps
  from Lemmas 23 and 39 and preserves both bridge exclusions at every size.
  The [extremal conclusion](OnlineReachabilityPreservers/CommonOrderExtremal.lean)
  applies this at any positive vertex and path budgets in a common vertex order.
  For each bridge cutoff up to size three, the [locally ordered extremum](OnlineReachabilityPreservers/LocalOrderExtremal.lean)
  gives the same caps and mass guarantee at the corresponding maximum over all simple lists.
- At every half cutoff through five and full cutoff through six, a
  witness at the unrestricted indexed maximum retains at least \(M/392\),
  fits both budgets, and satisfies all four factor-four caps around its
  own averages. For cutoffs of at least two in the same ranges, the
  feasible literal maximum over distinct nonempty paths has a literal
  witness of mass at least \(M/7056\) with the same budgets and caps.
  [Indexed and literal output-average cleaning](OnlineReachabilityPreservers/OutputAverageShortCleaning.lean).
- At a full cutoff covering the smaller budget, the unrestricted indexed
  maximum has a witness that excludes full bridges at every size, retains
  at least \(M/523\), and meets both original budgets and all four
  output-average caps. For simple input excluding full bridges through a
  cutoff of at least three, with mass at least both positive budgets, the
  same conclusion at that cutoff holds when every input precedence
  component excludes full bridges at every size.
  [Output-average cleaning of full components](OnlineReachabilityPreservers/IncreasingFullAverageCleaning.lean).
- In the literal model, the same full-component condition gives a
  distinct nonempty witness retaining at least \(M/9414\), with both
  budgets and all four output-average caps. A full cutoff covering the
  smaller budget gives an all-size witness at the feasible literal
  maximum.
  [Literal output-average cleaning at full cutoffs](OnlineReachabilityPreservers/OutputAverageDistinctCleaning.lean).
- If paths longer than the original upper length cap carry at least two
  thirds of the incidence mass (M), pruning that subfamily and trimming
  its vertex blocks retain at least (M/216). The witness meets both
  original budgets and all four frozen caps through half cutoff four or
  full cutoff six. [Cleaning the overlong subfamily](OnlineReachabilityPreservers/FrozenOverlongPaths.lean#L191).
- If such rows carry at most seven fifteenths of the mass, keeping the
  length-capped subfamily yields the original budgets and frozen caps
  with mass at least (M/104). The theorem preserves full exclusion at
  any cutoff and half exclusion through size four.
  [Cleaning the length-capped subfamily](OnlineReachabilityPreservers/FrozenLengthCappedPaths.lean#L154).
- The same bound holds if clipping every row at the cap deletes at most
  (7M/15) incidences. Combining clipping with the sharper charge for
  overlong rows yields a witness of mass at least (M/2000) when those rows
  carry at least (7M/12), through half cutoff four or full cutoff six.
  [Clipping and the overlong case](OnlineReachabilityPreservers/FrozenLengthCappedPaths.lean#L232).
- At half cutoff five, [the two width splits](OnlineReachabilityPreservers/HalfFiveProjection.lean)
  preserve exclusion when each pair of paths shares at most one vertex. The
  resulting cleaning witness retains at least \(M/16\). For arbitrary
  intersections, [the degree repair](OnlineReachabilityPreservers/HalfFiveCleaning.lean)
  gives \(M/5000\) when the total path-length excess above
  \(\lfloor4M/p\rfloor\) is at most \(7M/50\). Both conclusions require
  positive budgets and input mass \(M\) at least both budgets. Both witnesses
  keep the original budgets and all four original-average caps.
- Two more half-five cases use only the overlong paths. At least \(2M/3\)
  incidences on those paths give a witness of mass at least \(M/216\).
  At least \(7M/12\) suffices for retention \(M/2000\) when the total
  length excess is at least \(7M/15\).
  [Pruning and peeling the overlong paths](OnlineReachabilityPreservers/FrozenOverlongPaths.lean#L274).
- Half-five cleaning also keeps at least \(M/288\) if opposite-intersection
  pruning retains at least \(13M/24\). This holds when at least \(M/12\) paths
  are nonempty or there are at most \(11M/24\) opposite-neighbor links.
  [Pruning and trimming both supports](OnlineReachabilityPreservers/FrozenMatchedPartners.lean#L650).
- At the original path width, let \(E\) count distinct piece incidences
  where one comparison crosses its parent's cut and the reverse comparison
  lies within a piece of the other parent. Let \(U\) count the original
  degree excess above \(\lfloor4M/n\rfloor\).
  [Repairing the path cuts](OnlineReachabilityPreservers/HalfFivePathCleaning.lean)
  keeps \(M/5000\) at half cutoff five when \(20E\le3M\) or
  \(100U+50E\le43M\). The witness fits both original budgets and
  meets all four original-average caps.
- [One color deletion repairs both width splits](OnlineReachabilityPreservers/HalfFiveSharedWidthCleaning.lean)
  at half cutoff five. Take the union of the path-cut incidences and the
  incidences at vertices above the original degree width. If that union
  contains at most \(4M/5\) incidences, the witness keeps at least
  \(M/5000\) and satisfies both budgets and all four original caps.
  [Trimming the row pieces by their combined weight](OnlineReachabilityPreservers/HalfFiveWeightedWidthCleaning.lean)
  gives the same guarantees for a union of size at most \(22M/25\).
- If vertices above the original degree width carry at least 71 percent
  of the input mass, [counting their actual copies](OnlineReachabilityPreservers/HalfFiveHeavyWidthCleaning.lean)
  gives the same half-five guarantees without a bound on the number of
  path-cut conflicts.
- [Counting only reversed comparisons across actual degree cuts](OnlineReachabilityPreservers/HalfFiveDegreeCutCleaning.lean)
  gives another half-five criterion. After clipping rows to the original
  length width, let \(K\) be their mass and \(A\) the number of participating
  copied incidences. If \(A+2(M-K)\le23M/25\), the witness retains
  \(M/5000\) within both original budgets and all four original caps.
- [Repairing both actual cuts in degree-first order](OnlineReachabilityPreservers/HalfFiveDegreeFirstCleaning.lean)
  also gives \(M/5000\), both original budgets, and all four original
  caps at half cutoff five. The union of the crossed degree comparisons
  and the crossed path comparisons on copied vertices must mark at most
  81 percent of the incidences.
- The same actual cut relations admit [any cover of at most 37 percent
  of the original incidences](OnlineReachabilityPreservers/HalfFiveDegreeFirstCleaning.lean)
  as a deletion set. This gives the same half-five mass, budgets, and caps.
  Each incidence has at most one later target among the two cut relations.
  [A matching of equal size](OnlineReachabilityPreservers/CutConflictMatching.lean)
  characterizes the smallest cover. The same guarantee follows if every
  set of pairwise disjoint cut conflicts has at most 37 percent of the
  original incidence count as edges.
- [Cleaning inside selected degree copies and path pieces](OnlineReachabilityPreservers/DegreeFirstRectangleCleaning.lean)
  counts only matching edges whose two endpoints are retained in that
  rectangle. If its raw incidence count covers the largest such matching,
  the peeling costs of the selected supports, and \(M/5000\), the witness
  meets both budgets and all four original-average caps at half cutoff
  five.
- [Counting only supported reverse comparisons](OnlineReachabilityPreservers/DegreeFirstSupportedCleaning.lean)
  further restricts that matching to conflicts for which the other
  corner occurs in both rows inside the chosen rectangle. The same
  peeling inequality gives the same original-average guarantee.
- If either positive budget is at most 29, an unrestricted maximum at any
  cutoff of at least two has a witness with both budgets, all four frozen
  caps, and at least \(M/8\) incidences. The witness excludes full bridges
  through the input cutoff in either bridge mode.
  [Counting all ordered pairs](OnlineReachabilityPreservers/FrozenSmallBudgets.lean).
- If \(\binom p3\le56n\), counting triples of path labels gives the
  same \(M/8\) witness for any cutoff of at least two. If \(q\) paths
  exceed the original upper length cap and \(5\binom q3\le16n\), a
  separate argument gives an \(M/104\) witness at any full cutoff of
  at least two or half cutoffs two through four.
  [Cleaning by counting triples](OnlineReachabilityPreservers/FrozenPathTriples.lean).
- A [length-capped subfamily using at most half the path budget](OnlineReachabilityPreservers/FrozenLengthCappedPaths.lean#L124)
  needs only two fifths of the original mass before trimming and peeling.
  When a shared vertex partition of the overlong paths fits in that half
  budget, an ordered-pair bound controls clipping. The
  [overlong partition theorem](OnlineReachabilityPreservers/FrozenOverlongPartitions.lean#L48)
  gives both original budgets, all four frozen caps and at least
  \(M/104\), at every full cutoff and half cutoffs through four.
- For full-bridge cutoffs three through five, a cleaned maximizing family
  retains at least \(M/119\) and meets both budgets and all four factor-four
  caps measured against the original averages. The path split places matching
  cuts between opposite intersections. [Frozen-average cleaning](OnlineReachabilityPreservers/LocalFrozenCleaning.lean).
- For simple paths, mass \(M\) at least both positive budgets and at least
  \(8E\), where \(E\) counts opposite-neighbor links, suffices for both
  budgets, all four original-average caps, and retention of \(M/32\) at
  full cutoff six or half cutoff four. Each case uses its own bridge
  exclusion on the input and output.
  [Frozen size-six cleaning](OnlineReachabilityPreservers/ContiguousSixCleaning.lean#L136)
  · [Frozen half-four cleaning](OnlineReachabilityPreservers/ContiguousHalfCleaning.lean#L340).
- Full bridge exclusion at every size bounds the loss under pruning to
  unique intersections by \(n-1\) for \(n>0\). Combining this bound with
  explicit low-mass witnesses gives the same frozen size-six conclusion
  for every simple all-size full-bridge-free input of mass at least both
  positive budgets.
  [Pruning bound](OnlineReachabilityPreservers/OppositeLinkForest.lean#L528)
  · [All-size input](OnlineReachabilityPreservers/ContiguousSixCleaning.lean#L151).
  The [common-order cleaning](OnlineReachabilityPreservers/FullBridgeCleaning.lean#L37)
  preserves exclusion of every full bridge for inputs with that property.
  With positive budgets and mass at least both, it keeps at least \(M/32\),
  both budgets, and all four original-average caps when \(M\le 8\max(n,p)\)
  or \(24n\le M\).
  A [two-incidence deletion bound](OnlineReachabilityPreservers/OfflineBridgeConverse.lean#L209)
  and trimming at ratios that account for the retained mass give the
  [all-mass result](OnlineReachabilityPreservers/FullBridgeCleaning.lean#L271).
  It keeps at least \(M/40\), both original budgets, the four original-average
  caps, and exclusion of every full bridge when the input has that exclusion.
  At a finite full-bridge cutoff \(k\), the
  [component criterion](OnlineReachabilityPreservers/FullBridgeCleaning.lean#L203)
  keeps the same budgets, caps and \(M/40\) guarantee when every precedence
  component has at most \(k\) rows with a strict internal step. Longer
  bridges can exist in the original system.
  The [mixed support criterion](OnlineReachabilityPreservers/FullBridgeComponentSupports.lean#L96)
  also allows a component with at most \(k\) vertices shared by two
  distinct internal rows with strict steps. Each component can use
  whichever bound applies.
  After [small rowwise deletions](OnlineReachabilityPreservers/FullBridgeCleaning.lean#L250), the component test can use
  just the surviving precedence graph. Losing at most \(M/28\) and having
  at most \(k\) nontrivial rows per surviving component gives \(M/128\)
  with the original budgets and all four original-average caps.
  The [visit-excess test](OnlineReachabilityPreservers/FullBridgeComponentSupports.lean#L269) applies when some original
  components exceed both support bounds. Keep the first incidence of each
  nonempty row visit to a marked component and the full visits elsewhere.
  If the excess
  over one per marked visit is at most \(M/28\), the same \(M/128\)
  finite-cutoff guarantee holds with the original budgets and caps.
- In half-bridge-free systems through size three, there are no triangles
  of opposite links. If two opposite links connect distinct vertices on
  one path, the intermediate vertex belongs to that path. Half-bridge exclusion
  through size four also rules out four-cycles of opposite links. These
  restrictions apply to cyclic inputs.
  [Two-link property](OnlineReachabilityPreservers/OppositeLinkForest.lean#L620)
  · [Cycle length bound](OnlineReachabilityPreservers/OppositeLinkForest.lean#L846).
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
  For half exclusion through four, the number of opposite links \(E\)
  satisfies \(4E^2\le n^2(n-1)\). If \(M^2\ge16n^2(n-1)\) and the
  incidence mass \(M\) is at least both positive budgets, the cleaned
  family meets all four original-average caps within both budgets and
  retains at least \(M/32\). This holds at the unrestricted half-four
  maximum when \(p^2\ge16n^2(n-1)\).
  [Link count](OnlineReachabilityPreservers/OppositeLinkForest.lean#L877)
  · [Cleaning at large path budgets](OnlineReachabilityPreservers/ContiguousHalfCleaning.lean#L393).
  Taking both orientations of each edge as two-vertex paths realizes
  every graph of girth greater than four as an opposite-link graph of
  a half-four-free family. The paths have four incidences per graph edge.
  [Dart construction](OnlineReachabilityPreservers/OppositeLinkForest.lean#L1041).
  Point and line incidence over a finite prime field gives such systems
  with more opposite links than any fixed multiple of the vertex count.
  [Finite field construction](OnlineReachabilityPreservers/OppositeLinkDensity.lean#L120).
  It suffices to count the opposite links inside a later nested reversal.
  Deleting their starting incidences removes every such reversal. For
  simple half-four-free paths with mass \(M\) at least both positive
  budgets, a subset of at most \(M/8\) nested links gives a cleaned family
  with at least \(M/32\), both budgets, and all four original-average caps.
  [Cleaning with few nested links](OnlineReachabilityPreservers/NestedOppositeCleaning.lean#L147).
  The [post-split repair](OnlineReachabilityPreservers/ContiguousHalfCleaning.lean#L443)
  marks the starting incidence of each inner step in a nested reversal
  that survives the width cuts. [Trimming full blocks first](OnlineReachabilityPreservers/FrozenBlockTrimming.lean#L153)
  gives both original budgets, all four caps, and retention at least \(M/12\)
  if at most \(M/4\) incidences are marked.
  The [marked count](OnlineReachabilityPreservers/ActiveNestedCutCounting.lean#L58)
  is at most the sum of the lengths minus one, truncated at zero, over
  the non-first blocks. The [same cleaning guarantee](OnlineReachabilityPreservers/FrozenBlockTrimming.lean#L177)
  follows when this sum is at most \(M/4\).
  A [73-incidence example](OnlineReachabilityPreservers/AverageSplitAudit.lean#L430)
  marks at least 19 starts at the prescribed widths. The same family
  [has a clean witness](OnlineReachabilityPreservers/AverageSplitAudit.lean#L447)
  from the low-mass construction.
- A [common vertex partition with clipping](OnlineReachabilityPreservers/ClippedVertexPartitions.lean#L127)
  bounds the loss by the number of ordered vertex pairs on the selected
  paths divided by \(q(4L-2)\), where \(q\) is the number of parts and
  \(L\) is the path cap. Every bridge stays within one part. With room
  for all path pieces and enough mass after clipping, the
  [frozen cleaning theorem](OnlineReachabilityPreservers/ClippedVertexPartitions.lean#L199)
  attains both budgets and all four caps with at least \(M/16\).
- A color may depend on both the path and the vertex of an incidence.
  Giving each row piece and vertex copy its color
  [preserves both bridge exclusions](OnlineReachabilityPreservers/IncidenceColorCleaning.lean#L45)
  at every cutoff. If the colored pieces meet the upper caps and their
  occupied supports fit within four thirds of each original budget,
  [the frozen witness](OnlineReachabilityPreservers/IncidenceColorCleaning.lean#L213)
  fits both budgets, meets all four caps and retains at least \(M/16\).
  A [64-vertex example](OnlineReachabilityPreservers/IncidenceColorBudgetAudit.lean#L249)
  excludes full bridges through size two and admits no coloring of all its
  incidences meeting these support bounds and the original upper length cap.
  A [separate frozen witness](OnlineReachabilityPreservers/IncidenceColorBudgetAudit.lean#L261)
  meets both original budgets and all four caps for the same example.
  A [two-layer family](OnlineReachabilityPreservers/LayeredIncidenceColorAudit.lean#L91)
  on 128 vertices respects one vertex order and excludes half-bridges
  at every cutoff. It also
  [obstructs the coloring criterion](OnlineReachabilityPreservers/LayeredIncidenceColorAudit.lean#L274)
  at its original upper length cap. A different family supplies the
  [frozen witness](OnlineReachabilityPreservers/LayeredIncidenceColorAudit.lean#L287)
  for its original counts and mass.
- Given half exclusion through size three, [vertex copies for reversed intersections](OnlineReachabilityPreservers/ReverseIntersectionCopies.lean#L123)
  retain every incidence and make intersections unique. They preserve
  full exclusion at every cutoff and half exclusion through size four.
  When at most one sixteenth of the vertices have an outgoing reverse
  partner, [frozen cleaning](OnlineReachabilityPreservers/ReverseIntersectionCopies.lean#L299)
  keeps the input's exclusion at cutoff four in either mode or at full
  cutoff six. It retains at least \(M/16\) within both original budgets and
  all four caps for positive budgets and mass at least both counts. A broader
  [support condition](OnlineReachabilityPreservers/ReverseIntersectionCopies.lean#L233)
  uses the actual number of occupied vertex copies.
- [Quadratic trimming](OnlineReachabilityPreservers/FrozenQuadraticTrimming.lean#L225)
  works on a subsystem within the original budgets that carries at least
  nine sixteenths of the original mass and whose original-width splits
  preserve the chosen bridge exclusion. It keeps every nonfinal block
  and trims among the final blocks in each dimension. It retains at least
  \(M/104\) with both budgets and all four caps. Selecting the heaviest vertex
  copies before splitting gives this guarantee when at most
  [seven ninths of the vertices have outgoing reverse partners](OnlineReachabilityPreservers/FrozenQuadraticTrimming.lean#L353).
  This version preserves the matching input exclusion at cutoff four in
  either mode or at full cutoff six.
- [Cleaning with disjoint reverse partners](OnlineReachabilityPreservers/FrozenMatchedPartners.lean#L192)
  covers simple paths whose reversed comparisons are confined to disjoint
  pairs of paths. For positive budgets and mass at least both counts,
  the witness retains at least \(M/104\) within both original budgets and
  all four original-average caps, with the same exclusion at cutoff four
  in either mode or at full cutoff six. The proof selects the heavier
  path of each pair and, when needed, uses the
  [width splits with half the path budget](OnlineReachabilityPreservers/FrozenMatchedPartners.lean#L97).
  The [two-class theorem](OnlineReachabilityPreservers/FrozenMatchedPartners.lean#L308)
  gives the same guarantee whenever the paths can be partitioned into
  two classes and every reversed comparison crosses between classes.
- At the same cutoffs, a repaired two-class partition may delete up to
  \(M/24\) incidences. Alternatively, one subfamily with unique intersections
  suffices if rowwise shortening retains at least \(13M/24\). Each condition
  gives a witness with at least \(M/288\), both original budgets and all four
  original-average caps. Opposite-intersection pruning meets the second
  condition when there are at most \(11M/24\) opposite links.
  [Repair and pruning theorems](OnlineReachabilityPreservers/FrozenMatchedPartners.lean#L514).
- At these cutoffs, the [large path-budget theorem](OnlineReachabilityPreservers/FrozenManyRows.lean#L39)
  starts from the unrestricted maximum when \(n(n-1)\le66p\).
  Such a maximizing family has nonempty rows and average length at most
  twelve. Opposite-intersection pruning then gives a cleaned witness with
  \(M/288\), both budgets, and all four original-average caps.
- For positive budgets, the [clipping theorem](OnlineReachabilityPreservers/FrozenClippingBudgets.lean)
  gives both original budgets, all four caps and at least \(M/104\) of the
  unrestricted maximum when \(p\le227\) or \(n(n-1)\le235p\). It applies at
  every full cutoff of at least two and at half cutoffs two through four.
  The ordered-pair budget bounds the mass deleted by clipping, so this
  proof only needs to split vertices.
- For positive budgets with either \(n\le157\) or \(p\le156\), [clipping both dimensions](OnlineReachabilityPreservers/FrozenDegreeClipping.lean)
  gives a cleaned witness of mass at least \(M/104\) with both original
  budgets and all four original-average caps at
  every full or half cutoff of at least two. In the dense branch at
  cutoff three or higher, both length and degree clipping use rowwise
  deletions, which preserve the original arrival order.
- With positive budgets, [a squared-mass bound](OnlineReachabilityPreservers/FrozenUnbalancedBudgets.lean)
  gives a witness excluding full bridges at every size and keeping at
  least \(M/8\) of the unrestricted maximum, both original budgets, and
  all four original-average caps. This holds in both modes when
  \(n(n-1)\le28p\) and the input cutoff is at least two, or when
  \(p(p-1)\le40n\) and the input cutoff is at least three.
- In half mode at input cutoff at least three, [degree-three grids](OnlineReachabilityPreservers/HalfGridCleaning.lean)
  extend the \(M/8\) guarantee to positive budgets with \(p\le n\)
  and \(p(p-1)\le108n\). A single witness meets both original budgets
  and all four original-average caps and excludes every half-bridge.
  Horizontal paths arrive before the two directions of each column.
- The [grid in arbitrary dimension](OnlineReachabilityPreservers/AxisGridCleaning.lean)
  has \(d+1\) paths through each vertex in \(d\) dimensions. For
  positive budgets and mass \(M\ge\max(2n,p)\), it gives an \(M/8\)
  witness with both budgets and all four original caps when a block
  of the prescribed width and dimension fits. One witness excludes
  half-bridges of every size. The statement map gives the two
  explicit budget inequalities.
- The [finite-budget cases](OnlineReachabilityPreservers/FrozenBoundaryCases.lean)
  package the original caps at the unrestricted maximum through cutoff
  three in either mode, with a witness of mass at least \(M/16\).
  A full cutoff of at least \(\min(n,p)\) covers every bridge size and
  gives the all-size witness of mass at least \(M/40\) for positive
  budgets. An empty budget or cutoff below two admits the full \(np\)
  incidence mass in the indexed convention.
- [Half-four cleaning](OnlineReachabilityPreservers/FrozenHalfFourCleaning.lean)
  proves the original-average conclusion of Lemma 23 at cutoff four for
  arbitrary indexed simple paths. With positive budgets and mass \(M\)
  at least both budgets, the witness retains at least \(M/5000\) and at
  most \(M\), fits both original budgets, and meets all four original caps.
  It applies at the unrestricted maximum. The proof handles the
  conflicts left by contiguous path cuts before splitting vertices.
- [Full-six cleaning](OnlineReachabilityPreservers/FrozenFullSixCleaning.lean)
  gives both original budgets, all four caps, and retention at least
  \(M/5000\) at the unrestricted full cutoff-six maximum. The proof handles
  reversed comparisons across contiguous pieces using an independent set
  of incidences. Each incidence has at most one incoming and one outgoing
  conflict, and an independent set may have to omit two vertices of a triangle.
- A contiguous split preserves full exclusion through size seven
  when opposite steps stay on one piece and no two-step return through
  distinct other parents crosses two pieces against their common
  parent's order. The existing seven-vertex example passes the first
  test and has the two-step return \(3\to4\to0\) across its split.
  [Seven-bridge lift](OnlineReachabilityPreservers/CyclicSplits.lean#L383) · [Preservation through seven](OnlineReachabilityPreservers/CyclicSplits.lean#L506) · [Two-step return in the example](OnlineReachabilityPreservers/UniqueSplitAudit.lean#L140).
- The same two conditions also preserve full exclusion through seven
  for disjoint pieces that interleave. For simple full-seven-free rows
  of mass \(M\) at least both positive budgets, test for returns of at
  most two edges on the actual pieces after the standard degree and
  path splits. If the test passes, the frozen witness retains at least
  \(M/16\) with both original budgets and all four caps.
  [Lift allowing interleaved pieces](OnlineReachabilityPreservers/CyclicSplits.lean#L570) · [Two-step width test](OnlineReachabilityPreservers/FullSevenWidthCleaning.lean#L39) · [Full-seven frozen witness](OnlineReachabilityPreservers/FullSevenWidthCleaning.lean#L66).
- The [literal set versions](OnlineReachabilityPreservers/FrozenDistinctCleaning.lean)
  give distinct nonempty output paths with the same caps. They apply to
  the literal exact-count maximum when the positive original budgets are feasible.
  The retention factors are \(5000\) at half cutoff four and full cutoff
  six, and \(119\) at full cutoffs three through five. The all-size full family theorem gives
  the distinct output guarantee with factor \(40\).
- If each simple path visits at most one original mean path length of
  vertices inside any one precedence component, component cuts preserve
  full-bridge exclusion at the given cutoff. They also preserve exclusion
  of every full bridge when the input has that property. For positive
  budgets and mass at least both budgets, the cleaned family meets both
  budgets and all four original-average caps and retains at least \(M/16\).
  The half-bridge result holds with the same guarantees when the degree
  split is safe at the given cutoff.
  [Component cuts and fixed-average cleaning](OnlineReachabilityPreservers/ComponentSplitCleaning.lean).
  The visit limit can also be the full upper length cap, four times the
  original mean. The resulting family meets the same budgets and caps
  and retains at least \(M/54\). This version uses the combined length
  of adjacent pieces to control their count.
  [Component visits within the length cap](OnlineReachabilityPreservers/ComponentSplitCleaning.lean).
  If visits above that cap contain at most \(M/56\) incidences, remove
  those whole visits first. The construction then retains at least
  \(M/108\), with both budgets, all four original caps, and the same
  bridge guarantees.
  [Cleaning with a small mass of long visits](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1125).
- At cutoff \(k\), the factor-four blocks retain at least \(M/16\) in either
  bridge mode when the precedence graph has no directed cycle of length at
  most \(k-2\). If removing at most \(M/18\) incidences from the rows suffices
  to obtain this property, the construction retains at least \(M/32\).
  Both guarantees use the two positive original budgets and all four caps
  computed from the original averages, for mass at least both budgets.
  [No short cycles](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1596)
  · [After deletions](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1644).
  The same bounds follow by ruling out short returns only across the
  actual width cuts. Full mode uses this condition alone. Half mode also
  uses one of the sufficient conditions for splitting vertices.
  [Width-cut criterion](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1581)
  · [Width-cut criterion after deletions](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1623).
  For half bridges, the [copy-return test](OnlineReachabilityPreservers/BridgeVertexProjection.lean)
  uses walks of length at most \(\max(0,k-3)\) between distinct copies of
  one vertex. With the same width-cut condition, it gives \(M/16\),
  both original budgets, and all four original-average caps.
  [Cleaning with the copy-return test](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1885).
  The [actual-piece width test](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2142)
  searches only the precedence edges that survive both width cuts.
  It gives the same guarantee in both modes. Half bridges also require
  one of the sufficient degree-split conditions.
  [A strict example with the original widths](OnlineReachabilityPreservers/ActualPieceReturnAudit.lean).
  In half mode, [checking only returns to an earlier degree block](OnlineReachabilityPreservers/BackwardCopyReturns.lean)
  suffices for the degree split. Combined with the actual-piece width
  test, this gives the same \(M/16\) and original-average guarantee.
- The path-side result starts with admissible simple copied rows of mass
  \(M\) at least both positive budgets. The rows have at most \(4n/3\)
  labels and meet the original degree cap. Choose path gaps with no
  backward return of at most
  \(\max(0,k-3)\) edges in the precedence graph of those rows. If every
  run fits the original mean length rounded down, greedy packing keeps
  both original budgets, all four frozen caps and at least \(M/16\) of
  original mass in either bridge mode.
  [Chosen path gaps](OnlineReachabilityPreservers/PackedDegreeGaps.lean#L274).
- The two packings compose. The original simple rows exclude the chosen
  bridges through \(k\) and their mass \(M\) is at least both positive budgets.
  Choose degree runs of size at most \(\lfloor M/n\rfloor\) and then path runs of
  size at most \(\lfloor M/p\rfloor\) on the resulting rows. Half mode requires
  each chosen degree gap to pass the earlier-copy return test on the
  original graph. In both modes the path test uses the full precedence
  graph of the resulting copied rows.
  Packing preserves the full original mass. Restricting the supports and
  peeling give at least \(M/16\) with both budgets and all four frozen caps.
  [Compose the two packings](OnlineReachabilityPreservers/PackedDegreeGaps.lean#L295).
- The mean-run and factor-four run bounds can both fail. On \(2m-1\)
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
- A rank test on the actual pieces can handle those returns. The parent
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
- The rank condition has a finite component test. Start with the actual
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
- Each bridge through \(k\) lies in one component of the constraint graph.
  If different pieces of the same parent meet that component, test short
  returns using only the vertices and comparisons in the component.
  The return radius is \(\max(0,k-3)\) and the comparisons between pieces
  use the copied parent rows. Start with simple paths, positive budgets and
  mass \(M\) at least both budgets. With admissible degree copies, passing
  this test at the two original widths preserves either bridge exclusion
  and gives a frozen witness with mass at least \(M/16\), both budgets and
  all four caps.
  [Restriction proof](OnlineReachabilityPreservers/BridgeRiverRanks.lean#L103) · [Component return test](OnlineReachabilityPreservers/RiverDetourComponents.lean#L171) · [Frozen witness](OnlineReachabilityPreservers/RiverDetourComponents.lean#L192).
- A separate projection works for disjoint pieces that may interleave
  within their parent rows. Require each original comparison between
  different pieces of the same parent to have no projected return within
  \(\max(0,k-3)\) edges. The lift takes the detour after its last
  visit to the river parent, then shortcuts other repeated parents
  in their row order. It preserves the river parent and the last
  arc parent, so the same cutoff holds in full mode and in half
  mode when pieces follow their parents’ arrival order.
  [Return condition](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2639) · [Bridge projection](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2649) · [Full bridge exclusion](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2762) · [Half-bridge exclusion](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2779).
- For the vertex-copy step, the two copies of a repeated projected corner
  must be nonconsecutive along the detour and cannot be the two river
  endpoints. The first and last arcs of the closed projected part are on
  distinct rows. The interior return takes at most \(\max(0,k-4)\) steps
  in the original precedence graph. If the copies agree at the ends
  of every such short return and all comparisons project to their original
  rows, each bridge through the cutoff projects with distinct corners and
  the same arc and river labels. This preserves either exclusion.
  [Agreement of vertex copies](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2798) · [Lift with distinct projected corners](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2807) · [Preservation in either mode](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2871).
- For simple rows admissible at the chosen cutoff, group the incident rows
  at each vertex so the first and last rows of each tested short return are
  together. Assume the groups
  are disjoint and fit the degree width. Choose a valid partition with the
  minimum number of groups and use the groups as copies. Every original
  row is recovered by projection, each degree is within the width, and at
  most one copy of each vertex is at or below half the width. For simple
  input, the copies preserve the chosen full or half exclusion.
  [Short-return pairs of incident rows](OnlineReachabilityPreservers/ShortReturnVertexPacking.lean#L14) · [Bounded degree groups](OnlineReachabilityPreservers/ShortReturnVertexPacking.lean#L21) · [Admissible capped degree copies](OnlineReachabilityPreservers/ShortReturnVertexPacking.lean#L29).
- Start with simple rows whose mass \(M\) is at least both positive
  budgets. If standard degree copying at the original width preserves
  the cutoff, protect the endpoints of each row comparison with a
  backward return through \(\max(0,k-3)\) in the copied precedence graph.
  If each protected support fits the original path width, pack it
  into block zero and keep the row order within each piece. This
  keeps every incidence before trimming and yields the indexed
  \(M/16\) witness with the cutoff, both budgets and all four frozen caps.
  [Protected vertices](OnlineReachabilityPreservers/HalfFiveTerminalPacking.lean#L471) · [Preservation through the cutoff](OnlineReachabilityPreservers/HalfFiveTerminalPacking.lean#L499) · [Frozen witness at both original widths](OnlineReachabilityPreservers/HalfFiveTerminalPacking.lean#L528).
- For simple rows already admissible at the given cutoff, the protected
  endpoints can be placed in several groups per row. Assume a disjoint
  partition within the path width, with both endpoints of every tested
  comparison in one group. A minimum-cardinality partition has at most
  one piece of length at most half the width per parent. Filtering each
  row by its group keeps the original order, every incidence and every
  vertex degree. It preserves the given full or half cutoff, with the
  pieces in parent arrival order in half mode.
  [Partition constraints](OnlineReachabilityPreservers/ShortReturnPiecePacking.lean#L107) · [Minimum-size partition](OnlineReachabilityPreservers/ShortReturnPiecePacking.lean#L89) · [Degree-preserving pieces](OnlineReachabilityPreservers/ShortReturnPiecePacking.lean#L116).
- For simple input of mass \(M\) at least both positive budgets, apply
  the grouping to admissible standard degree copies at the original
  width. If each copied row admits the partition at the original path
  width, the full degree blocks and the pieces above half the path
  width give quadratic loss bounds for the two support trims. Their
  individual losses are at most \(M/12\) and \(M/8\). After frozen peeling,
  the indexed witness has mass at least \(M/4\), both budgets, all four
  caps and the original full or half cutoff.
  [Two support trims](OnlineReachabilityPreservers/FrozenQuadraticTrimming.lean#L154) · [Frozen quarter-mass witness](OnlineReachabilityPreservers/ShortReturnPiecePacking.lean#L241).
- The two support trims also apply when the degree groups have varying
  sizes. Assume simple admissible copies of mass \(M\) at least both
  positive budgets, with all degrees within the original width. At most
  \(n\) copy labels may have degree at or below half that width. If the
  copied rows admit the short-return
  path partition at the original path width, each support trim loses at
  most \(M/8\). The later peeling uses the two original lower caps and
  leaves a frozen witness of mass at least \(M/4\) within both budgets.
  [Separate heavy-group thresholds](OnlineReachabilityPreservers/FrozenQuadraticTrimming.lean#L85) · [Frozen cleaning from both grouped profiles](OnlineReachabilityPreservers/ShortReturnVertexPacking.lean#L198).
- The path-group bound can be checked on the original rows. Exact row
  projection sends every copied return and its linked component to the
  original graph. Projection is injective on each copied row, so its
  component size cannot grow. For simple admissible input of mass \(M\)
  at least both positive budgets, bounded degree groups at the original
  degree width and original row components within the original path
  width give a frozen \(M/4\) witness outright. Both budgets, all four caps
  and the chosen cutoff hold in either exclusion mode.
  [Component size does not increase under row copying](OnlineReachabilityPreservers/ShortReturnPieceComponents.lean#L137) · [Frozen cleaning under both original-width tests](OnlineReachabilityPreservers/ShortReturnVertexPacking.lean#L260).
- The degree grouping premise has a finite component test too. For each
  original vertex, connect any two incident rows that start and end a
  tested short return there. A partition respecting those links exists
  at the degree width exactly when each component fits. If both the
  degree and path components fit their original widths, the on-input
  tests give the frozen indexed quarter-mass witness at the chosen cutoff.
  [Components and bounded partitions](OnlineReachabilityPreservers/ShortReturnPieceComponents.lean#L49) · [Graph of linked incident rows](OnlineReachabilityPreservers/ShortReturnVertexPacking.lean#L286) · [Exact degree component criterion](OnlineReachabilityPreservers/ShortReturnVertexPacking.lean#L308) · [Frozen witness from both finite tests](OnlineReachabilityPreservers/ShortReturnVertexPacking.lean#L326).
- For distinct nonempty simple inputs with positive budgets and mass
  \(M\) at least the vertex budget, the same tests apply at every
  admissible cutoff of at least two. The literal transfer gives
  a distinct nonempty witness of mass at least \(M/8\), within both original
  budgets and all four original caps, preserving the chosen cutoff.
  [Frozen cleaning for distinct nonempty paths](OnlineReachabilityPreservers/ShortReturnDistinctCleaning.lean#L10).
- Restricting simple rows to sublists can only shrink the two component
  graphs and their components. Delete each incidence for which either
  original component exceeds its width. The restricted rows satisfy
  both component bounds at those same widths. Retained mass plus the
  number of deleted incidences equals the original mass. An incidence
  with two oversized components contributes one to the loss.
  [Exact mass of removed incidences](OnlineReachabilityPreservers/ShortReturnOverflow.lean#L92) · [Retained mass plus removed mass](OnlineReachabilityPreservers/ShortReturnOverflow.lean#L99) · [Both component bounds after deletion](OnlineReachabilityPreservers/ShortReturnOverflow.lean#L108).
- The two support trims can use the smaller retained mass in their
  quadratic loss bounds while keeping the original widths. For simple
  admissible input of mass \(M\) at least both positive budgets, a
  sublist restriction that retains at least \(2M/3\) and satisfies both
  component tests at the original widths yields an indexed witness of
  mass at least \(M/18\) with both budgets, the chosen cutoff and all four
  frozen caps. In particular this applies when the original oversized
  components account for at most \(M/3\) deleted incidences.
  [Grouped width trimming after earlier losses](OnlineReachabilityPreservers/ShortReturnVertexPacking.lean#L140) · [Frozen witness from a two-thirds restriction](OnlineReachabilityPreservers/ShortReturnOverflow.lean#L158) · [Frozen witness from the overflow bound](OnlineReachabilityPreservers/ShortReturnOverflow.lean#L200).
- Within a connected component, keep the first elements in the finite
  order up to the prescribed width. Disjointness ensures that a component
  of size \(s\) keeps exactly \(\min(s,w)\) elements at width \(w\). The loss
  over all distinct components is the sum of their excesses above \(w\).
  [Bounded selection from each component](OnlineReachabilityPreservers/ShortReturnPieceComponents.lean#L219) · [Exact selection size per component](OnlineReachabilityPreservers/ShortReturnPieceComponents.lean#L231) · [Mass lost to component excess](OnlineReachabilityPreservers/ShortReturnPieceComponents.lean#L254).
- For simple rows, first clip each degree component to the vertex width
  by keeping a bounded number of its row labels. Compute the path
  components and clip them to the path width. Both component bounds
  hold on the final sublists. The total loss is the degree excess on
  the original rows plus the path excess after the degree restriction.
  [Exact degree-component loss](OnlineReachabilityPreservers/ShortReturnComponentClipping.lean#L63) · [Exact path-component loss](OnlineReachabilityPreservers/ShortReturnComponentClipping.lean#L90) · [Successive clipping with both bounds](OnlineReachabilityPreservers/ShortReturnComponentClipping.lean#L146).
- For simple admissible input with mass \(M\) at least both positive
  budgets, compute the successive component excesses at the original
  widths. If their sum is at most \(M/3\), the indexed frozen witness
  has mass at least \(M/18\), both budgets, all four original caps and
  the chosen cutoff. The same guarantee holds for literal distinct
  nonempty input and output at cutoff at least two.
  [Indexed excess criterion](OnlineReachabilityPreservers/ShortReturnComponentClipping.lean#L174) · [Literal excess criterion](OnlineReachabilityPreservers/ShortReturnComponentClipping.lean#L202).
- For two fixed partitions of the same finite incidence set, a deleted
  incidence can spend one unit of excess in both of its classes. A shared
  deletion set may use at most the original excess in each class of either
  partition. There is a deletion set meeting both fixed widths within a
  given budget exactly when the total of the two excesses is at most
  that budget plus the size of some shared deletion set. This comparison
  uses the original class labels throughout.
  [Exact criterion for two partitions](OnlineReachabilityPreservers/SharedCapacityClipping.lean#L87).
- For two fixed partitions, enumerate the feasible shared sets and
  maximize their cardinality. The exact minimum deletion count is the
  sum of the two total excesses minus this maximum. A deletion set
  attains that count while meeting both widths, and every feasible
  deletion set has at least that many incidences.
  [Maximum shared credit](OnlineReachabilityPreservers/SharedCapacityOptimum.lean#L30) · [Budget equivalence](OnlineReachabilityPreservers/SharedCapacityOptimum.lean#L72) · [Attained minimum](OnlineReachabilityPreservers/SharedCapacityOptimum.lean#L91).
- Apply the fixed-partition criterion to the degree and path components
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
- For simple input rows at a fixed cutoff, each recomputed degree or path
  class after rowwise deletion lies within one original class. Total excess
  on each side therefore cannot
  increase at a fixed width. When deletions spend at most the original
  excess in each class of both fixed partitions, the two fixed excess sums
  decrease by exactly the number of deletions. Recomputing the components
  reduces each excess by at least that much and can reduce it further by
  splitting a class.
  [Fixed-label accounting](OnlineReachabilityPreservers/SharedCapacityClipping.lean#L150) · [Excess under refinement](OnlineReachabilityPreservers/SharedCapacityClipping.lean#L167) · [Excess under sublists](OnlineReachabilityPreservers/ShortReturnExcessRefinement.lean#L63) · [Excess saved after recomputation](OnlineReachabilityPreservers/ShortReturnExcessRefinement.lean#L78).
- An arbitrary rowwise restriction of simple admissible input can precede
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
- A seven-vertex spine with its six adjacent backward darts attaches at
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
- Arbitrary initial sublists can also precede the shared deletion test.
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
- When differently labelled row families can meet only at one fixed
  common vertex, any bridge stays within its river's family. The first and last
  steps outside that family would require the shared vertex at two
  different corners. Combining such families preserves either bridge
  exclusion through any common cutoff with the original arrival order.
  [Localize a bridge at a one-vertex intersection](OnlineReachabilityPreservers/BridgeAtJoint.lean#L13) · [Preserve both exclusions](OnlineReachabilityPreservers/BridgeAtJoint.lean#L56).
- A checked shared-deletion instance attaches two reversed length-15
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
- For simple rows, standard degree copying preserves full exclusion
  through any chosen cutoff. For such input that excludes full bridges
  through the cutoff and has mass at least both positive budgets,
  the original path-component bound alone gives the frozen quarter-mass
  witness. A restriction retaining at least two thirds of the original mass and
  passing the same path test also suffices for a frozen \(M/18\) witness.
  In particular it suffices that original path excess is at most \(M/3\).
  The latter conclusion has a literal distinct nonempty version at
  cutoff at least two, with the same budgets, cutoff and four frozen caps.
  [Full cleaning with the original path bound](OnlineReachabilityPreservers/ShortReturnFullCleaning.lean#L11) · [Full cleaning after a path-only restriction](OnlineReachabilityPreservers/ShortReturnFullCleaning.lean#L28) · [Full cleaning from path excess](OnlineReachabilityPreservers/ShortReturnFullCleaning.lean#L47) · [Literal full-bridge witness](OnlineReachabilityPreservers/ShortReturnFullCleaning.lean#L62).
- The path-component criterion also applies in half mode whenever standard
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
  [Degree test](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1550) · [Degree test after sublists](OnlineReachabilityPreservers/ShortReturnStandardCleaning.lean#L11) · [Original path room](OnlineReachabilityPreservers/ShortReturnStandardCleaning.lean#L52) · [Path room after restriction](OnlineReachabilityPreservers/ShortReturnStandardCleaning.lean#L125) · [Path-excess witness](OnlineReachabilityPreservers/ShortReturnStandardCleaning.lean#L146) · [Literal path-excess witness](OnlineReachabilityPreservers/ShortReturnStandardCleaning.lean#L170).
- Another path test keeps the labels of the original degree copies after
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
- The component clipping loss is optimal among subsets with at most the
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
- A second full-mode example uses indexed rows with budgets 51 and 23, two opposing
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
- The bidirected 23-leaf star has one row per dart, 24 vertices and 46
  rows of mass 92. Every full bridge is excluded. Its original widths
  are 15 for degree and eight for path length. At cutoff seven, the
  center has a single degree component of size 46. Its excess of 31
  already exceeds one third of the total mass. The path components
  fit, so the full-mode path test gives the original-budget quarter-mass
  witness at cutoff seven.
  [Full exclusion at every cutoff](OnlineReachabilityPreservers/ShortReturnFullCleaningStar.lean#L68) · [The center component](OnlineReachabilityPreservers/ShortReturnFullCleaningStar.lean#L140) · [Original widths](OnlineReachabilityPreservers/ShortReturnFullCleaningStar.lean#L144) · [Failure of the two-sided excess test](OnlineReachabilityPreservers/ShortReturnFullCleaningStar.lean#L151) · [Full frozen witness at cutoff seven](OnlineReachabilityPreservers/ShortReturnFullCleaningStar.lean#L171).
- The path-partition premise has an exact finite test. Within one row,
  link the endpoints of every comparison with a short backward return.
  Each connected component must lie in one group of any valid partition.
  When every component fits the width, the components themselves give a
  valid partition. For admissible standard degree copies at the original
  width, this test at the original path width gives the same indexed
  \(M/4\) witness in either mode.
  [Graph of linked endpoints](OnlineReachabilityPreservers/ShortReturnPieceComponents.lean#L102) · [Exact component criterion](OnlineReachabilityPreservers/ShortReturnPieceComponents.lean#L121) · [Frozen quarter-mass witness](OnlineReachabilityPreservers/ShortReturnPieceComponents.lean#L184).
- A six-vertex family with twelve indexed rows and mass twelve has one
  increasing row, three disjoint backward pairs and eight empty labels.
  The original degree and path widths are eight and four. At cutoff
  four, all six vertices of the long row are protected, so a single
  protected block would overflow. Each connected group has at most two
  vertices at every cutoff. With the same widths, the partition method
  gives the frozen quarter-mass witness at every full cutoff.
  [Full exclusion before splitting](OnlineReachabilityPreservers/ShortReturnPieceComponentExample.lean#L43) · [Component width bound](OnlineReachabilityPreservers/ShortReturnPieceComponentExample.lean#L96) · [Single-block limit](OnlineReachabilityPreservers/ShortReturnPieceComponentExample.lean#L146) · [Frozen witness at every full cutoff](OnlineReachabilityPreservers/ShortReturnPieceComponentExample.lean#L159).
- An eight-vertex example shows a limit of the disjoint-component rank test.
  Its seven original rows exclude full bridges through three. Standard
  width-two blocks form a directed cycle. Each vertex starts a strict
  comparison in only one piece, so the pieces exclude full bridges at
  every cutoff. The two pieces of the first parent share an SCC in the
  detour constraint graph at every cutoff. The example uses a supplied
  width of two. Its original factor-four cap is nine.
  [Original exclusion](OnlineReachabilityPreservers/RiverDetourRankLimits.lean#L27) · [All-size exclusion after the split](OnlineReachabilityPreservers/RiverDetourRankLimits.lean#L64) · [Component test failure](OnlineReachabilityPreservers/RiverDetourRankLimits.lean#L72).
- The same limitation occurs at the prescribed path width. Use
  \(2m+16\) vertices and \(2m+3\) rows. Put two portions of eight consecutive
  vertices of a directed cycle in one row. Each step on the two connecting
  chains has its own row. Each chain has \(m+1\) edges, and the original
  system excludes full bridges through \(m+1\). The mass is \(4m+20\) and for
  \(m\ge 27\) the original factor-four path width is eight. Splitting the
  original rows at that width preserves full exclusion at every size.
  The two pieces of the central row share a component of the constraint
  graph at every cutoff.
  [Original exclusion](OnlineReachabilityPreservers/LongRankCriterionCycle.lean#L215) · [Original path width and component test](OnlineReachabilityPreservers/LongRankCriterionCycle.lean#L495).
- The original factor-four degree width is seven. Every vertex has degree
  at most three, so it keeps its block-zero label. The degree copies exclude
  full bridges through \(m+1\). After splitting at width eight, the pieces
  exclude full bridges at every size and the same two pieces still share a
  component of the constraint graph. Restricting the supports of the pieces
  and peeling gives a frozen witness of mass at least \(M/16\), with
  both original budgets and all four caps.
  [Admissibility and component test at both widths](OnlineReachabilityPreservers/LongRankCriterionCycle.lean#L706) · [Frozen witness from the original widths](OnlineReachabilityPreservers/LongRankCriterionCycle.lean#L731).
- A finer finite graph joins each possible river’s start to every vertex on
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
- The full bridges through \(k\) give exact constraints on the arrival
  order. Require the river to precede the final arc of each such bridge.
  There is a half-\(k\)-free ordering of all the rows exactly when the
  directed graph of these constraints is acyclic. At the two original
  widths, an acyclic graph on the pieces permits a new arrival order
  without losing incidences. For simple input with mass \(M\) at least both
  positive budgets, the reordered pieces give a half-\(k\)-free witness of
  mass at least \(M/16\) within both original budgets and all four frozen caps.
  [Exact order constraint](OnlineReachabilityPreservers/HalfBridgeArrivalOrder.lean#L56) · [Frozen cleaning after reordering](OnlineReachabilityPreservers/HalfBridgeArrivalOrder.lean#L228).
- Taking sublists of simple pieces can only remove arrival constraints.
  Keep the original degree copies and path blocks when deleting incidences.
  If the surviving pieces have acyclic constraints through \(k\) and
  the deletion costs at most \(M/18\), reordering, restriction and peeling
  retain \(M/32\) with both original budgets and all four frozen caps.
  [Constraint monotonicity](OnlineReachabilityPreservers/HalfBridgeArrivalOrder.lean#L87) · [Frozen cleaning after arrival deletions](OnlineReachabilityPreservers/HalfBridgeArrivalOrder.lean#L248).
- For simple input of mass \(M\) at least both positive budgets, discard
  unused copy and row labels when both occupied supports fit. Restricting
  the labels preserves acyclicity and every retained incidence. For mass
  \(K\) with \(a\) occupied vertices and \(b\) nonempty rows, peeling retains at least
  \(K-aM/(4n)-bM/(4p)\). At the original widths with acyclic constraints and
  both occupied supports fitting, losing at most \(M/4\) still gives an
  indexed witness with at least \(M/4\), both budgets and all four frozen caps.
  [Acyclicity under restriction](OnlineReachabilityPreservers/HalfBridgeArrivalOrder.lean#L268) · [Peeling with occupied supports](OnlineReachabilityPreservers/HalfBridgeArrivalOrder.lean#L289) · [Quarter-loss guarantee at the original widths](OnlineReachabilityPreservers/HalfBridgeArrivalOrder.lean#L335).
- An arrival constraint survives an incidence deletion exactly when some
  pre-deletion bridge on the pieces retains every required corner occurrence.
  Fix any injective ranking of the pieces. It respects the surviving constraints
  exactly when the deletions hit every original bridge whose final arc ranks
  earlier than its river. If the deletions hit every such bridge through \(k\)
  and cost at most \(M/18\) actual incidences at the original widths, the
  indexed half-\(k\)-free witness retains at least \(M/32\), both original
  budgets and all four frozen caps.
  [Survival of an arrival constraint](OnlineReachabilityPreservers/HalfBridgeArrivalRepair.lean#L35) · [Exact cover for a ranking](OnlineReachabilityPreservers/HalfBridgeArrivalRepair.lean#L62) · [Frozen cleaning from an incidence cover](OnlineReachabilityPreservers/HalfBridgeArrivalRepair.lean#L83).
- Choose a set of arrival edges whose removal makes the graph acyclic.
  For each chosen edge, delete on its final arc piece every vertex shared
  with its river piece. Each bridge giving the edge uses one of those
  occurrences. The surviving graph is a subgraph of the graph with the
  chosen edges removed. If the sum of the selected intersection sizes
  is at most \(M/18\), this gives the indexed \(M/32\) guarantee for simple
  input of mass at least both positive budgets, with all four frozen caps.
  [Count of erased incidences](OnlineReachabilityPreservers/HalfBridgeArrivalRepair.lean#L137) · [Surviving constraints](OnlineReachabilityPreservers/HalfBridgeArrivalRepair.lean#L146) · [Frozen cleaning from selected edges](OnlineReachabilityPreservers/HalfBridgeArrivalRepair.lean#L169).
- Start with simple rows excluding half-bridges through five. Each copied
  comparison projects to a comparison on the same original row. The
  sufficient rank test at each vertex compares the river and final arc
  of a full three-bridge ending there and the start and return rows of
  a two-step return. Weak increase on these edges preserves half-five
  exclusion when a vertex and rank determine its copy. Every assignment
  in this test is constant on each strongly connected component. The
  component ranks distinguish all different components.
  [Terminal constraint graph](OnlineReachabilityPreservers/HalfFiveTerminalRank.lean#L13) · [Half-five copy preservation](OnlineReachabilityPreservers/HalfFiveTerminalRank.lean#L158) · [Forced equalities within components](OnlineReachabilityPreservers/HalfFiveTerminalRank.lean#L174) · [Exact component ranks](OnlineReachabilityPreservers/HalfFiveTerminalRank.lean#L215).
- The explicit rank assignment copies each occurrence to its vertex and
  assigned rank. An example on six rows already excludes half-bridges at
  every size. A three-bridge and a two-step return force equal ranks for
  two rows at vertex 2. The assigned ranks at that vertex decrease on the
  two last rows, both of which end a comparison there. The local test
  still gives half-five exclusion on the copied family.
  [Vertex copying by rank](OnlineReachabilityPreservers/HalfFiveTerminalRank.lean#L238) · [Original exclusion](OnlineReachabilityPreservers/HalfFiveTerminalRankExample.lean#L35) · [Rows in the same terminal component](OnlineReachabilityPreservers/HalfFiveTerminalRankExample.lean#L65) · [Half-five exclusion after copying](OnlineReachabilityPreservers/HalfFiveTerminalRankExample.lean#L77) · [Ranks decreasing in arrival order](OnlineReachabilityPreservers/HalfFiveTerminalRankExample.lean#L84).
- A four-row family on six vertices excludes all full bridges. Its first
  two rows share vertices 0 and 1 in reverse order. At each of these
  vertices, return edges put both rows in one strongly connected component.
  Every assignment passing the terminal rank test therefore gives these
  two rows two common copied vertices. The test by itself can preserve
  half-five exclusion while leaving repeated intersections.
  [Original full exclusion](OnlineReachabilityPreservers/HalfFiveTerminalRankCoincidence.lean#L28) · [Two terminal cycles](OnlineReachabilityPreservers/HalfFiveTerminalRankCoincidence.lean#L41) · [Forced common copies](OnlineReachabilityPreservers/HalfFiveTerminalRankCoincidence.lean#L55).
- The degree-copy test can use a smaller graph. Keep both rank comparisons
  only for a three-bridge ending at the vertex followed by a two-step
  return to it, with five distinct rows and the returning row earlier
  than the river. Every projected half-five obstruction produces this
  pattern. The same weak-rank inequalities still preserve half-five
  exclusion. The smaller graph is empty at any vertex with no full
  three-bridge ending there, including every vertex of the four-row example.
  [Collision patterns](OnlineReachabilityPreservers/HalfFiveTerminalRank.lean#L31) · [Subgraph of the broad test](OnlineReachabilityPreservers/HalfFiveTerminalRank.lean#L63) · [Half-five preservation with the smaller graph](OnlineReachabilityPreservers/HalfFiveTerminalRank.lean#L253) · [Empty smaller graph in the example](OnlineReachabilityPreservers/HalfFiveTerminalRankCoincidence.lean#L78).
- For simple half-five-free input, an explicit degree-copy assignment
  preserves half-five exclusion exactly when it realizes none of the
  projected terminal patterns. A pattern is realized when ranks match
  at all five joins, including the two joins with the river, and the
  two projected terminal copies have distinct ranks. Lean lifts each
  realized pattern to a half-five bridge and recovers a realized pattern
  from each forbidden bridge among the copies.
  [Realized joins](OnlineReachabilityPreservers/HalfFiveTerminalRank.lean#L325) · [Lift to a forbidden half-five](OnlineReachabilityPreservers/HalfFiveTerminalRank.lean#L370) · [Exact copy criterion](OnlineReachabilityPreservers/HalfFiveTerminalRank.lean#L449).
- At each vertex, put the rows involved in any projected collision constraint
  first in its degree packing order. If those rows fit into one block of
  the original width, all collision rank inequalities hold. Each copy degree
  is within the cap, and projection recovers every original row. For simple
  half-five-free input of mass at least both positive budgets with path
  lengths already within the original cap, the construction gives an indexed
  witness of mass at least \(M/4\) with both budgets and all four frozen caps.
  [Constrained rows](OnlineReachabilityPreservers/HalfFiveTerminalPacking.lean#L18) · [Degree cap](OnlineReachabilityPreservers/HalfFiveTerminalPacking.lean#L135) · [Half-five exclusion](OnlineReachabilityPreservers/HalfFiveTerminalPacking.lean#L148) · [Frozen witness with capped path lengths](OnlineReachabilityPreservers/HalfFiveTerminalPacking.lean#L174).
- To handle long rows after degree packing, protect both endpoints of each
  comparison reversed on another copied row. Put the protected vertices
  first in the packing order, then keep the original order within each piece.
  If the protected vertices of every row fit the path width, the pieces
  preserve half-five exclusion in parent arrival order. When both protected
  supports fit their widths, these two packings keep every incidence before
  restriction and peeling. For simple half-five-free input of mass at least
  both positive budgets, the indexed witness has both original budgets,
  all four frozen caps and mass at least \(M/16\).
  [Protected path vertices](OnlineReachabilityPreservers/HalfFiveTerminalPacking.lean#L332) · [Half-five path splitting](OnlineReachabilityPreservers/HalfFiveTerminalPacking.lean#L375) · [Exact mass](OnlineReachabilityPreservers/HalfFiveTerminalPacking.lean#L362) · [Frozen cleaning with both packings](OnlineReachabilityPreservers/HalfFiveTerminalPacking.lean#L433).
- The usual nested split example can be padded to six vertices and ten
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
- On this same six-vertex example, packing the reversed corners
  keeps both prescribed widths and the original arrival order. The
  packed pieces exclude half-bridges through five and give the frozen
  witness of mass at least \(10/16\) with both budgets and all four caps.
  [Prescribed packings](OnlineReachabilityPreservers/HalfFiveTerminalPackingExample.lean#L53) · [Ordinary split and packed pieces](OnlineReachabilityPreservers/HalfFiveTerminalPackingExample.lean#L72) · [Frozen witness](OnlineReachabilityPreservers/HalfFiveTerminalPackingExample.lean#L82).
- The midpoint obstruction also occurs at both prescribed widths in a
  literal family. Add one extra vertex to the split row and 41 distinct
  singleton rows. The input has 49 vertices and 45 distinct nonempty
  rows of mass 56. It excludes half-bridges through four and both
  factor-four widths are four. On the resulting pieces, the size-three
  and size-four bridges impose a directed two-cycle. Every arrival order
  fails at cutoff four and above. Four disjoint two-vertex rows give a
  separate literal witness of mass eight, full exclusion at every size,
  both original budgets and all four frozen caps.
  [Literal input parameters](OnlineReachabilityPreservers/HalfBridgeArrivalObstruction.lean#L23) · [Original half-four exclusion](OnlineReachabilityPreservers/HalfBridgeArrivalObstruction.lean#L88) · [Cyclic constraints at both widths](OnlineReachabilityPreservers/HalfBridgeArrivalObstruction.lean#L177) · [Separate literal witness](OnlineReachabilityPreservers/HalfBridgeArrivalObstruction.lean#L193).
- Deleting vertex 5 from the row \([2,5]\) leaves mass 55 and removes the
  size-three constraint. The size-four bridge still violates the original
  arrival order. From cutoff four onward its river-to-final-arc comparison
  is the only constraint. The new order after this deletion gives an
  indexed witness at every cutoff, with mass at least \(56/32\), both
  original budgets and all four frozen caps.
  [Retained mass](OnlineReachabilityPreservers/HalfBridgeArrivalObstruction.lean#L355) · [Half-four bridge in the retained order](OnlineReachabilityPreservers/HalfBridgeArrivalObstruction.lean#L321) · [Exact retained constraint](OnlineReachabilityPreservers/HalfBridgeArrivalObstruction.lean#L328) · [Frozen witness after reordering](OnlineReachabilityPreservers/HalfBridgeArrivalObstruction.lean#L367).
- In the indexed convention, pad the four midpoint rows with eight empty
  labels. The input has seven vertices, twelve row labels and mass 14.
  It excludes half-bridges through four. At its original degree and path
  widths eight and four, two bridges impose opposite arrival orders.
  The loss bound \(M/18\) allows zero deletions in this example, so
  every sublist family within that loss bound still has cyclic constraints
  at cutoff four and above. The unrestricted half-four cleaning result
  supplies a separate witness at cutoff four.
  [Input parameters](OnlineReachabilityPreservers/HalfBridgeArrivalBudgetAudit.lean#L14) · [Original half-four exclusion](OnlineReachabilityPreservers/HalfBridgeArrivalBudgetAudit.lean#L19) · [Failure of the small-deletion premise](OnlineReachabilityPreservers/HalfBridgeArrivalBudgetAudit.lean#L86) · [Unrestricted half-four cleaning](OnlineReachabilityPreservers/FrozenHalfFourCleaning.lean#L469).
- After [deletions from the fixed degree copies](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2620),
  test for short returns in the pieces of the retained rows. If the
  copied input has the required bridge exclusion, at most \(M/18\)
  incidences are deleted, and the surviving pieces pass the test,
  the cleaned witness keeps \(M/32\) with both original budgets and
  all four original-average caps.
  In half mode, [test earlier-block returns after the same deletions](OnlineReachabilityPreservers/BackwardCopyReturns.lean#L249).
  The starting input has half exclusion through the cutoff. With retained
  copied rows passing both return tests, the \(M/32\) guarantee applies
  even if degree copying introduced a forbidden bridge before deletion.
- For simple paths with the matching bridge exclusion and incidence mass
  \(M\) at least both positive budgets, the cuts can move around individual
  short returns within a row. Pack whole runs between safe boundaries.
  If each run fits into one original mean path length, keep at least
  \(M/16\). At the wider
  factor-four cap the bound is \(M/54\). If longer runs carry at most
  \(M/56\) incidences, delete them first and keep at least \(M/108\).
  All three results preserve both budgets and all four original-average
  caps. They retain the input bridge exclusion through the cutoff, with
  the degree split conditions for half bridges.
  [Cutting between short-return runs](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1790)
  · [Choosing safe boundaries after copying degrees](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2236)
  · [Deleting long runs from fixed degree copies](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2352)
  · [Clipping only the excess of each copied run](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L2530)
  · [After removing long runs](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1846).
- [`lemma24_left_injective`, `lemma24_right_monotone`](OnlineReachabilityPreservers/IntersectionOrder.lean)
  order the intersection chains on each pair of outer paths in Appendix A.
  [`lemma26_chain_lower` and `lemma27_acyclic`](OnlineReachabilityPreservers/PairwiseInitial.lean)
  prove the initial incidence bound on systems with a common vertex order by
  counting high-degree incidences with enough predecessors. The same module's
  `pairwise_initial` proves an online `O(n + (np)^(2/3))` edge bound on general
  digraphs, with the exact cubic inequality stated in Lean.
- [`lemma28_from_incidence`, `lemma28_mean_lower`, and `lemma41_branch_count`](OnlineReachabilityPreservers/ClosePairs.lean)
  give the finite close-pair and sampled-subsystem counts used in Appendices A
  and B for systems with a common vertex order. Summing over the base paths
  gives the numerator of the uniform expectation. In the dense regime the
  expectation is at least the squared product of the two averages divided by
  `4096`. The proof also retains the factor that grows with the window size.
  The full-bridge-free proof
  bounds the contribution by the ordered pairs of vertices on the restricted paths.
- [`theorem38_root`, `theorem38_exponent_limits`, and `theorem43_exponent_limit`](OnlineReachabilityPreservers/ExponentLimits.lean)
  check the online cubic root and both arithmetic iterations.
  [OfflineBound](OnlineReachabilityPreservers/OfflineBound.lean) applies each
  Appendix B update to acyclic full-bridge-free systems, including the
  integer branching window, split budgets, and sparse regimes.
- [`lemma37_acyclic_update` and `theorem38_acyclic_iteration`](OnlineReachabilityPreservers/OnlineBound.lean)
  prove the corrected Appendix A update and each finite online iterate.
  The chosen integer window scales with the constant in the inductive estimate.
  The lower mean absorbs the linear contribution and the two window
  exceptions give the claimed rates directly.
- [`theorem1_rounded` and `theorem1_limiting_rate`](OnlineReachabilityPreservers/OnlineSharp.lean)
  prove both adaptive online edge bounds for the actual forward-growth
  preserver on arbitrary finite digraphs, at every prefix. The limiting proof
  chooses one nonnegative slack function of the vertex count that tends to
  zero and works for every demand count. The small-demand bound keeps the
  coefficient of the linear term fixed.
- [`theorem14_acyclic_overlay_lower`](OnlineReachabilityPreservers/AcyclicOverlay.lean)
  checks the reverse construction in a common vertex order. Any preserver of
  the endpoint demands must retain exactly the total incidence count minus
  the path count in consecutive edges.
- [`theorem14_offline_extremal_lower`](OnlineReachabilityPreservers/OfflineBridgeConverse.lean#L315)
  proves the unrestricted converse. For every \(n\ge2\) and \(0\le p\le n^2\),
  one DAG on exactly \(n\) vertices with \(p\) distinct demands forces at
  least one twenty-fourth of the maximum fully bridge-free incidence mass.
  The [common-order construction](OnlineReachabilityPreservers/OfflineBridgeConverse.lean#L209)
  removes at most two incidences per vertex and keeps the last vertex
  of each nonempty path. A spanning path supplies the lower bound when
  the maximum mass is below \(6n\).
- For a fully bridge-free family of nonempty simple paths, let \(M\) be its
  incidence mass, \(n\) its vertex count, and \(J\) the total number of visits
  to strongly connected components of the precedence graph, counted once
  per path and component. For \(n\ge 2\), \(1\le p\le n^2\), and
  \(M\le C(n+J)\), a DAG on exactly \(n\) vertices with \(p\) distinct demands forces
  \(M\le 14C|E(H)|\) for every preserver \(H\). A component-wise linear
  bound suffices for this hypothesis. Applying that condition after
  opposite-intersection pruning gives factor \(28C\).
  [Component lower bounds](OnlineReachabilityPreservers/OfflineComponentOrders.lean#L246).
- The component condition has an [unbounded obstruction](OnlineReachabilityPreservers/OverlayLowerAudit.lean#L509).
  A lattice family with private return paths has \(M/(n+J)\) growing
  with the number of layers. Every path lies within one component and
  opposite-intersection pruning retains the entire family.
- [`theorem14_dag_compression` and `offline_pairwise_initial`](OnlineReachabilityPreservers/OfflineIndependence.lean)
  prove the constructive independence reduction on DAGs and its initial
  offline pairwise consequence on arbitrary digraphs. The algorithm deletes
  each dispensable edge and the proof assigns the surviving edges to requests
  that require them. The resulting acyclic system has size `m+p` and is fully
  bridge-free.
- [`theorem14_extremal_lower_in_linear_regimes`](OnlineReachabilityPreservers/OfflineConverseRegimes.lean)
  proves the converse for arbitrary simple local path orders when `p² ≤ K n`
  or `n² ≤ K p`, with `n ≥ 2`, `1 ≤ p ≤ n²`, and `K ≥ 1`.
  For a universal constant `C`, a DAG with exactly `n` vertices and `p`
  distinct demands forces at least `1/(C K)` of the mass of every simple
  path system that excludes full bridges through size four. Theorem 43
  bounds that mass by a linear term in each regime.
- [`layered_offline_lower`](OnlineReachabilityPreservers/OverlayLowerAudit.lean)
  gives DAGs on \(4(L+1)L^5\) vertices with \(L^6\) distinct feasible demands
  that force exactly \(L^7\) edges for every positive integer \(L\). This gives
  a superlinear lower bound when the vertex and demand counts are comparable.
- [`offline_lower_all_sizes_with_linear`](OnlineReachabilityPreservers/OfflineLatticeLower.lean)
  varies the layer and slope counts independently. For every \(n\ge2\) and
  \(1\le p\le n^2\), a DAG with exactly those counts forces
  \(\Omega(n+p+n^{2/3}p^{1/2})\) edges, with one absolute constant.
- [`lemma14_overlay_no_constant`](OnlineReachabilityPreservers/OverlayLowerAudit.lean)
  checks fully bridge-free simple path families for which the cited overlay
  and its distinct endpoint demands admit preservers arbitrarily smaller
  than the total incidence count minus the demand count.
- [`theorem4_rounded` and `theorem4_sharp`](OnlineReachabilityPreservers/OfflineSharp.lean)
  prove both offline edge bounds for the constructed preserver on arbitrary
  finite digraphs. Two acyclic updates suffice for the rounded bound.
  A single invariant constant gives the limiting rate
  `O(n + n^(3/4) p^(1/2) + n^(2−sqrt(2)) p^(1/sqrt(2)))`.
  The limiting exponents have zero slack. The exact list evaluator has a
  polynomial source-level work bound.
  [List evaluator for general digraphs](OnlineReachabilityPreservers/SccLiftListWork.lean#L1022).
- [`lemma37_first_term`, `lemma37_third_term`, and `lemma42_third_term`](OnlineReachabilityPreservers/BootstrapArithmetic.lean)
  verify the rearrangements of those individual branching-count terms.
  The third term of Lemma 42 gives vertex exponent `1/(b+1)`, the exponent
  implicit in Theorem 43. [OfflineArithmetic](OnlineReachabilityPreservers/OfflineArithmetic.lean)
  checks the complete three-term scalar comparison, including absorption of the
  logarithmic term into the two updated powers.
- [`lemma30_integral_square_sum`](OnlineReachabilityPreservers/IntegralMajorization.lean)
  checks the integral majorization step with explicit integrability hypotheses.
  [`lemma31_acyclic_moment`](OnlineReachabilityPreservers/SecondMoment.lean)
  proves the second-moment estimate given the inductive bound on subfamilies.
  It orders the actual path lengths and bounds four clipped powers with
  finite sums and integrals.
- [BranchingDegrees](OnlineReachabilityPreservers/BranchingDegrees.lean)
  checks the predecessor count and average in Lemmas 32–33 under the
  inductive size bound and a maximum-degree cap. It also proves the dyadic
  upper bound on off-base tuples in terms of the path moments of sampled
  vertex sets. A finite square-root triangle inequality retains each bucket
  moment without a separate factor for the number of buckets.
  [OffBaseMoment](OnlineReachabilityPreservers/OffBaseMoment.lean) expresses
  those inequalities as uniform means of the actual bucket statistics.
  [OffBaseAverage](OnlineReachabilityPreservers/OffBaseAverage.lean)
  proves the three off-base powers with no logarithmic loss and combines
  them with the on-base estimate by partitioning the qualifying tuples.
- [OnBaseCounting](OnlineReachabilityPreservers/OnBaseCounting.lean)
  proves the source-restricted bound for the actual systems in Lemma 35
  and counts tuples with their second endpoint on the base. The proof
  groups them by the left branching degree and charges each group to
  important incidences in the induced system.
  [OnBaseAverage](OnlineReachabilityPreservers/OnBaseAverage.lean) sums both
  sides of the dyadic threshold geometrically. Under the inductive incidence
  bound and uniform caps, the resulting expectation is bounded by a constant
  times `ℓ²d² + ℓ^(3/2)d²h^(5/4)` with no logarithmic loss.
- [Regularization](OnlineReachabilityPreservers/Regularization.lean)
  verifies an acyclic upper-cap reduction for Appendices A and B. Splitting
  vertices and consecutive path blocks preserves every incidence and both
  bridge conditions at every size. The new sizes are at most twice their
  original values, and each cap is at most four times the corresponding new average.
- [OfflineMoment](OnlineReachabilityPreservers/OfflineMoment.lean)
  checks the logarithmic second-moment bound and the resulting upper count
  on the actual offline sample. The proof uses the inductive size bound on
  full-bridge-free subfamilies and an ambient sample size at least the degree cap.
- [`lemma20_opt_squared` and `lemma22_hub_count`](OnlineReachabilityPreservers/SteinerCounting.lean)
  prove the terminal-counting lower bounds used in the Steiner application.
  [`lemma29_square_sum`](OnlineReachabilityPreservers/Majorization.lean) proves
  the weak-majorization step used in Appendix A.

Here `p` counts processed requests. For the paper's ordered set of distinct demands,
this is its demand cardinality. The model admits self-pairs and unreachable pairs.
For component contraction, unused vertex labels are isolated in the DAG, keeping
the budget parameter `n` equal to the original vertex count. The distinct-demand
lift forwards first occurrences in arrival order, even when two distinct original
demands project to the same pair. It preserves every request and adds at most
`2n` edges to a DAG budget that is monotone in demand and endpoint counts.
[Theorem 9](OnlineReachabilityPreservers/DagReduction.lean).

The algorithms are executable bounded searches on finite sets. The graph searches
iterate at most `n` times over finite vertex and edge sets, with a deterministic
minimum choice. SCC labels, internal trees, and crossing representatives depend
only on the input graph and can be precomputed. The [Steiner replay](OnlineReachabilityPreservers/SteinerDistanceReplay.lean)
also bounds weighted capacity-table construction and reuse, graph searches, and
original weight reads by a polynomial at fixed height. Finite container operations,
arithmetic bit costs, and construction and use of the finite index enumerations
still need end-to-end time bounds.

## Source and verification

The [statement map](STATEMENT_MAP.md) records the paper's claims, dependencies,
and remaining proofs. The [source notes](SOURCE_NOTES.md) record exact discrepancies.
[SourceAudit](OnlineReachabilityPreservers/SourceAudit.lean) verifies the counterexample
and corrected tail inequality for Lemma 25 and the recurrence discrepancy in Theorem 38.
[SplitAudit](OnlineReachabilityPreservers/SplitAudit.lean) checks that the path
split printed in Lemmas 23 and 39 can introduce a forbidden bridge in a general
path system.
[LocalOnlineLimit](OnlineReachabilityPreservers/LocalOnlineLimit.lean) proves
Theorem 38 for arbitrary simple paths with no half-bridge through size four.
One exponent slack depends only on the vertex count and tends to zero.
[LocalOfflineBound](OnlineReachabilityPreservers/LocalOfflineBound.lean) proves
Theorem 43 for arbitrary simple paths excluding full bridges through size
four, with the exact limiting exponent and a constant that works for every
vertex and path count.

Build from the repository root with `lake build OnlineReachabilityPreservers`.
The library is included in the repository's module index, declaration audit,
and kernel replay.

The companion PaperLab includes an interactive trace and a source-linked
proof map. Open cases include general cyclic cleaning at half cutoffs of
five or more, frozen-average cleaning under only a finite full cutoff of
seven or more, and a native execution-time bound for the Steiner algorithm.

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
[Companion PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site).
