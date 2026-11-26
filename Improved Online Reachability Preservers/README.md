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
  The [incremental thin evaluator](OnlineReachabilityPreservers/SteinerThinReplay.lean#L631)
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
  interval computations. The late replay also uses the arc list for
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
  · [Weighted early evaluator](OnlineReachabilityPreservers/SteinerFinWeightedReplayWork.lean#L285).
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
  [Charge magnitude after the weighted run](OnlineReachabilityPreservers/SteinerWeightedChargeWork.lean#L544)
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
  [Early rounding preparation](OnlineReachabilityPreservers/SteinerFinWeightedReplayWork.lean#L396)
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
  charges. Remaining work includes trial and tier containers, weighted
  search and its vertex enumeration, later service steps, and bit and
  native execution costs.
  [Prepared arithmetic](OnlineReachabilityPreservers/SteinerFinWeightedReplayWork.lean#L804)
  · [Complete replay with measured rounding](OnlineReachabilityPreservers/SteinerFinTraceReplayWork.lean#L2111).
- [The acyclic cleaning construction](OnlineReachabilityPreservers/BalancedRegularization.lean)
  retains at least a sixteenth of the incidence mass within the original vertex
  and path budgets. In the dense regime it proves the lower and upper caps
  from Lemmas 23 and 39 and preserves both bridge exclusions at every size.
  The [extremal conclusion](OnlineReachabilityPreservers/CommonOrderExtremal.lean)
  applies this at any positive vertex and path budgets in a common vertex order.
  For each bridge cutoff up to size three, the [locally ordered extremum](OnlineReachabilityPreservers/LocalOrderExtremal.lean)
  gives the same caps and mass guarantee at the corresponding maximum over all simple lists.
- At cutoff four, a cleaned witness for the unrestricted maximum in either
  bridge mode retains at least \(M/392\) of the maximizing incidence mass \(M\).
  It meets both budgets and all four factor-four bounds around its own
  averages. The same conclusion holds at the unrestricted full-bridge
  cutoff six. [Output-average cleaning](OnlineReachabilityPreservers/LocalAverageCleaning.lean).
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
  · [Frozen half-four cleaning](OnlineReachabilityPreservers/ContiguousHalfCleaning.lean#L335).
- Full bridge exclusion at every size bounds the loss under pruning to
  unique intersections by \(n-1\) for \(n>0\). Combining this bound with
  explicit low-mass witnesses gives the same frozen size-six conclusion
  for every simple all-size full-bridge-free input of mass at least both
  positive budgets.
  [Pruning bound](OnlineReachabilityPreservers/OppositeLinkForest.lean#L524)
  · [All-size input](OnlineReachabilityPreservers/ContiguousSixCleaning.lean#L151).
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
  [Cleaning with a small mass of long visits](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1081).
- At cutoff \(k\), the factor-four blocks retain at least \(M/16\) in either
  bridge mode when the precedence graph has no directed cycle of length at
  most \(k-2\). If removing at most \(M/18\) incidences from the rows suffices
  to obtain this property, the construction retains at least \(M/32\).
  Both guarantees use the two positive original budgets and all four caps
  computed from the original averages, for mass at least both budgets.
  [No short cycles](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1552)
  · [After deletions](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1600).
  The same bounds follow by ruling out short returns only across the
  actual width cuts. Full mode uses this condition alone. Half mode also
  uses one of the sufficient conditions for splitting vertices.
  [Width-cut criterion](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1537)
  · [Width-cut criterion after deletions](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1579).
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
  [Cutting between short-return runs](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1746)
  · [After removing long runs](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1802).
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
- For a fully bridge-free family of nonempty simple paths, let \(M\) be its
  incidence mass, \(n\) its vertex count, and \(J\) the total number of visits
  to strongly connected components of the precedence graph, counted once
  per path and component. For \(n\ge 2\), \(1\le p\le n^2\), and
  \(M\le C(n+J)\), a DAG on exactly \(n\) vertices with \(p\) distinct demands forces
  \(M\le 14C|E(H)|\) for every preserver \(H\). A component-wise linear
  bound suffices for this hypothesis. Applying that condition after
  opposite-intersection pruning gives factor \(28C\).
  [Component lower bounds](OnlineReachabilityPreservers/OfflineComponentOrders.lean#L240).
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
  bounds that mass by a linear term in each regime. The general extremal
  lower bound remains open between these regimes.
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
Theorem 43 for arbitrary simple paths, with the exact limiting exponent and a
constant that works for every vertex and path count.

Build from the repository root with `lake build OnlineReachabilityPreservers`.
The library is included in the repository's module index, declaration audit,
and kernel replay.

The companion PaperLab includes an interactive trace and a source-linked
proof map. The general extremal converse in Lemma 14 and the end-to-end
running-time proofs remain open.
[Companion PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site).
