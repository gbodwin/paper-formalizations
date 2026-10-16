# Proof coverage and combined integration scope

This integration imports all 49 `SlackSparsification` leaves and their three
`LinearDistancePreservers` support leaves. The combined gate compiles the 52-leaf
source-derived union and aggregate, individually replays all 52 leaves, and audits
the recursive type/body closure of every declaration actually owned by those
modules. Its result is pending the new exact-source CI and independent review.
Earlier incremental acceptance is source/log/hash reconciliation, not a fresh
execution or a claim that this combined gate has already passed.

The table uses the numbering in the preserved arXiv:2001.07741v3 source.
Names without a prefix are in `SlackSparsification`; `Directed.*` and
`SubsetPlusTwo.*` are subnamespaces. Bounds below are explicit inequalities,
not a separate formalization of asymptotic notation. Write n = |V| and p = |P|.

| Paper statement | Actual endpoint / module | Scope and assumptions |
| --- | --- | --- |
| Main Lemma 1 | `complete_of_slack`, `overhead_pos` / Amplification | Finite demand and edge sets; explicit monotone satisfaction, small-instance and slack-constructor hypotheses, nonnegative costs and geometric decay hypotheses. The application endpoints below discharge their construction hypotheses. |
| Informal Theorem 2, distance item; Theorem 3 | `Directed.exists_exact_input_preserver` / DirectedPreserver | Finite V, ambient simple graph K, arbitrary directed allowed relation A, finite nonnegative real weights (zero allowed), finite ordered demands. Actual input arcs; exact extended distance including unreachable pairs. Bound 14 n sqrt(p)/(1-sqrt(1/2)). |
| Theorem 4 (distance with slack) | `Directed.exists_exact_slack_rpow_paths` / DirectedComplete; `Directed.exists_exact_slack_paths` / DirectedExact | Indexed actual minimum-weight allowed paths; positive demand count in the parameter wrapper. Half of indexed demands satisfied, bound 14 n sqrt(p). Theorem 3 wrapper constructs paths for reachable demands and handles unreachable/empty cases. |
| Informal Theorem 2, reachability item; Theorem 5.1 | `Directed.exists_reachability_preserver` / SCCInternal | Arbitrary finite orientation supported by K, actual input arcs, no sourcewise/DAG/connector premise. Bound 8n + 25 n^(2/3) p^(2/3)/(1-(1/2)^(2/3)). Empty inputs and unreachable demands included. |
| Cited Theorem 5.2, corrected reachability reading | `Directed.sourcewise_bound_uniform`, `Directed.bidirectional_sourcewise_uniform` / SCCInternal | `SourcewiseBound K A 4` for arbitrary orientations and reversal. Ordered demands contained in S × V; bound 4(sqrt(n p |S|)+n). SCC internal connectors total at most 2n original arcs. This proves reachability, not the printed stronger distance wording. |
| Lemma 6 | `path_neighborhood_count` / Neighborhoods | Actual shortest walk, selected missing-edge source indices and degree d supplied by `exists_initialization`; d times the selected count ≤ three times the neighbor-union count. |
| Informal Theorem 2, +2 item; Theorem 7 | `exists_plus_two_complete` / PlusTwoComplete | Finite undirected unweighted simple graph, arbitrary finite ordered demands; actual subgraph, extended additive distance. Bound 14 n p^(1/3)/(1-(1/2)^(1/3)); empty and disconnected inputs included. |
| Theorem 8 (+2 slack) | `exists_plus_two_slack_paths` / PlusTwo; `exists_plus_two_slack_rpow_paths` / PlusTwoComplete | Indexed shortest walks; parameter wrapper assumes positive demand count. At least half satisfied, cost ≤14 n p^(1/3); complete wrapper removes supplied-path premise. |
| Informal Theorem 2, +6 item; Theorem 9 | `exists_plus_six_complete_unconditional` / PlusSixIntegration | Actual additive +6 subgraph, bound 106 n p^(1/4)/(1-(3/4)^(1/4)). Uniform subset +2 premise discharged at C=16; finite empty/disconnected inputs included. |
| Cited Theorem 10 (subset +2; CGK13 Theorem 3) | `SubsetPlusTwo.uniform_subset_plus_two` / SubsetPlusTwoFold | `UniformSubsetPlusTwo G 16`: for each finite S, an actual subset +2 subgraph with ≤16 n sqrt(|S|) edges. Clustering, path buying, charging, diagonal cases and integer optimization constructed. No supplied clustering/purchase premise remains. |
| Theorem 11 (+6 slack) | `exists_plus_six_slack_rpow_paths` / PlusSixComplete | Indexed shortest walks and uniform subset +2 contract; instantiate with the proved `SubsetPlusTwo.uniform_subset_plus_two G` at 16. Quarter coverage and bound 106 n p^(1/4); complete unconditional wrapper removes path and subset premises. |
| Theorem 12 (+4 slack) | `exists_plus_four_slack_rpow_paths` / PlusFourComplete | Indexed shortest walks, positive demand count; at least 1/12 coverage and cost ≤176 n p^(2/7). Constructed prefix/suffix routing handles overlap and integer thresholds. |
| Informal Theorem 2, +4 item (amplified Theorem 12) | `exists_plus_four_complete` / PlusFourComplete | Actual additive +4 subgraph, bound 176 n p^(2/7)/(1-(11/12)^(2/7)); empty/disconnected inputs included. |

The indexed slack wrappers also use a nonempty finite vertex type and decidable
index equality; the final complete endpoints remove nonemptiness and supplied
paths. SourcewiseBound states allowed-arc containment and forward reachability;
`Directed.sourcewise_input` filters to actual ambient input arcs without increasing
cost, and input containment gives the reverse implication.

## Supporting constructions and model boundaries

`exists_half_hitting_set` gives deterministic half coverage; `exists_joint_sample`
is a separate finite simultaneous cost/coverage lemma. `exists_initialization`,
shortest-path/root preservers, actual missing-path purchases and finite folds
construct the witnesses used by the endpoints. `Directed.exists_root_preserver`
is used with zero weights on each SCC subtype; preserved finite distance gives
allowed reachability. The SCC fiber identity sums component cardinalities to n.

Additive results use extended natural graph distance. Reachability is a separate
predicate: substituting infinity into an additive inequality would be vacuous.
Directed results use finite vertex types and loopless ordered input arcs supported
by an ambient simple graph; both orientations of an edge may be allowed. Weights
are finite nonnegative reals. Negative weights, arbitrary parallel-edge models,
self-loop normalization, infinite graphs, algorithmic runtime and computational
complexity are outside this scope. No endpoint claims those extensions. The
paper's informal assertion of proof simplicity is not a formal theorem.

## Corrections, not stronger claims

Theorem 12's displayed H-distance equality is genuinely false:
`CorrectionExample.printed_equality_fails` certifies the seven-vertex witness.
Triangle inequality repairs the proof; this is not a counterexample to the final
+4 bound. Separately, Theorem 5.2 calls the cited AB18 reachability result a
"distance preserver." The original cited source states reachability. This is a
citation/type correction, not a counterexample to the stronger distance claim.
The original v3 retraction of an earlier +4 all-pairs claim remains outside the
accepted result set. Original paper source and all prior proofs/evidence remain
preserved. No websites are changed by this integration.

## Validation boundary

The exact integration source and CI trigger are recorded in
`checkpoints/combined-integration-20261016/REPORT.md` after freezing and execution.
The new gate uses the official Lean 4.34.0 release archive, unchanged nine pinned
dependencies, clean outputs, sequential compilation and singleton kernel replay,
and an actual-owner recursive audit allowing only `propext`, `Classical.choice`
and `Quot.sound`. Raw warnings must match reviewed baselines; warning totals count
anchored diagnostic headers, not occurrences of the word "warning" in hints.
All compiler/checker invocations have unique source-bound lock/PID/timing receipts.

Historical directed local execution had a sequencing/receipt gap, retained in
its original evidence. The accepted directed CI closed that fresh-execution gap;
it did not rewrite history. The present combined gate is a new validation of the
union, and does not by itself assert whole-paper acceptance or completion.
