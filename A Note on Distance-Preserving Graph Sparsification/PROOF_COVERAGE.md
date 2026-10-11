# Proof coverage

Certified checkpoint: `2c4f35bc73c7787945a0f781ba06164d75fbfaee`.
A compiled supporting lemma is not treated as a proof of an application theorem.

| Paper component | Lean declarations | Certified scope |
| --- | --- | --- |
| Main Lemma 1 | `complete_of_slack`, `overhead_pos` | Complete finite quantitative theorem. Constructs the edge union, proves termination and the geometric bound from precisely the small/slack premises. |
| Simultaneous sample selection | `exists_joint_sample` | Finite weighted distributions; produces one witness satisfying both coverage and cost. Positive cost/coverage parameters are explicit. |
| Definition 1 | `IsAdditiveSpanner`, `IsReachabilityPreserver`, `zero_additive_iff`, `infinite_additive_vacuous` | Actual unweighted graphs with extended natural distances; unreachable demands are distinguished correctly. |
| Hitting step | `exists_half_hitting_set` | Constructs a set of size at most floor(2n/d)+1 hitting half the demands with neighborhoods of size at least d. Deterministic replacement of random sampling. |
| d-initialization | `exists_initialization` | Constructs an actual subgraph with ≤nd edges; every endpoint of a missing original edge has initialized degree ≥d. |
| Lemma 6 | `path_neighborhood_count` | Actual shortest walks: d times the number of selected missing-edge source indices is at most three times the neighbor-union size. The initialization theorem supplies the degree premise. |
| Shortest-path tree | `exists_shortest_path_tree` | Constructs an actual ≤n-edge root-distance preserver, including disconnected graphs. Reuses the already verified parent-tree construction from the distance-preserver library. |
| Missing-path purchase | `missing_edges_card_le`, `captured_path_distance`, `shortest_split` | Actual graph edges and exact extended distances. |
| Theorem 8 construction | `exists_plus_two_slack_paths` | Actual graph satisfying ≥half the indexed shortest-path demands; cost ≤3nd+pm+n(floor(2n/[d(m+1)])+1). |
| Theorem 8 parameters | `plus_two_integer_budget`, `exists_cube_parameter` | At p≤k³, d=k, m=floor(n/k²), cost ≤7nk. Rounded k≤2p^(1/3), including m=0. |
| Theorem 7 | `PlusTwoComplete.lean` | Complete actual graph theorem: ≤ [14/(1−(1/2)^(1/3))] n p^(1/3) edges, including disconnected graphs and empty demands. |
| Theorem 12 local correction | `CorrectionExample.printed_equality_fails` | A seven-vertex unweighted G and subgraph H where the asserted equality fails despite shortest-path placement in G. |
| +4/+6 algebra | `plus_four_route`, `plus_six_route` | Arithmetic support only. Does not assume or assert existence of the claimed spanners. |
| Theorems 3–4, 5.1, 9, 11, 12 | — | Full graph-level applications remain open. |
| Cited Theorems 5.2 and 10 | — | Prior results cited by the paper; not silently introduced as Lean axioms. |

The +2 construction quantifies over arbitrary indexed actual shortest walks,
not a supplied successful sample or supplied spanner. The certified complete wrapper chooses
those walks from reachable demand pairs and makes the analytic edge bound and
full amplification explicit.
