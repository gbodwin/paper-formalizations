# Eleventh component semantic review: forest components and real-eta rounding

**Verdict: PASS.** No semantic or frozen-source blockers were found in the four reviewed production modules. This is a bounded component review, not a final whole-paper audit or an unrestricted main-upper-theorem claim.

Reviewed on 2026-10-10 UTC against the actual production files and relevant upstream source contracts. No compiler or kernel checker was run by this reviewer; no proof source was edited, no child was created, and nothing was published externally. Only this requested report was written. `SubdivisionFaultProjection`, `PreserverWeightPositivity`, and the parked multigraph candidate were outside scope and were not reviewed.

## Frozen identity and supplied verification evidence

The production files under `repo/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/` were hashed directly. All four match `review/eleventh-source-hashes.json`:

| Module | SHA-256 |
| --- | --- |
| ForestComponents | `5d4d22c36c3b8545700f591700602d02f4b0d1f940f207e2e77eba9fd631918b` |
| ForestComponentPacking | `79e32b0c794467aeabdc7544eb10bc9c6d7ce3c6a21998b9167689a21dcc4edd` |
| SeededForestPacking | `9da10b4e4eafcc37cb77e6ea5484f058a0727d1c7e568efc9721ed031e14cc33` |
| RoundedCompetition | `344bb7275afca41f22190505c6cc95379143ed8224f60b24c1f83ecffe19b6bd` |

`verification/eleventh-build.log` records the four builds, the audit of 428 project declarations using only `propext`, `Classical.choice`, and `Quot.sound`, the successful import-index check, and `ELEVENTH_AGGREGATE_GATE_PASSED`. The inspected gate script builds the four modules with `autoImplicit=false` and warnings as errors, builds the root, runs the project axiom audit, and checks the import index. The root has 49 project imports, matching the 49 production module files. The axiom-audit source traverses project-module declarations and recursively checks their collected axioms against that allowlist; it is not merely an audit of selected public theorem names.

`verification/eleventh-replays.log` names all four modules and ends with `ELEVENTH_REPLAYS_PASSED`. The inspected replay script invokes the official `leanchecker` route for those targets. These are the supplied successful verification records, not additional builds or replays performed by this reviewer. The semantic assessment below is based on direct source inspection, not just these logs or prior review conclusions.

## 1. Native component trees and injective endpoint transport

`ForestComponents.lean:10–25` uses the native type `F.ConnectedComponent`, its actual vertex support, the subtype inclusion as an embedding, and `c.toSimpleGraph`. The inspected mathlib definition of `toSimpleGraph` is precisely the graph induced by the component support. Mathlib's `IsAcyclic.isTree_connectedComponent` proves connectedness and acyclicity on that local vertex type. Thus these are genuine component trees, not spanning trees on the entire original vertex type and not a custom graph predicate. The inclusion is injective by construction, and the mapped graph lies in the original forest.

The mapped adjacency equivalence at lines 23–25 is correct despite mentioning only membership of the first endpoint explicitly: actual adjacency supplies membership of the second endpoint in the same connected component. Its actual mathlib implementation was inspected. `component_edge_unique` at lines 28–36 then extracts a common actual endpoint and identifies both native component classes. It applies to actual unordered edge membership, so there is no orientation factor or duplicated component charge. A diagonal unordered pair cannot satisfy these actual simple-graph edge premises.

By contrast, `component_pair_preimage` at lines 40–50 intentionally concerns all unordered endpoint pairs. It proves that a local preimage exists exactly when both actual endpoints lie in the same component support, using the two possible equalities of unordered pairs. This includes the diagonal case correctly. It does not confuse joint endpoint membership with mere intersection with a host domain. `reachable_component_pair` at lines 53–56 selects the actual component of the first endpoint and uses reachability to put the second endpoint in it.

There is no hidden nonempty global vertex assumption. Native connected components have nonempty support; when the global vertex type is empty there are no such components. Finite component indexing comes from the inspected native quotient `Fintype` instance. Singleton components and empty candidate sets are permitted by the downstream transport theorem; nonempty candidates establish the local order lower bound needed for per-host sampling.

## 2. Actual sigma indexing, congestion, and connected endpoint counts

`ForestComponentPacking.lean:9–13` constructs the actual finite sigma collection of all connected components of every supplied forest index. The index type `I` itself need not be finite; the given `Finset I` is sufficient. Equal forest graphs at distinct supplied indices remain distinct indexed hosts, as required for honest multiplicity counting.

For each fixed actual unordered edge, the proof at lines 17–39 projects component-tree hosts to their original forest indices. Mapping into forest hosts follows from actual subgraph inclusion. Injectivity on the edge's host set follows from `component_edge_unique` after equality of the forest indices. Consequently splitting a forest into all its component trees cannot increase that edge's congestion. The result is proved for every unordered pair; diagonal pairs simply have no edge hosts.

The injection at lines 44–54 sends each forest that actually connects the two endpoints to its canonical component containing the first endpoint. Reachability supplies the joint-endpoint preimage, and the sigma first projection proves injectivity. Thus the target count is an actual joint-endpoint component count, not a total forest count substituted without a connectivity argument.

At lines 59–95, the family passed to `subtree_packing_lightness` has exactly these local vertex types, inclusions, and induced component trees. Acyclicity and containment in `Q` come from the supplied forest premises; endpoint coverage and congestion come from the two proved injections. Membership of an actual edge in `G.edgeFinset \\ Q.edgeFinset` is explicitly converted to adjacency in `G` and nonadjacency in `Q` before applying the forest count premise.

The actual upstream `SubtreeAssignments`, `SubtreeHostFamily`, `HostWeightTransport`, `InducedHostSampling`, and relevant `HostGraphSampling`/`HostCounting` contracts were inspected. They use injective unordered-edge transport and exact weight sums; assignments are actual non-seed edges whose original blockers avoid the mapped tree. Congestion two removes at most `2*f` eligible hosts. Weighted incidence aggregates the genuine candidate and tree-edge multiplicities; the supplied per-host sampling theorem contributes `4*f*L`, and tree congestion contributes two. The seed/non-seed weight split retains the baseline one. No final global weight inequality is an input to the forest reduction. The result is the conditional bound `1 + 8*f*L/h`, where `L = 8 + 2048/eps * |V|^(1/k)`.

## 3. Genuine optimum seed, native missing-edge connectivity, and the same output

`SeededForestPacking.lean:14–25` assumes the actual `IsMinimumFTPreserver G Q w q`. Its upstream definition includes both fault-connectivity preservation and minimum total weight among all such preservers. The proof does not need its minimization clause, but the theorem is genuinely about an optimum seed; the hypothesis is not a renamed arbitrary seed or an assumed lightness conclusion.

The inspected native definition `Q.IsEdgeReachable (q+1) a b` means that the endpoints remain reachable after deleting every set of strictly fewer than `q+1` edges. `MissingEdgeConnectivity.missing_edge_edgeReachable` converts such a finite cut set to a finset of cardinality at most `q`, then invokes actual fault-preserver semantics. Its upstream `missing_edge_connected` handles fault sets that include the missing input edge by erasing that edge from the input fault set: it is absent from `Q`, so this does not change the failed preserver. This supplies native cut-set connectivity, not an assumed path-packing conclusion.

At lines 43–50, an edge of the actual output outside `Q` is first mapped back to an input edge through `output ≤ G`. Native `(q+1)`-edge reachability is then derived from that same seed. The supplied `hconn` makes every supplied forest connect those endpoints, so the filter is proved equal to the original index finset. The required count follows from the explicit inequalities `2*f+h ≤ q+1 ≤ indices.card`. Thus forest connectivity is used to justify actual endpoint coverage rather than being replaced by the bare number of forests.

The inspected `output` is the actual seeded recursive edge insertion procedure processing the input edges outside `Q`; `output_isEFTSpanner` proves its EFT property and containment in `G`, and `seed_le_output` proves retention of `Q`. At lines 40–42, `output_has_blocking` produces the blocker map for this exact output, seed, weights, stretch, and fault budget. The forest theorem is applied to that same output. Positivity of original input-edge weights is restricted to output edges through the same containment. There is no substitution of an unrelated graph or abstract blocking oracle.

The global nonnegativity, input-edge strict positivity, and positive `f`, `k`, `eps`, and `h` hypotheses remain explicit. Lines 33–39 retain the preexisting denominator convention: `competitiveLightness` is real division, and the zero-seed-weight branch uses Lean's `x/0 = 0`. In the nonzero branch, nonnegative seed weight implies strict positivity before ratio charging. This does not establish a positive denominator in all cases and must not be presented as doing so.

## 4. Exact rounded budget and uniform finite coefficient

`RoundedCompetition.lean:8–12` proves

`floor_nat((2+eta)*f) = 2*f + floor_nat(eta*f)`

for every natural `f` and nonnegative real `eta`. The real expression is rewritten as `eta*f` plus the cast of the natural number `2*f`. The actual `Nat.floor_add_natCast` contract requires nonnegativity of the real summand, which follows from the stated assumptions. This is an exact natural-floor identity, including `f=0` and `eta=0`, not an asymptotic replacement of the competition budget.

At lines 16–25, `h = floor_nat(eta*f)+1` is a positive natural integer. The proof uses the actual strict inequality `eta*f < floor_nat(eta*f)+1`, scales by nonnegative `8*L`, and cross-multiplies only after proving that both denominators are positive. This yields `1 + 8*f*L/h ≤ 1 + 8*L/eta` for `eta>0` and `L≥0`. The casts are explicit at the cross-multiplication step. The lemma covers `f=0` and `L=0` as well. There is no `eta≤1`, `eta≤2`, or other upper restriction, and the baseline one is preserved rather than absorbed into an unjustified coefficient.

The joined theorem at lines 33–55 retains the genuine optimum seed at the original exact budget `floor_nat((2+eta)*f)`. Its tree-family premise explicitly requires that budget plus one joint-endpoint hosts for every input non-seed edge. The exact floor identity converts this into `2*f + (floor_nat(eta*f)+1)` integer votes. It invokes the existing actual-output subtree theorem with precisely that positive `h`, then applies the scalar inequality with the nonnegative actual coefficient `L`. Thus the conclusion concerns the same actual greedy output and gives the stated conditional `1 + 8*L/eta` bound for every positive real `eta`.

## Scope boundary and remaining obligations

The family of forests, their acyclicity, containment, connectivity preservation, number, and congestion are supplied structural premises. The rounded theorem likewise assumes its actual embedded subtree family, endpoint coverage at the exact rounded budget, and congestion. Neither theorem derives forest or subtree packing existence from the fault budget alone. These premises are graph structure and finite incidence requirements, not disguised final lightness inequalities.

This PASS closes the reviewed component reduction and rounding check only. The Eulerian multigraph forest-packing existence theorem, optimized heavy/light sampling, Theorem 34 replacement certificate, runtime, and the fresh root-owned whole-paper final audit remain outside what is established here. No unrestricted upper theorem or whole-paper completion follows from this report.
