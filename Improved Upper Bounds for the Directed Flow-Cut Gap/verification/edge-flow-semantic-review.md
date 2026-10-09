# Semantic review: directed edge sum-multiflow duality

Draft reviewed 9 October 2026, 05:15–05:16 UTC; final frozen source reconciled 05:18 UTC. **No mathematical or domain defect found. Strict compilation is clean, all 35 owned declarations pass the recursive axiom audit, and isolated official kernel replay passes.** No Lean source was edited and no compiler was run by the reviewer.

Source: `repo/Improved Upper Bounds for the Directed Flow-Cut Gap/DirectedFlowCutGap/EdgeFlow.lean`.

Final reviewed SHA-256: `e91a1583f58c0ccbdfea379f56b3e40e8a94c04872f965e717f478c84bd57c6a`. The complete final diff from draft hash `c31be664010c2a4d7e642b032af2d924d64f1e51a61a8e2fbe4f3127618a50e6` was inspected: it adds only the source citation to the opening comment. No definition, theorem, or proof changed.

## Actual finite path and capacity semantics

Packing coordinates are the sigma type of a demanded ordered pair and an actual directed simple path between its endpoints. Finiteness is justified by the existing finite graph/simple-path model. A path consumes all consecutive edges, including edges incident to its endpoints. Since a simple path has no repeated vertices, its finite set of edges has no lost multiplicities. The objective is the sum of all path amounts across all commodities; there is no imposed common demand rate or concurrent-flow interpretation.

The graph capacity predicate constrains actual adjacent ordered pairs. The incidence LP has every ordered pair as a resource but masks capacities to zero on nonedges. A separately proved zero-load lemma shows that no path loads a nonedge, so this mask changes neither the graph feasible-flow set nor the intended objective. The exact covering objective is `weightedEdgeCost`, summed only over actual edges. Arbitrary input values assigned to nonedges have no effect. These facts prevent a spurious budget or capacity constraint from entering through the larger ambient coordinate type.

The path covering inequality is exactly the actual path's full edge weight, and the all-path covering predicate is equivalent to `IsFractionalEdgeCut` through the existing edge-distance characterization. No alternate artificial path family or externally postulated graph/LP equality is used.

## Feasibility domain and degenerate cases

A feasible fractional cut implies every demanded simple path has at least one edge, since an empty resource set has weight zero. Conversely, unit edge weights give a feasible fractional cut whenever all those resource sets are nonempty. The source proves this is equivalent to exclusion of every diagonal demand `(s,s)`. The empty self path exists even in graphs with self-loops; assigning large loop weights cannot make such a demand feasible.

Distinct adjacent demands remain permitted and consume their actual connecting edge. This is the correct distinction from the endpoint-excluding vertex-capacity model, where a directly adjacent path would consume no internal vertex. All unreachable pairs contribute no path coordinate and have vacuous covering constraints. The explicit empty-demand, unreachable-demand, and zero-capacity lemmas agree with these definitions; the zero-capacity flow-value claim correctly retains a feasible-cut hypothesis so that an unconstrained zero-edge self flow cannot invalidate it.

## Attained duality and correspondence

The strong theorem supplies an attained feasible maximum sum-multiflow and an attained feasible minimum fractional edge cut, with exactly equal objectives, comparison to every other feasible flow and fractional cut, and a minimizing cut bounded coordinatewise by one. It applies the existing finite incidence packing/covering strong-duality theorem after proving resource nonemptiness from a merely feasible initial cut. It does not assume an optimal witness, equality of optima, or a desired rounding factor.

The real-valued LP witnesses are transported back to nonnegative-real graph weights/flows using the actual nonnegativity constraints. Their feasibility, equality, and both optimality comparisons are transported through the exact previously proved bridge equalities. Capping the final fractional weights at one is a legitimate consequence of the finite covering theorem on nonempty resource sets.

This supplies the conventional finite path-based sum-multiflow/fractional-multicut equality described in arXiv:2604.03412v3, `tex/intro.tex:58`, and used by its edge-capacitated main claims. It remains an explicit finite simple-digraph and simple-path formulation. It does not separately formalize a transformation from arbitrary edge-variable commodity flows with circulations or parallel-edge multigraphs, and it makes no approximation, sampling, algorithmic runtime, or maximum-concurrent-flow claim.

## Independently inspected local verification

The final source hash was independently recomputed. `edge-flow-compile.log` is empty (SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`). The audit driver enumerates every declaration owned by `DirectedFlowCutGap.EdgeFlow`, rejects an empty enumeration, and recursively rejects axioms outside `propext`, `Classical.choice`, and `Quot.sound`. The audit log lists all 35 owned declarations and success, including the strong-duality theorem and both feasibility equivalences. Its SHA-256 is `dd170d4edd27653b71be0854befa04716891853ef193f2f7ea59396397a3ef3c`.

The replay driver calls official `LeanChecker.replayFromImports` on the exact target and prints PASS afterward. The resulting PASS log has SHA-256 `464b98fda178dfff95a2086b99b6f9276f2beb82a26e35ca353db6ed5316ec97`. This replays the target's kernel declarations with imported dependencies; it is not an independent proof checker or a fresh rebuild of the entire dependency closure in the isolated run.

This module is absent from the seventh aggregate manifest and was certified here through its own later frozen-source receipts. An enlarged source-bound aggregate remains a separate check. No remote Git publication or CI result is claimed.

## Eighth-checkpoint cross-check

At 05:34 UTC the full enlarged checkpoint completed. The reviewer independently matched all 53 source hashes, all 52 component imports plus root, all 53 unique official kernel-replay PASS targets, and the actual 2,854-declaration recursive allowed-axiom audit. The sources reviewed here are included and unchanged. See `eighth-independent-verification-review.md` for exact evidence hashes, fresh-build scope, count reconciliation, and local-versus-remote limitations.
