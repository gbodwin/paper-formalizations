# Semantic review: finite vertex-to-edge splitting

Reviewed 9 October 2026, 05:05 UTC, against arXiv:2604.03412v3 Theorem 31, `tex/reductions.tex:597–620`.

**No mathematical or specification defect found in the frozen `VertexToEdgeReduction.lean`.** The module constructs the actual split graph, proves its path/metric/cut bridges and exact parameters, and derives a conditional vertex-rounding theorem from an explicitly bounded edge-rounding oracle. It does not assert the main asymptotic theorem, construct that oracle, or prove runtime.

The reviewer read the entire source and inspected its dedicated verification drivers/logs. No Lean source was edited and no compiler or kernel process was run by the reviewer. Exact source SHA-256, rechecked after inspection: `13f8025a0196521f8b2e1b24dfef07223994953bf879dc63538d05741e6725ca`, at `repo/Improved Upper Bounds for the Directed Flow-Cut Gap/DirectedFlowCutGap/VertexToEdgeReduction.lean`.

## Actual graph and parameters

The vertex type is the disjoint sum `V ⊕ V`, giving exactly `2n` vertices. Each original vertex has one input-to-output split arc, carrying its original weight and cost. Each original adjacency supplies an output-to-input connector, with weight zero and cost `M`. There are no other adjacencies. Tagged endpoints distinguish a split arc from a connector even when the original graph has a self-loop. Both arc maps are injective. Values assigned to nonedges are harmless because the edge objectives explicitly sum only over actual adjacent pairs.

The total fractional edge weight is exactly the original total vertex weight `W`; the fractional weighted objective is exactly the original `C=Σc(v)w(v)`, independently of `M`. Zero connector weights are multiplied only by finite costs, so no `0*∞` issue arises. Empty vertex types and arbitrary finite nonnegative costs/weights, including zeros, are covered.

## Genuine path projection and lift

The demand represented by original `(s,t)` is `(output s,input t)`. A lifted nonempty original path traverses only the split arcs of its internal vertices, with exactly their original total weight; the source and target split arcs are omitted. The indexed internal-sequence lemma uses injectivity to identify precisely positions `1,…,edgeLength−1`.

In reverse, `project_walk` contracts split arcs and turns each connector into its actual original adjacency. It proves that every visited original vertex has traversed its split arc, except possibly an exposed output source or input target. Before projecting a gadget simple path, a walk with edge support contained in that path is constructed by restricting adjacency. Original loop erasure then preserves vertex support. Every internal vertex of the final original simple path therefore has its split arc in the original gadget path. Injectivity of the split-arc map and nonnegative summation prove that projected internal weight is no greater than gadget edge weight.

These two directions establish exact extended-distance equality for **distinct original endpoints**. Both disconnected distances are handled by the existing infimum/all-path semantics. The restriction is correct and necessary: original self-distance is zero, but distance from `output s` to `input s` can be positive or infinite without an original self-loop. The module does not claim the false self-demand metric equality. Its final application proves that every original threshold-one demand has distinct endpoints before invoking the bridge.

## Finite connector exclusion and exact cuts

The connector exclusion lemma assumes an allowed budget `B` and chooses `M>B`. Any selected actual connector alone contributes `M` to the actual edge-cut cost, contradicting the budget. This is derived from a finite sum, not assumed as a property of the returned cut. In the final theorem, `B=αC` and `M=αC+1`, so the strict inequality holds even when `α=0` or `C=0`.

After excluding actual connectors, filtering the selected edge set to actual graph edges produces exactly the split arcs of `pullCut X`. Thus the pulled-back vertex cost equals the selected edge cost, even if the syntactic edge set also contains nonedges. A selected original vertex is defined exactly by membership of its split arc.

For distinct demands, an original simple path is lifted and then edge-preservingly erased to a gadget simple path. An edge cut must hit this path; connector exclusion forces that hit to be an internal original vertex's split arc. This proves the forward cut pullback without mistakenly counting either endpoint. The reverse implication uses the projected original path and its internal split-arc certificate. Together they give the claimed cut equivalence under the explicit distinctness and connector-exclusion assumptions.

## Oracle scope, quantifiers, and source correspondence

`BoundedEdgeRoundingOracle` quantifies over actual finite graphs with vertex count at most `2n`, edge mass at most `W`, and **all** finite nonnegative cost functions. Consequently applying it after setting connector cost `αC+1` is legitimate: `C` does not depend on connector costs, and `α` is fixed before selecting that cost function. There is no circular budget definition or unknown final cut cost in `M`.

The final theorem applies this oracle to the concrete split graph, obtains a cut of every split-graph threshold demand, excludes connectors, and returns a cut of every original vertex threshold demand at cost at most `αC`. The `HasVertexRoundingFactor` corollary keeps the same bounded edge oracle and factor for all original costs. No monotonicity of a gap defined at exact parameters is presumed.

This implements the source's split-node construction and replaces its unspecified sufficiently large connector costs by an explicit finite value. It also supplies the demand-endpoint convention and both metric/cut directions omitted from the brief printed proof. The graph model is directed adjacency on ordered pairs; separately identified parallel edges are outside its scope.

## Inspected verification evidence

`vertex-to-edge-compile.log` is empty. The all-owned-declaration driver recursively audits axiom dependencies, allowing only `propext`, `Classical.choice`, and `Quot.sound`; its log reports **117** declarations passed. The dedicated official `LeanChecker.replayFromImports` driver and log report PASS for `DirectedFlowCutGap.VertexToEdgeReduction`. These are local results from the implementation worker, inspected rather than rerun by the reviewer. They do not imply remote publication, remote CI, or fresh rechecking of every dependency. The exact source hash above matches the worker's frozen result. Later aggregate releases should retain their own source-bound verification record.

## Seventh-checkpoint cross-check

At 05:14–05:15 UTC, the reviewer independently reconciled all 42 source hashes, all 41 component imports plus root, all 42 unique official kernel-replay PASS targets, and the 2,574-declaration recursive allowed-axiom audit. All sources reviewed here are included and unchanged. See `seventh-independent-verification-review.md` for exact evidence hashes, fresh-build scope, and local-versus-remote limitations.
