# Semantic review: directed edge-to-vertex reduction

Reviewed 9 October 2026, approximately 04:54–04:57 UTC, against arXiv:2604.03412v3 Theorem 30, `sources/2604.03412v3/tex/reductions.tex:398–434,553–595`.

**No mathematical defect was found in the inspected construction or theorem statements.** The first pass reviewed an uncompiled draft. At 05:01 UTC, the final compiled source was compared to that exact saved draft and its dedicated verification artifacts were inspected. Changes were proof/elaboration repairs and removal of unnecessary typeclass assumptions; construction and substantive conclusions remained unchanged. No Lean source was edited and no compiler was run by this reviewer. The conditional oracle reduction is not an unconditional proof of the paper's headline theorem.

The complete initial draft `EdgeToVertexReduction.lean` and its `DyadicEdgeWeights.lean` dependency were read. The review also used the actual edge/path/cut semantics inspected in `new-foundations-semantic-review.md`. Final reviewed hashes, relative to `repo/Improved Upper Bounds for the Directed Flow-Cut Gap/DirectedFlowCutGap/`, are:

| File | SHA-256 |
| --- | --- |
| `EdgeToVertexReduction.lean` | `1d7bd95d3aba569f18fbbcd2cff7a502c44b5cd0de19a1aabcc8b4abcd91caa3` |
| `DyadicEdgeWeights.lean` | `7efe080ef97003b2586c0820719ba1e9b9e1cd57a7b55bb6ed58daa3c798f94d` |

The initial graph-module draft hash was `f9ff4fb4b2a605e5850f885729c67622955fed5886919d56a15475e5489e0d02`. The final `edge-to-vertex-compile.log` is empty, `edge-to-vertex-axiom-audit.log` reports all **122** owned declarations passed with only `propext`, `Classical.choice`, and `Quot.sound` allowed, and `edge-to-vertex-kernel-replay.log` reports PASS. The audit driver and replay invocation were inspected. This is local evidence from the owner's run, independently reviewed rather than rerun; it does not assert remote publication or external CI.

At 05:05 UTC the final DyadicEdgeWeights hash was independently rechecked and remained the value in the table. Its dedicated compilation log is empty, its exhaustive owned-declaration audit reports **65** declarations passed under the same allowed axioms, and its official kernel-replay log reports PASS. The complete dyadic source was already inspected in this review; no later semantic or proof-source change was present in this dependency.

## Construction and finite parameters

The actual gadget type is the subtype of active raw nodes: two endpoint ports per original vertex, and only left/right label vertices incident to a mapped original edge. Merely assigning zero cost to inactive vertices is not being substituted for deleting them. A mapped edge joins its tail's right label to its head's left label; biclique arcs go from an incoming left label to an outgoing right label at the same original vertex. No reverse/symmetric adjacency is assumed.

The one addition to the printed gadget is the zero-cost, zero-weight arc from each start port to its own finish port. It represents the original empty walk. Start ports have no incoming arcs and finish ports have no outgoing arcs, so this addition cannot create a shortcut between distinct original vertices. It also ensures that a self-demand cannot become artificially separated by treating the two gadget ports as an originally nonempty route.

The dyadic labels are zero and `2^(-i)` for `0≤i≤floor(log₂ n)+1`, with `n=0` assigned zero by the rounding function. The extra bottom bin removes the source's power-of-two assumption. The finite selector drops weights at most `1/(2n)`, rounds intermediate weights upward, and clips weights at least one to one. The inspected arithmetic proves the factor-two upper bound and the additive light-edge loss bound only in their appropriate domains. It does not falsely claim that clipping dominates raw weights above one.

The cardinality is at most `2n(log₂ n+4)`. Each active label's weight can be charged to at least one incident mapped edge, giving gadget total weight at most twice the rounded original total and hence at most `4W`. Each original edge contributes its cost to both mapped endpoint labels; exact incidence summation yields gadget weighted cost equal to twice the original objective with rounded weights, hence at most four times the original objective. Zero costs and self-loops cause no double-counting defect: the left/right tags are distinct even at the same original base vertex. Pullback counts an original edge once even if both labels are selected, so its cost is at most the selected gadget-node cost.

## Arbitrary-path projection and threshold transfer

The critical reverse direction is present: it considers every actual gadget path between the relevant endpoint ports, not only canonical lifts of original paths. Each gadget arc either stays over one original vertex or is exactly a mapped original edge. Before extracting the original path, the proof restricts the original graph to edges whose two label vertices occur internally on that gadget path. Projecting an actual gadget walk and erasing loops in this restricted graph therefore supplies a genuine original simple path whose edges all have both labels represented. The method preserves edge support and does not infer it merely from vertex support.

Distinct original simple-path edges have distinct tails and distinct heads. Their right labels are consequently distinct, their left labels are distinct, and the right and left sets are disjoint. All those labels occur internally in the gadget path. This justifies the factor-two lower bound on gadget path weight even though different graph edges elsewhere may share a label vertex. Repeated visits in the initially projected walk are harmless because erasure precedes this injective counting argument.

Threshold transfer splits correctly at a weight-one edge. A retained heavy edge alone supplies rounded weight one. If every edge is below one, each loses at most `1/(2n)`; an original simple path has fewer than `n` edges, so the total loss is at most one half. The gadget's two labels per retained edge restore weight at least one. The printed source's raw-weight domination sentence is not valid for clipped weights above one; this separate heavy branch resolves that issue. Checking arbitrary gadget paths also makes explicit the projection obligation left implicit by the source's discussion of lifted paths.

## Endpoint-safe cut pullback and conclusion

An original walk avoiding the pulled-back edge cut is lifted through actual gadget arcs while retaining the two demand ports in the vertex-deleted graph. Every mapped label on that lift is outside the selected gadget set by the definition of pullback. The construction includes original empty walks and works with repeated vertices/edges. Endpoint-retaining loop erasure then contradicts a gadget internal-vertex cut. Thus selecting either demand port cannot falsely certify separation of the original demand. No requirement that original demand endpoints remain unselected is smuggled into the proof.

`round_of_bounded_vertex_oracle` applies an explicit vertex-rounding oracle to the actual constructed gadget. Its premise covers every finite graph with at most `2n(log₂ n+4)` vertices and total weight at most `4W`, for arbitrary nonnegative costs and weights. The conclusion supplies a subset of actual original edges cutting any originally feasible demand family, at cost at most `4α` times the original fractional objective. The implicit threshold-family specialization is also supplied.

The oracle is a substantive and plainly stated premise of this reduction. It is not constructed here, and no monotonicity of a gap defined at exact parameters is assumed. The empty graph, zero weights/costs, disconnected demands, and self-demands are compatible with the definitions. This is a relation-graph reduction; separately identified parallel edges are outside its domain. Proving the oracle from the vertex bound, any asymptotic gap-function packaging, and implementation/runtime remain separate. The dedicated local compilation/audit/replay results above cover the final graph module; its integration into later aggregate releases requires their own recorded source-bound checks.

## Seventh-checkpoint cross-check

At 05:14–05:15 UTC, the reviewer independently reconciled all 42 source hashes, all 41 component imports plus root, all 42 unique official kernel-replay PASS targets, and the 2,574-declaration recursive allowed-axiom audit. All sources reviewed here are included and unchanged. See `seventh-independent-verification-review.md` for exact evidence hashes, fresh-build scope, and local-versus-remote limitations.
