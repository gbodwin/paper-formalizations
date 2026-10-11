# Native tree-packing equivalence: reciprocal component review

2026-10-11 17:28 UTC. Verdict: PASS for the exact three-source necessity/equivalence packet. Read-only review by the Greedy owner, with no child or compiler. The earlier sufficiency join was separately reviewed; this does not replace a fresh end-to-end audit of the entire Light EFT paper or every inherited proof. Owner strict112/root/index, 822-declaration audit and official kernel gates remain separate.

## Frozen binding
- NativePartitionLower.lean: 732a32e9e05a37f3b4ff21151c6eb07b21d0050645ef67d0169932982f9c1b88
- NativePackingNecessity.lean: 11bd2c694b8ad6867e61f0fbdffd54e9b9cb897745111b1f1f04f699b0c08ec5
- NativePackingEquivalence.lean: ac4a67024eaf4562c6fe6b76eda0222a91b6dfb39968396c38a0b4516dcb8d69

All 113 root/module manifest entries were independently rehashed, and all 109 prior proof files match parent 7047d2e08e31907242cb53ff3b706905643907e8 exactly. All three new files were read in full. Immediate quotient semantics, actual crossing identities and native connected-cardinality contracts were also inspected. Printed Theorem22 was read directly in sources/article.html, at the Thmtheorem22 section.

## Semantics

The connected-partition lower bound extends the labeling from actual vertices to ambient vertices using one actual vertex, provided by true connectedness. Surjectivity makes the actual quotient vertex set exactly Fin m; phantom ambient vertices add nothing. The quotient maps original links, discards internal edges and retains each crossing identity. Every connected original walk projects by deleting internal steps, so the quotient is connected even when individual label fibers are disconnected. The proof uses only the connected-graph edge lower bound on that quotient. It correctly avoids the stronger tree-quotient cardinality theorem, whose connected-fiber hypothesis would be invalid for an arbitrary partition.

The restriction identity is an exact equality of finite crossing-edge sets: retain precisely the original crossing identities in F. Graph restriction preserves the actual vertex domain, so the same surjective labeling is used for every member. Each connected spanning member therefore contributes at least m-1 crossings. Pairwise disjoint original edge sets make these finite crossing sets disjoint; card_biUnion converts their sum to a genuine union contained in the original crossing set. This proves k*(m-1) with no assumed numerical packing or accidental multiple counting of parallel identities. Necessity needs connectedness only, as the theorem explicitly says.

HasNativeTreePacking contains only actual subsets of G.edgeSet, native all-bridge and full-vertex connectedness conditions, and pairwise set disjointness. It does not encode the partition criterion or a maximality conclusion. Under the finite nonempty actual-vertex hypotheses, native all-bridge plus connectedness is the intended spanning-tree notion and excludes loops/parallel cycles. The forward iff direction extracts connectedness and disjointness. The reverse direction invokes the previously constructed native packing and forgets its separately proved exact cardinality certificate; no seed or desired packing is added as a premise.

## Printed scope and boundaries

This matches the finite nonempty-multigraph instance of printed Theorem22: k edge-disjoint spanning trees are equivalent to at least k*(number of occupied parts minus one) crossing edges for every vertex partition. Surjective labels over Fin m represent arbitrary finite partitions with nonempty parts, not just connected parts. The formal statement includes k=0 and singleton graphs consistently; m=0 has no labeling from the assumed nonempty vertex set. Its finite ambient-edge assumption and finite nonempty actual-vertex scope are explicit, rather than a claim for infinite graphs or an implicit empty-graph convention.

No semantic blocker or new correction of the printed theorem was found. This establishes the native finite tree-packing equivalence component. It does not by itself close the higher-level forest-packing sampling joins, the rest of the paper, or any algorithmic runtime claim.
