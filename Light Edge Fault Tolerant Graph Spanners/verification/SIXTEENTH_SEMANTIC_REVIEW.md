# Sixteenth bounded semantic/source review

Date: 2026-10-11 UTC.
Verdict: **COMPONENT PASS for the six frozen foundations below. No semantic blocker found within this scope.** This is not a proof or final audit of general tree packing or the paper's main upper bounds.

## Scope and evidence

Reviewed all 415 lines of these six production sources, their relevant previously reviewed native graph dependencies, Mathlib's native restriction/projection definitions, the refinement/forest proof interfaces, and the pinned Kaiser source. No proof-source changes, publishing, compiler invocations, or kernel replays were performed by this reviewer. Build/replay conclusions below are independently inspected recorded evidence, not newly executed checks.

The supplied published proof checkpoint is `9b2a722589b4484ccacb897f0357be1dd07cc3b2`. Its local Git object, working sources, review manifest, and committed production manifest agree exactly:

| Module | SHA-256 |
|---|---|
| NativePartitionCriterion | 3f154f0599ccd80a54a1c5632d85d6a7ec630f32578337bf4a3d2cb279f33dd7 |
| NativeBlockRefinement | 88d722789c37306c30847d178143b41e36c773636d151cfa9b78e7d2c0cc34ca |
| FinitePartitionRefinement | 836d7ee5e691d3ea1f4faa621c6753e3058dc214e25420fca2df6f32f15e07fc |
| PartitionRefinementTermination | f0d4ec7a357e1a4b2f3550f36bbbdb8e7324b0f8a8d067c3ded45a8c14e6fff7 |
| NativeExchangeConnectivity | 2338e245a001de0f3734a38ef58dd1811549d337aa51b371909965c16135c890 |
| NativeForestDensity | d9dd14a066d55dacd6962725af9f241db9b4884185178d3e94820c8a3737757d |

All 72 production module files present at reviewed baseline `f8ed484cb46e01e6d71262ae804310eb228c11a0` are byte-identical at this checkpoint and in the working tree. The production module directory contains exactly 78 Lean modules, and the root imports exactly those 78, without omissions or duplicates. The proof-source diff from the baseline adds only the six reviewed files and six root imports. The repository was clean during inspection. Prior semantic reviews are inherited through byte equality, not claimed to have been repeated here.

The committed build logs equal the local gate logs. `sixteenth-build-a.log` records three successful strict builds; `sixteenth-build-b.log` records the remaining three, aggregate/index success, and a 631-declaration audit allowing only `propext`, `Classical.choice`, and `Quot.sound`. The inspected scripts use `-DwarningAsError=true` for each new module; the Lean wrapper additionally uses `-DautoImplicit=false`. The audit traverses declarations belonging to project modules and collects their transitive axioms. No added custom axiom, placeholder proof, unsafe declaration, or implementation override appears in these six sources.

The committed two replay logs record successful official `leanchecker` replay for all six modules and match the local records. The second local successful log is named `verification/sixteenth-replay-b.log` (singular), while the committed copy is `verification/sixteenth-replays-b.log`; an empty plural-named local staging log is not the successful evidence. This naming distinction is resolved, not a failed gate.

Exact CI run `38096551852` was reported running in the handoff. This review does not independently refresh remote publication or CI status and does not certify CI success. It verifies the supplied checkpoint's local Git contents and corresponding evidence. CI remains a separate gate.

## Semantic findings

### 1. Actual partitions and one-tree sufficiency

`actualPartitionCrossings` filters original identities in `E`, using actual endpoint subtypes `G.vertexSet`. Nonedges cannot satisfy `IsLink`; loops cannot have different labels; distinct parallel identities remain distinct counted elements. Surjectivity into `Fin m` excludes unoccupied blocks. The two-side equality identifies the resulting finite crossing set with the genuine native cut, including both possible endpoint orientations.

`partitionCriterion_faultConnected` supplies an actual surjective two-block labeling from a separating pair and invokes the previously established cut/reachability theorem. That theorem deletes original identities before projecting surviving adjacency. Thus the conclusion is real fault connectivity, not a renamed partition or packing assumption.

The positive connectedness result explicitly needs a nonempty actual vertex domain and positive `k`; taking no faults then supplies actual walks. The one-tree theorem also assumes finite actual vertices and constructs a subset of original edges via the proved native spanning-tree selection theorem. Its exact count is for that subset, with inherited full actual vertex set, and its every-edge-is-a-bridge condition excludes loops and parallel cycles. It is genuinely the `k = 1` sufficiency case, not multi-tree sufficiency.

Empty-domain checks are correct: the criterion permits the empty `Fin 0` partition with truncated `m - 1 = 0`, but the connectivity/tree corollaries exclude empty actual vertices. For `k = 0`, the criterion is vacuous and no positive-connectivity conclusion follows. A singleton actual graph can satisfy the criterion for arbitrary `k`, consistently with a zero-edge spanning tree and reflexive reachability.

### 2. Genuine within-block components

`blockGraph` retains precisely edges whose endpoints are related by the supplied setoid. Reachable endpoints remain in one block by induction on an actual walk. `componentRefinement` is that graph's actual reachable setoid. The proofs establish refinement, monotonicity, and equality exactly when each supplied block is connected in the chosen color.

Idempotence is not postulated: the proof identifies the two successive within-block graphs, using the fact that every retained adjacency already connects its endpoints in the first refinement. Disconnected endpoints in a common original block establish a strict refinement.

The native specialization uses `G.restrict F` before `toSimpleGraph`. Inspection of Mathlib confirms restriction preserves `G.vertexSet`, intersects the native edge set with `F`, and requires membership in `F` for each link. Parallel identities therefore affect color membership before projection; isolated actual vertices survive. Phantom ambient vertices do not enter the native specialization.

### 3. Least-color choice and decreasing measure

`relatedPairs` counts exactly the ordered pairs related by the current partition. Proper refinement gives a proper subset of these pairs and therefore strictly smaller finite cardinality. `splitColors` contains precisely those colors whose component refinement changes the current partition. `refinementStep` actually chooses its minimum when nonempty, and otherwise returns the current partition. `least_split_color_prior_fixed` proves all preceding colors are already fixed.

This matches least-color priority rather than choosing an arbitrary splitting color. Splitting is applied to all current blocks in that color. These operations are classical/noncomputable; they are mathematically specified finite choices, not an extracted executable efficiency result.

For zero colors, the splitting set is empty and the step is the identity. For an empty vertex domain, the related-pair measure is zero and no strict refinement exists. Reflexive singleton blocks are already connected. None of these cases needs an unstated positive cardinality assumption.

### 4. Actual bounded stabilization

The natural-measure induction proves a fixed point among iterates of the supplied step, within the starting measure. Its application uses the already proved strict decrease of the actual least-color step; no termination or packing oracle is assumed. The final bound follows from the number of ordered pairs being at most the square of the vertex count.

The returned terminal partition is an actual iterate, is below the initial partition, and is fixed under every color's component refinement. Every common fixed refinement below the initial partition remains below each iterate by monotonicity. Together these facts characterize a greatest common connected refinement below the starting partition, ruling out unjustified substitution of arbitrary singleton blocks. The result bounds refinement rounds only; it does not bound connectivity computation, representational cost, or the full packing algorithm.

### 5. Conditional original-edge exchange preservation

`reachable_of_edge_routes` substitutes actual target walks for each source adjacency and concatenates them inductively. In the native application, an old adjacency has an explicit original witness identity. If it is not the designated removed identity, `F \\ {e} ⊆ F'` retains it. If it is that identity, the explicit `replace` hypothesis supplies a within-block walk in the new graph. Thus original identity distinctions are respected throughout.

The theorem is intentionally a one-way reachability-preservation helper. It allows any `F'` retaining the other edges; it does not specify a unique added exchange edge, prove that the new color is a tree, construct a cycle or replacement route, or establish equality of the two component partitions. The route hypothesis is somewhat stronger than necessary when the removed identity is absent from `F`, but this is harmless and not a hidden conclusion.

The external-edge specialization makes the removed-edge case impossible inside a block, so it correctly needs no replacement route. Loops cause no false adjacency; in the general helper their endpoint route is reflexive, while an existing loop cannot satisfy the external-to-every-block premise. This is a valid foundation for the route-substitution portion of Kaiser's exchange argument, not his complete exchange claims.

### 6. Real disconnected-forest density

The simple-graph lemma starts with two actual unreachable vertices, supplying nonemptiness and implicitly distinctness. It extends the actual acyclic graph to a spanning tree of the complete graph. Equality with that tree would contradict the given unreachable pair, so the extension is strict. Strict edge-cardinality growth combined with the tree count proves the stated two-edge deficit.

The native forest lemma does not count a general multigraph by its simplified endpoint pairs. It first uses every actual edge being a bridge to prove native simplicity and projected acyclicity, then uses the genuine original-edge/simple-edge bijection. This rules out losing a loop or parallel cycle during the count. Finite actual vertices suffice; an ambient infinite vertex or edge type is not itself a problem.

The final density theorem refutes the all-bridges possibility using this deficit and returns an actual present nonbridge identity. Its conclusion is only a nonbridge. It does not construct an explicit cycle, force that identity to cross a prescribed partition, select a minimum-level edge, or prove the source's quotient-density calculation.

Important `Nat.card` boundary: if the actual edge set is infinite, `Nat.card G.edgeSet` is zero. The displayed density premise then cannot hold for a graph with two unreachable vertices, whose finite actual vertex count is at least two. Thus the theorem is sound but is not an infinite-edge density theorem; arbitrary infinite ambient `E` is supported when the relevant actual edge set is finite. Under the forest hypothesis, simplicity and the finite-vertex edge bijection already ensure the relevant actual edges are finite. No extra cardinality convention is silently used.

## Correspondence with the pinned source and exclusions

The local primary text is Tomas Kaiser, *A short proof of the tree-packing theorem*, arXiv:0911.2809v3, 6 March 2012. Its SHA-256 is `58342327af7f9d3cd5586549b12eb2ea53ab7018fc2a557dc6fc3859ffcde506`; the pinned PDF's SHA-256 is `4bef0841bbfe41cc93c2edfa33ec6649c56f7810e6e5dc932e053dec1a85808b`. Both match `review/tree-packing-proof-route.md`. This report paraphrases the needed source relationship without reproducing the paper.

The component sequence and least-color policy agree with the construction on source page 2, allowing an arbitrary starting partition and zero colors as safe generalizations. The one-tree construction supplies a genuine base ingredient. The disconnected-forest deficit is an ingredient for the density contradiction on page 3, but the source applies that reasoning through terminal partition quotients and then obtains an appropriate crossing cycle. Those quotient/cycle steps are not proved by this batch. The conditional route substitution matches the walk-preservation mechanism in Claim 1 on page 4, but construction of its routes and the exceptional-block/level analysis remain to be supplied. No decomposition maximality order or Claim 2/maximality contradiction is implemented here.

Not reviewed: drafts `NativeCorePackingCriterion`, `NativeForestQuotient`, `NativeQuotientCardinality`, `NativeQuotientReachability`, `NativeCrossingNonbridge`, `NativeColorCrossings`, and `NativeTerminalDensity`. General Nash-Williams/Tutte packing, the cycle-level exchange construction, decomposition maximality, Mader splitting, the CS09 Steiner-forest existence/expansion join, optimized sampling, full algorithmic runtime, and the main paper's full upper bounds remain open. This component PASS must not be presented as resolving them.
