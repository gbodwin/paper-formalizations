# Twentieth bounded semantic/source review

Date: 2026-10-11 UTC. Frozen three-file, 100-module checkpoint.

Verdict: **COMPONENT PASS. No semantic blocker found in the three frozen modules.** This packet defines the actual two-identity color swap, connects the constructed lower-level exchange to a genuine changed-color native tree and route, and constructs a genuine maximum of the stated finite signature over every admissible finite coloring. It does not establish strict improvement, the recomputed-prefix comparison, the full inductive countercase, or tree packing.

## Scope and identity

I read all 279 lines of the three production modules, the relevant earlier native tree/exchange/level/refinement dependencies, Mathlib's graph restriction/deletion/simple-adjacency definitions and Pi/Prod lexicographic orders, and the pinned Kaiser text, principally pages 2–4. No compiler or kernel checker was invoked. No proof, repository state, GitHub content, or Site was edited. Only this report was written. The new PriorityComparison, SignatureStages, and RefinementRigidity drafts are excluded; this review grants no verdict on them.

Independently checked:

- Repository: `gbodwin/paper-formalizations`; branch: `light-eft-spanners-checkpoints`.
- Published proof commit: `5e40d7fb299f03c7555da20f5b62ae0ec6b4d94c`.
- Tree: `970aa85b7591a2955b626bbdbfa3ef66a73801dc`.
- Prior reviewed97 parent: `e607ac12ac0023aaeb4616cedeababb92fca0850`.

The GitHub commit fetch succeeded. The remote branch comparison against the pinned proof commit returned `identical`, zero ahead/behind, and no changed files. The local raw commit object independently rehashes to that published commit ID, with the tree and parent above. The three remote file contents were fetched independently and compared byte-for-byte with production; recomputed SHA-256 and Git blob hashes match. The first fetch used the branch, whose identity to the pinned commit was separately verified; the other two used the exact commit.

| Module | SHA-256 | Git blob |
|---|---|---|
| NativeColorExchange | `937369a6786937e32282d4d682eb8f388654656988e476bea64c57a43e835ec6` | `13c314da691fbdb8ed73a825420027bef68c683d` |
| NativeColoredExchange | `5b9a2390a337224a5b49231f8ef80482b5906b63a569b7f0054ef7c7a4701cfa` | `eb70627b44dc6460d118710138e6eedecd3f5b26` |
| NativeDecompositionMaximum | `0209d5f21ff2f4ce5068846c121a52c739a6a9acc345dc088877ca13dd0e54a1` | `945d41f4ffb9f42a2232a96d799cc9cecec488af` |

Review manifest, production manifest, current production, corresponding frozen drafts, and exact committed bytes agree. All **97 prior production Lean modules** are byte-identical between the parent, published proof commit, and current filesystem. Their prior review is inherited by equality, not repeated in full. The production directory, distinct aggregate-root imports, and statement-map module union each contain exactly the same 100 modules, with no missing or extra entries. The repository working tree was clean during inspection.

## Validation evidence and limits

Workspace and production twentieth build/replay logs agree byte-for-byte. The inspected gate script compiles the three new production sources with `-DwarningAsError=true`; the wrapper supplies `-DautoImplicit=false`. It also compiles the aggregate root, invokes the transitive project-declaration axiom audit, and checks the module index. The log records 765 audited declarations with only `propext`, `Classical.choice`, and `Quot.sound`, successful index status, and `TWENTIETH_AGGREGATE_GATE_PASSED`.

The inspected replay script uses the official `leanchecker` wrapper and records individual successful replay markers for all three new modules. This is corroboration of the supplied build/replay evidence, not fresh execution by this reviewer. Prior97 objects were reused; neither a clean local100 rebuild nor exact100 remote CI success is claimed here. Those are separate gates. No `sorry`, `admit`, custom `axiom`, unsafe declaration, implementation override, or local option weakening appears in the frozen sources.

## Semantic findings

### 1. Literal color exchange and native graph equality

`NativeColorExchange.lean:8–29` swaps values at the original identities e and d and leaves every other identity unchanged. The first/last class formulas require unequal original colors, which also forces e and d to be different. The formulas gain e/lose d and gain d/lose e in the correct directions. Other classes are exactly unchanged. Equal-identity or equal-color inputs to the raw definition simply produce no effective exchange; the nontrivial class lemmas do not silently permit them.

At lines 33–64 the equalities are native `Graph V E` equalities, proved using compatibility and exact edge sets. Mathlib restriction preserves `G.vertexSet`, intersects with the original edge set, and retains the original IsLink relation for each selected identity. Deletion removes the indicated identities before any conversion to simple adjacency. Consequently parallel identities are not collapsed by the swap, and phantom ambient vertices are not introduced.

A total color function gives every actual original edge exactly one color. Its native color restrictions therefore cover the actual edge set and are pairwise edge-disjoint by construction, even though this packet does not add separately named coverage/disjointness lemmas. The swapped function remains a total coloring on exactly the same E. Labels on unused ambient identities cannot change the native restricted graph.

### 2. Conditional all-stage preservation is correctly scoped

`exchangedColor_preserves_stages` (lines 67–92) retains two explicit replacement routes and two next-stage externality boundaries. The last-color case replaces the removed e; the earlier-color case replaces the removed d. All other colors use exact class equality. The underlying preservation lemma uses antitonicity correctly: stages at or before the removed edge's level contain the replacement route, and later stages cannot contain that edge in a within-block walk.

This proves preservation of old reachability inside the supplied original sequence R for every natural stage. It does **not** identify R with the new coloring's recomputed refinement sequence. Nor does it construct the last-color route or either boundary from a full source countercase. Those premises are visible and legitimate in a generic helper.

`exchanged_earlier_trees` (lines 96–125) requires the changed earlier class's actual native tree and preserves all remaining earlier trees by class equality. Fin.castSucc cannot equal Fin.last; the unchanged-class argument therefore selects the correct colors. The helper does not assume that the last color is a tree. Its changed-tree premise is supplied locally by the following joined construction once the caller has the relevant source inputs.

### 3. The changed-color tree and lower global boundary are constructed

`exchanged_graph_eq_tree_exchange` (`NativeColoredExchange.lean:12–29`) requires F to agree with the relevant color class on actual G edges only. Its native equality consequently survives arbitrary unused ambient color labels. The main theorem additionally requires F to be a subset of G.edgeSet, so its returned member d is an actual original edge.

`exists_actual_colored_tree_exchange` (lines 34–89) takes an actual earlier-color tree, an actual differently colored inserted e, an antitone top-initial R, m <= N, e internal at m, and genuine failure of an earlier-tree route between e's endpoints inside that block. These are local countercase inputs, not a supplied exchange identity, cycle, path, maximality fact, or final packing conclusion.

The inherited lower-exchange construction produces d in F, d != e, its strict lower level, and a genuine exchanged native tree with an actual within-level route. The new theorem identifies this native graph with the class of the literal swapped color function and transports the all-native-edges-bridge and connectedness conclusions to it. Thus acyclicity is not replaced by a count-only assertion or by acyclicity of simplified adjacency. The prior tree certification obtains genuine native all-bridge status; loops and parallel cycles are excluded as consequences.

The returned level is exactly `edgeLevel G R N d`, not a level silently computed in a restricted graph or with a different horizon. The earlier transport proof uses d's actual retention and the fact that it already crosses stage m to equate the local and global internal-stage sets. Since level(d) < m <= N, d crosses N. Actual membership and R 0 = top establish initial internality, and `finite_edgeLevel_boundary` proves separation at exactly level(d) + 1. The default zero for an empty internal-stage set is not used as a genuine level here.

The final route is converted edge by edge: inserted e receives color c; every retained old F identity other than d keeps c. Every edge carries its original IsLink evidence and the same R-block relation. This is a real route in the actual changed-color graph. The output deliberately omits some stronger inherited certificates, such as the selected minimum certificate and explicit internality; it does return the tree, strict lower global level, exact next-stage separation, and route advertised.

The main construction leaves source assembly explicit: R is generic, c need not yet be the actual chosen least splitting color, e's next-stage boundary is not an input or output here, and the last-color replacement route is not constructed here. For m = 0 the top/connectedness/no-route hypotheses are inconsistent, as they should be; no spurious lower natural level follows from an ordinary valid zero-stage case. A loop e is similarly excluded by the no-route premise and reflexive reachability.

### 4. Actual finite maximum, priority, and domains

`NativeDecompositionMaximum.lean:13–33` computes the least actual splitting color from `splitColors`, whose test is that genuine within-block component refinement changes R. If there is no such color, the sentinel is the number of colors. For q colors the formal values are 0 through q-1 with sentinel q, exactly the paper's values 1 through q with sentinel q+1 after subtracting one. In the main signature q = k+1, so the sentinel is k+1, not k.

The signature recomputes the genuine refinement iterates from top for the actual restricted native color graphs. Each stage first compares the cardinality of actual related ordered vertex pairs, then the actual least-color priority. Mathlib's inner Prod lexicographic order has this coordinate order. Its outer Pi lexicographic order uses the ordinary ascending order on `Fin (N+1)`, so the earliest differing stage controls the comparison. The final lemma at lines 54–62 is exactly that order's witness, not a pointwise-order substitution. It assumes the required prefix and stage inequalities; it does not prove them for a swap.

The optimizer (lines 38–50) forms `univ.filter (earlierColorTrees G)` over **all** functions E -> Fin(k+1), proves nonemptiness from seed, and invokes finite maximum existence on the actual signature. Every admissible other coloring belongs to that same set. It is a true maximum, rather than a supplied optimizer, a finite handpicked candidate list, or maximization over a weakened count certificate.

`Fintype E` is an explicit stronger-than-necessary ambient-edge finiteness requirement. Signature counts use `Fintype G.vertexSet`, not Fintype V. Different assignments to unused E identities only duplicate a decomposition in the finite search and cannot create fake graph edges or alter its signature. EarlierColorTrees uses actual native all-bridge status and connectedness for all k earlier colors. Its seed is a k-tree inductive premise for a (k+1)-color decomposition, not the desired (k+1)-tree conclusion.

For k = 0 the earlier-tree property is vacuous and Fin 1 admits one total coloring; the maximum is legitimate. The generic priority on Fin 0 has the empty sentinel 0. An empty actual vertex domain is also harmless for the numerical maximum; for positive k the seed's Connected property already requires actual nonemptiness. No infinite Nat.card is used to masquerade as a finite optimization domain.

### 5. Important source-order and horizon boundary

The related-pair count is a **strict-refinement rank**, not an injective encoding of partitions. The inherited `relatedPairs_card_lt` proves R < S implies a strict count increase. Equal partitions give equal counts. Thus a source-order improvement at a represented stage, with the source's exact equal partition/priority prefix, induces the corresponding strict numeric-signature improvement.

The converse is not asserted and should not be assumed. Distinct incomparable partitions can have equal pair counts; on four vertices, two different partitions into two pairs both have count eight. Equality of stage signature values therefore does not by itself imply equality of the actual partitions. To use maximality to recover prefix rigidity, one must first establish the relevant partition/refinement comparability, then use strict-rank monotonicity and maximality. This is a boundary of the representation, not a defect in any frozen theorem. The outside-freeze comparison/rigidity drafts were not reviewed.

N is arbitrary and explicit. The maximum controls only represented stages 0 through N. The module does not choose a horizon, assert stabilization by this N, or infer source maximality at every later stage. A downstream contradiction at m+1 requires that stage to be in the horizon, together with the actual recomputed-prefix and strict-improvement proof. A previously proved uniform quadratic stabilization bound is available elsewhere, but its application to this maximal choice remains assembly work. Classical finite optimization is not an efficient executable search or a complexity proof.

## Source correspondence and remaining work

Primary source: [Tomáš Kaiser, A short proof of the tree-packing theorem, arXiv:0911.2809v3](https://arxiv.org/pdf/0911.2809v3), 6 March 2012. Independently recomputed pinned PDF SHA-256: `4bef0841bbfe41cc93c2edfa33ec6649c56f7810e6e5dc932e053dec1a85808b`; text SHA-256: `58342327af7f9d3cd5586549b12eb2ea53ab7018fc2a557dc6fc3859ffcde506`.

Page 2 defines the full decomposition, least-color component refinement, terminal sentinel, and levels. Page 3 defines the lexicographic partial order and chooses an optimal decomposition whose earlier colors are trees, then obtains the lower-level earlier-tree exchange. Page 4 makes the literal two-color exchange and begins comparing the recomputed sequences. This packet supplies concrete color identities, the changed earlier-tree/route join, and a finite rank-based maximization tool. The numerical signature faithfully detects strict comparable-partition improvements but is not literally the source's partition-valued partial order.

Still open in this freeze: the original last-color route and selected earlier color assembled with the local join; admissibility of the full source swap in one joined countercase theorem; comparison and rigidity of newly recomputed partitions and least colors; strict improvement and maximality contradiction; a sufficient common horizon applied to that argument; initial induction and complete packing assembly. General tree/Steiner-forest packing, Mader splitting, Steiner expansion, weighted/fractional scope, runtime, and the main Light EFT upper bounds remain open. No completion percentage is inferred from module or declaration counts.

This is a bounded independent component review of the exact frozen packet, not a final audit or full-paper completion claim.
