# Source corrections and convention audit

Source: arXiv:2510.10227v1. Page numbers below are the printed PDF page numbers.

The repaired integer-parameter main results are valid. The literal all-real reading of Theorem 1.3's exact exponent is false; see item 6. The first two items are independently confirmed mismatches in the Appendix A proof as written; a repaired proof must address both rather than silently changing definitions. The asymmetric-demand, fractional-integrality, and graph-level nonmonotonicity counterexamples are formalized; the full two-edge maximal-sequence example below remains a source-level graph calculation.

## 1. Ordered demand versus an undirected matching (pages 5, 13)

Definition 2.2 makes D an ordered-pair function. Definition 2.4 bounds outgoing and incoming totals separately by A(v). Definition A.1 asks for an undirected matching on exactly A(v) copies per vertex whose count between copies(u) and copies(v) equals D(u,v) for every ordered pair.

- Literal counterexample: two vertices with A=1 and D(0,1)=1, D(1,0)=0. Undirected edge counts are symmetric, so they cannot equal this D.
- If one instead interprets every directed unit as a distinct undirected matching edge, a directed 3-cycle with A=1 satisfies both budgets but requires three matching edges on three copies. Equivalently, reciprocal unit demand on two vertices needs two incidences at each vertex.
- If one undirected edge is allowed to represent both reciprocal units, the edge count no longer equals total directed demand as required in the proof of Lemma A.6.

A conservative repair gives each vertex separate outgoing and incoming copies, A(v) of each. The demand-matching graph then has 2|A| vertices. The dispersed demand must be scaled to respect the increased incident-copy budget. With the direct adaptation, the expected union constant changes from 8α(|A|,s) to 16α(2|A|,s). This remains the same asymptotic order once the claimed arboricity bound is proved. The matching construction and downstream repaired union bound are now checked; the final proof uses paired sparse orientations and accounts explicitly for every loss.

## 2. Integral demand versus fractional scaling (pages 5, 15)

Definition 2.2 requires integer values, while Definition A.5 multiplies by 1/(2α). A single tree edge with α=1 gives a half-unit entry, so the resulting function is not a demand under Definition 2.2.

A repair can consistently allow fractional demands or extract an integral demand on the same positive support. `DemandExtraction.lean` now constructs a maximal feasible integral demand and proves that its total is at least half the fractional total, with the same integral row/column budgets. This uses no transportation theorem: every positive supported pair has a saturated row or column, and charging to those endpoints loses at most a factor two. It does not assert entrywise domination. The final construction now proves its fractional budgets and support geometry and includes this additional factor. Entrywise rounding down is insufficient.

## 3. Ratio of sums, not sum of ratios (page 13)

In the proof of Theorem 5.1, the displayed implication from |C_i|/a_i ≤ φ for every i to Σ_i |C_i|/a_i ≤ φ is false. Two terms, each equal to φ=1, suffice as a counterexample. The intended valid statement is

(Σ_i |C_i|)/(Σ_i a_i) ≤ φ,

when the denominator is positive. This is exactly the ratio in Theorem 4.1, so the local repair preserves the intended estimate.

## 4. Sparsity gives an inequality (page 12)

Equation (5.1) and the subsequent equality use sparsity = φ. Definition 2.10 gives sparsity ≤ φ. Replacing both equality signs by ≤ yields the desired Lemma 5.2 bound.

## Formalization conventions to make explicit

- Permit the zero cut as a *decomposition*, including when the input is already an expander or has no edges. Definition 2.5's nonzero requirement otherwise leaves the degenerate existence statement unsupported.
- A sparse-cut witness must have positive separated demand. The quotient with zero demand is not assigned sparsity zero.
- Preserve strict separation throughout the triangle argument in Lemma A.7. The printed prose weakens > to ≥, but the earlier strict inequality supplies the needed strict conclusion.
- Prove finite termination explicitly: each positive-demand sparse cut makes at least one currently h-near pair permanently farther than h, and there are finitely many ordered pairs.

## 5. Maximality certifies the unscaled sum, not its larger rescaling (page 12)

Theorem 5.1 selects a maximal sparse-cut sequence, then calls its scaled sum `(1+1/(s−1)) ΣC_i` expanding by maximality. Maximality only certifies the graph after the **unscaled** sum. Length-constrained expansion is not, in general, monotone under further length increases: these may make separation cheaper before a currently h-near pair ceases to be h-near.

An independent semantic audit supplied a concrete example: two disjoint edges a,b; initial lengths zero; capacities 1 and 100; A=1 at every vertex; h=1, s=2, φ=35. The cut C(a)=2,C(b)=1/5 costs 22 and separates two units of demand. After C, lengths are 4 and 2/5. Only edge b supports distinct h-near pairs; separating its two units requires further cost > 80, greater than φ·2=70. Hence this one-cut sequence is maximal. After 2C, b instead has length 4/5; an additional cut D(b)=13/20 costs 65 and makes its length 21/10 > 2, so the graph is no longer an expander.

The proof repair is simple and preserves the main bound: return the unscaled sum as the decomposition; use Theorem 4.1 only to upper-bound the cost of the larger scaled sum; transfer that bound downward by nonnegative capacities/cuts. `DecompositionReduction.lean` implements precisely this logic. The explicit numerical example is independently source-reviewed; its full graph-level Lean encoding is still pending.

### Repaired matching bridge checkpoint

`DirectedDemandMatching`, `DemandMatchingFamily`, `SequentialDemandGeometry`, and `CutSequenceMatching` now implement the separate outgoing/incoming-copy repair. From an actual sparse-cut sequence, the auxiliary graph has exactly 2|A| vertices and summed maximum demand volumes as its edge count, and is proved parallel greedy in reverse order. Its forest partition therefore uses the explicit bound at 2|A|, not |A|. The completed dispersion construction accounts for the doubled copy budget and the factor-two integral extraction loss. The repaired final union theorem now follows from this bridge.

### Direct decomposition repair

`DirectDecomposition.lean` now gives a complete alternative proof of the integer-s Theorem 5.1 regime, without a union-sparsity premise. The matching graph's exact edge count equals the sum of witness volumes, so its checked density bound gives the total cut cost directly. Returning the unscaled sum yields explicit slack 8s·(2|A|)^(2/s). `DegreeDecomposition.lean` specializes to unit capacities and degree weights, giving 64s·n^(4/s) slack. These proofs pass local kernel checks and independent semantic review; their exact-checkpoint CI is recorded separately. The separately completed union theorem is not a dependency of these decomposition results.

### Repaired integral union proof

`PairingLists` through `DegreeUnion` complete an alternative to the rooted-forest dispersion. A sparse orientation with incoming-child pairing produces at least half the auxiliary edges as demand pairs while using each copy at most K+1 times, where K=ceil(8s(2|A|)^(2/s)). Projection through exactly 2A(u) copies and support-preserving integral extraction give an actual integral A-respecting witness of mass at least total volume / (8(K+1)). The scaled union costs at most twice the unscaled sum. Thus the loss is 16(K+1), bounded by 512s·|A|^(2/s). The nonempty sparse-sequence degree specialization is 2048s·n^(4/s)·φ.

These are finite-sequence, integer-s≥2 statements. A positive total attained volume is required for the ratio theorem; the source's unqualified zero-denominator interpretation is not adopted. The original Lemma 4.2's literal 8α(|A|,s) constant is not claimed by this repaired construction.

## 6. The exact exponent requires an integer parameter (printed pages 2–3, 7–8)

Definition 1.1 and Theorem 1.3 say only s≥2; they do **not** explicitly require an integer. Section 3's proof assumes even s and discusses the odd case, so integrality is implicit in the proof but missing from the statement.

The unrestricted real-s reading of Theorem 1.3 is false. Fix s=5/2 and insert the edges of K_{a,a} in any order, with one edge per matching. Every batch is a matching. Before an edge is inserted, its opposite-side endpoints have no direct edge and no two-edge path, by bipartiteness. Their earlier distance is therefore at least three or infinite, strictly greater than s. Thus the graph satisfies the literal definition. It has a² edges and 2a vertices; every forest has at most 2a−1 edges, so its arboricity is at least a²/(2a−1), linear in n=2a. This cannot be O(s·n^(2/s))=O(n^(4/5)). There is no maximality or minimum-batch-size condition that excludes this example; the source explicitly permits singleton matchings.

The cleanest faithful repair is to state **integer s≥2** for the exact O(s·n^(2/s)) theorem. For all real s≥2, rounding downward instead gives O(s·n^(2/floor(s))), and hence the weaker smooth bound O(s·n^(4/s)). A real-s graph is floor(s)-parallel-greedy because its earlier distances are integers (or infinite); floor(s)≥s/2. `RealParameterArboricity.lean` now certifies the actual rounded and smooth all-real forest partitions. The new real-cut proof chain now also preserves the exact real output parameters, with general exponent 4/s and degree-specialized exponent 8/s. Thus the simplified n^O(1/s) statements extend to all real s≥2; the exact general 2/s exponent is not claimed for that larger domain.

### Formal counterexample family and all-real repairs

`BipartiteCounterexample.lean` now proves the 5/2-parallel-greedy family for every a, the exact a² edge count, the forest-cover lower bound K(2a−1)≥a², and impossibility of any uniform constant times n^(4/5). The real cut extensions in `RealCutSequence`, `RealUnionWitness`, `RealUnionSparsity`, and `RealDegreeTheorems` round only auxiliary counting, retaining exact real cut geometry and all integral-witness guarantees.

## 7. Lemma A.7 needs maximizing witness demands (pages 15–16)

The lemma's hypotheses mention arbitrary A-respecting h-length demands separated by the respective cuts, but its third conclusion lower-bounds the dispersed mass using the cuts' **maximum** demand volumes. The lower bound in Lemma A.6 only supplies the sum of the actual input demand sizes. Substitution of maximum cut volumes requires each input to be a maximizing witness, as intended in the preceding Appendix discussion. Arbitrarily smaller separated demands do not justify that substitution.

The repaired proof constructs attained maximum witnesses directly from `demandVolume` and proves the exact summed-volume auxiliary edge count. Thus this qualification is enforced by the formal theorem, not left as an undocumented premise. The original literal matching/fractional definitions have the separate defects above.
