# Source corrections and convention audit

Source: arXiv:2510.10227v1. Page numbers below are the printed PDF page numbers.

The main asymptotic theorems have **not** been refuted. The first two items are independently confirmed mismatches in the Appendix A proof as written; a repaired proof must address both rather than silently changing definitions. Formal counterexamples are being compiled separately.

## 1. Ordered demand versus an undirected matching (pages 5, 13)

Definition 2.2 makes D an ordered-pair function. Definition 2.4 bounds outgoing and incoming totals separately by A(v). Definition A.1 asks for an undirected matching on exactly A(v) copies per vertex whose count between copies(u) and copies(v) equals D(u,v) for every ordered pair.

- Literal counterexample: two vertices with A=1 and D(0,1)=1, D(1,0)=0. Undirected edge counts are symmetric, so they cannot equal this D.
- If one instead interprets every directed unit as a distinct undirected matching edge, a directed 3-cycle with A=1 satisfies both budgets but requires three matching edges on three copies. Equivalently, reciprocal unit demand on two vertices needs two incidences at each vertex.
- If one undirected edge is allowed to represent both reciprocal units, the edge count no longer equals total directed demand as required in the proof of Lemma A.6.

A conservative repair gives each vertex separate outgoing and incoming copies, A(v) of each. The demand-matching graph then has 2|A| vertices. The dispersed demand must be scaled to respect the increased incident-copy budget. With the direct adaptation, the expected union constant changes from 8α(|A|,s) to 16α(2|A|,s). This remains the same asymptotic order once the claimed arboricity bound is proved. The construction and downstream constants still need formal verification.

## 2. Integral demand versus fractional scaling (pages 5, 15)

Definition 2.2 requires integer values, while Definition A.5 multiplies by 1/(2α). A single tree edge with α=1 gives a half-unit entry, so the resulting function is not a demand under Definition 2.2.

A repair can consistently allow fractional demands or extract an integral demand on the same positive support. `DemandExtraction.lean` now constructs a maximal feasible integral demand and proves that its total is at least half the fractional total, with the same integral row/column budgets. This uses no transportation theorem: every positive supported pair has a saturated row or column, and charging to those endpoints loses at most a factor two. It does not assert entrywise domination. The fractional construction must still prove its budgets and support geometry; the final union constant must include this additional factor. Entrywise rounding down is insufficient.

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

`DirectedDemandMatching`, `DemandMatchingFamily`, `SequentialDemandGeometry`, and `CutSequenceMatching` now implement the separate outgoing/incoming-copy repair. From an actual sparse-cut sequence, the auxiliary graph has exactly 2|A| vertices and summed maximum demand volumes as its edge count, and is proved parallel greedy in reverse order. Its forest partition therefore uses the explicit bound at 2|A|, not |A|. The remaining dispersion construction must still account for the doubled copy budget and the factor-two integral extraction loss. This is not yet a proof of the full union theorem.
