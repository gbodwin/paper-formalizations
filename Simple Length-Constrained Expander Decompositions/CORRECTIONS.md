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

A correct repair may either consistently allow fractional demands or use integral transportation/bipartite-flow extraction. For the latter, one must obtain an integer demand on the same supported ordered pairs, with row and column bounds A and total at least the fractional total. Entrywise rounding down is insufficient. This background fact and any use of it will be explicit in the trust boundary.

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
