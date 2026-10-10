# Corrected proof of Lemma 4.3

Source: [arXiv:2511.20111v2](https://arxiv.org/html/2511.20111v2), printed page 10, PDF page 12. This is a local correction to the displayed signs and indexing, not a counterexample to the lemma or main theorem. Independent source review confirmed the issue on 10 October 2026.

Let G′ have unique shortest paths. Fix the **initial** active demand set A′ and a comparison hopset H′={e₁,…,e_h}, where H′_i consists of its first i edges. For a demand d=(s,t), write q_i(d) for its raw hopdistance after inserting H′_i. The telescoping identity is

    Σ_{d∈A′} q_h(d) = φ′ − Σ_i Σ_{d∈A′} (q_{i−1}(d) − q_i(d)).

The original display reverses the decrement. All graphs in this argument are G′, and the prefix sets satisfy H′_i ⊆ H′. The set A′ remains fixed even if some demands subsequently become inactive.

For e_i=(u_i,v_i), define I_i(d)=1 exactly when u_i occurs before v_i on the unique original shortest s→t path, and 0 otherwise. Then

    q_{i−1}(d) − q_i(d) ≤ I_i(d) · (hopdist_G′(u_i,v_i)−1)
                        = q_0(d) − hopdist_{G′∪{e_i}}(d).

The incidence factor is essential; the displayed unconditional equality without it is false for an edge outside the demand's unique path. The following singleton decrement in the paper also has its sign reversed.

For each initially active demand, the singleton raw-hop saving is at most its thresholded-potential saving. Consequently

    Σ_{d∈A′} q_h(d) ≥ φ′ − Σ_i Δ′(e_i)
                    ≥ φ′ − h · max_e Δ′(e).

If H′ has hopbound B, the left side is at most |A′|B, yielding the intended conclusion. Empty active sets are handled without dividing by |A′|.

## Checked replacement argument

The Lean proof uses direct expansion rather than the faulty displayed telescoping sequence. `WeightedExpansion.unique_expansion` expands every comparison hopedge into its actual original shortest path, preserving the cost and the exact expanded length. Uniqueness identifies the expansion with the original demand path. `WeightedSavings.multi_edge_savings` then bounds aggregate saving by the sum of singleton savings. A minimum-hop augmented shortest path is simple, so no comparison edge is charged twice.

`WeightedProgress.comparison_progress` performs the finite demand/edge averaging. `WeightedTransfer` proves that a compatible perturbation's augmented shortest walks remain shortest in the original weights. `WeightedStateProgress` applies this to the actual greedy state, with insertion-sensitive closure weights.

These statements currently cover finite directed graphs with nonnegative real weights. They do not silently assert an undirected edge-budget conversion or arbitrary negative-weight conventions.
