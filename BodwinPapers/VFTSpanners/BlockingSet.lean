import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Vertex blocking sets and cycle elimination

Source: Greg Bodwin and Shyamal Patel,
*A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners*,
arXiv:1812.05778v2 (2019), Definition 3 and the deterministic part of Lemma 4.

This file does not prove the probabilistic edge count, the greedy-algorithm
blocking-set construction, or the main spanner-size theorem.
-/

namespace BodwinPapers.VFTSpanners

open SimpleGraph

universe u
variable {V : Type u}

/-- Definition 3: every blocking pair uses a graph edge and a vertex that is
not an endpoint; every cycle of length at most `k` contains such a pair. -/
def IsBlockingSet (G : SimpleGraph V) (k : ℕ) (B : Set (V × Sym2 V)) : Prop :=
  (∀ ⦃v : V⦄ ⦃e : Sym2 V⦄, (v, e) ∈ B → e ∈ G.edgeSet ∧ v ∉ e) ∧
  ∀ ⦃a : V⦄ (p : G.Walk a a), p.IsCycle → p.length ≤ k →
    ∃ v e, (v, e) ∈ B ∧ v ∈ p.support ∧ e ∈ p.edges

/-- The sampled graph after removing every edge paired with a sampled vertex.
The vertex type is exactly the sampled set `S`. -/
def prunedGraph (G : SimpleGraph V) (S : Set V)
    (B : Set (V × Sym2 V)) : SimpleGraph S where
  Adj x y := G.Adj x.val y.val ∧ ∀ v ∈ S, (v, s(x.val, y.val)) ∉ B
  symm := ⟨by
    intro x y h
    constructor
    · exact h.1.symm
    · simpa only [Sym2.eq_swap] using h.2⟩
  loopless := ⟨by
    intro x h
    exact G.loopless.irrefl x.val h.1⟩

/-- Every retained edge is an original edge. -/
def prunedInclusion (G : SimpleGraph V) (S : Set V)
    (B : Set (V × Sym2 V)) : prunedGraph G S B →g G where
  toFun := Subtype.val
  map_rel' := fun h => h.1

/-- Deterministic cycle-elimination step of Lemma 4: pruning a sampled graph
using a `k`-blocking set leaves no cycle of length at most `k`.
No finiteness or probability assumptions are needed for this step. -/
theorem prunedGraph_no_short_cycle {G : SimpleGraph V} {k : ℕ}
    {B : Set (V × Sym2 V)} (hB : IsBlockingSet G k B) (S : Set V)
    {a : S} (p : (prunedGraph G S B).Walk a a) (hp : p.IsCycle) :
    ¬ p.length ≤ k := by
  intro hlen
  let incl := prunedInclusion G S B
  have hcycle : (p.map incl).IsCycle := hp.map Subtype.val_injective
  obtain ⟨v, e, hve, hv, he⟩ := hB.2 (p.map incl) hcycle (by simpa using hlen)
  have hvS : v ∈ S := by
    rw [Walk.support_map] at hv
    obtain ⟨w, _, hwv⟩ := List.mem_map.mp hv
    exact hwv ▸ w.property
  rw [Walk.edges_map] at he
  obtain ⟨e', he', heq⟩ := List.mem_map.mp he
  have havoid : ∀ z ∈ S, (z, Sym2.map incl e') ∉ B := by
    revert he'
    refine Sym2.ind (fun x y hxy => ?_) e'
    exact (p.adj_of_mem_edges hxy).2
  exact havoid v hvS (heq.symm ▸ hve)

/-- Equivalent numerical form: each cycle in the pruned graph has length
strictly greater than `k`. This avoids conventions about infinite girth. -/
theorem prunedGraph_cycle_length_gt {G : SimpleGraph V} {k : ℕ}
    {B : Set (V × Sym2 V)} (hB : IsBlockingSet G k B) (S : Set V)
    {a : S} (p : (prunedGraph G S B).Walk a a) (hp : p.IsCycle) :
    k < p.length :=
  Nat.lt_of_not_ge (prunedGraph_no_short_cycle hB S p hp)

end BodwinPapers.VFTSpanners
