import MinorFreeSpanners.Minor
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-! Elementary robustness from actual common neighbors. This is a graph
lemma for the deterministic clique-minor route, not a density oracle. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

/-- Removing fewer than q vertices leaves every surviving pair connected. -/
def DeletionConnected (G : SimpleGraph V) (q : ℕ) : Prop :=
  ∀ S : Finset V, S.card < q → (G.induce {x | x ∉ S}).Preconnected

/-- The two actual neighbor sets fit inside the finite host. -/
theorem degree_sum_le_common_neighbors_add_card (G : SimpleGraph V) (x y : V) :
    G.degree x + G.degree y ≤ Fintype.card (G.commonNeighbors x y)+Fintype.card V := by
  classical
  have h := Finset.card_union_add_card_inter (G.neighborFinset x) (G.neighborFinset y)
  have hi : G.neighborFinset x ∩ G.neighborFinset y =
      (G.commonNeighbors x y).toFinset := by ext z; simp [mem_commonNeighbors]
  rw [hi,Set.toFinset_card,card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at h
  have hu := Finset.card_le_card (Finset.subset_univ (G.neighborFinset x ∪ G.neighborFinset y))
  simp only [Finset.card_univ] at hu
  omega

/-- A common-neighbor lower bound gives actual two-hop paths after any
smaller deletion set, with no connectivity certificate assumed. -/
theorem deletionConnected_of_common_neighbors (G : SimpleGraph V) (q : ℕ)
    (h : ∀ x y, x ≠ y → q ≤ Fintype.card (G.commonNeighbors x y)) :
    DeletionConnected G q := by
  classical
  intro S hS x y
  by_cases hxy : x = y
  · subst y
    exact ⟨.nil⟩
  have hne : x.val ≠ y.val := fun he => hxy (Subtype.ext he)
  have hout : ∃ z, z ∈ G.commonNeighbors x.val y.val ∧ z ∉ S := by
    by_contra hn
    push_neg at hn
    have hs : (G.commonNeighbors x.val y.val).toFinset ⊆ S := by
      intro z hz
      exact hn z (Set.mem_toFinset.mp hz)
    have hc := Finset.card_le_card hs
    rw [Set.toFinset_card] at hc
    have hq := h x.val y.val hne
    omega
  obtain ⟨z,hz,hzS⟩ := hout
  let w : {x : V // x ∉ S} := ⟨z,hzS⟩
  exact ⟨Walk.cons (show (G.induce {x | x ∉ S}).Adj x w from hz.1)
    (Walk.cons (show (G.induce {x | x ∉ S}).Adj w y from hz.2.symm) .nil)⟩

/-- If twice a minimum degree exceeds the order by q, the graph remains
connected after deletion of fewer than q vertices. -/
theorem deletionConnected_of_degree (G : SimpleGraph V) (q δ : ℕ)
    (hδ : ∀ x, δ ≤ G.degree x) (hbudget : Fintype.card V+q ≤ 2*δ) :
    DeletionConnected G q := by
  apply deletionConnected_of_common_neighbors
  intro x y _
  have hc := degree_sum_le_common_neighbors_add_card G x y
  have hx := hδ x
  have hy := hδ y
  omega

end MinorFreeSpanners
