import MinorFreeSpanners.PostleMates
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! Actual integer-degree regularization on one side of a bipartite graph.
No preservation of unmatedness under deletion is asserted; the subsequent
small-dense/unmated dichotomy must be reapplied to the constructed graph. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Choose exactly m neighbors per left vertex, and construct the resulting
actual symmetric spanning subgraph. The right degrees are unconstrained. -/
theorem exists_left_regular_subgraph (G : SimpleGraph V) (A B : Finset V)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (m : ℕ)
    (hdeg : ∀ a ∈ A, m ≤ G.degree a) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartiteWith (A:Set V) (B:Set V) ∧
      (∀ a ∈ A, H.degree a = m) ∧ H.edgeFinset.card = m*A.card := by
  classical
  have hex : ∀ a : A, ∃ N : Finset V, N ⊆ G.neighborFinset a.val ∧ N.card = m := by
    intro a
    exact Finset.exists_subset_card_eq (by simpa using hdeg a.val a.property)
  choose N hN hcard using hex
  let S : V → Finset V := fun a => if ha : a ∈ A then N ⟨a,ha⟩ else ∅
  have hSmem : ∀ a b, b ∈ S a → a ∈ A ∧ G.Adj a b := by
    intro a b hab
    dsimp [S] at hab
    split_ifs at hab with ha
    · exact ⟨ha,(G.mem_neighborFinset a b).mp (hN ⟨a,ha⟩ hab)⟩
    · simp at hab
  let H : SimpleGraph V := {
    Adj := fun a b => b ∈ S a ∨ a ∈ S b
    symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
    loopless := ⟨fun a h => h.elim
      (fun ha => (hSmem a a ha).2.ne rfl)
      (fun ha => (hSmem a a ha).2.ne rfl)⟩ }
  letI : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
  have hHG : H ≤ G := by
    intro a b hab
    exact hab.elim (fun h => (hSmem a b h).2) (fun h => (hSmem b a h).2.symm)
  have hH : H.IsBipartiteWith (A:Set V) (B:Set V) :=
    ⟨hG.disjoint,fun _ _ h => hG.mem_of_adj (hHG h)⟩
  have hdegree : ∀ a ∈ A, H.degree a = m := by
    intro a ha
    have he : H.neighborFinset a = S a := by
      ext b
      rw [H.mem_neighborFinset]
      change (b ∈ S a ∨ a ∈ S b) ↔ b ∈ S a
      constructor
      · rintro (h | h)
        · exact h
        · have hx := hSmem b a h
          have haB := hG.mem_of_mem_adj hx.1 hx.2
          exact (Set.disjoint_left.mp hG.disjoint ha haB).elim
      · exact Or.inl
    rw [← H.card_neighborFinset_eq_degree,he]
    simp only [S,dif_pos ha]
    exact hcard ⟨a,ha⟩
  refine ⟨H,hHG,hH,hdegree,?_⟩
  rw [← isBipartiteWith_sum_degrees_eq_card_edges hH]
  calc
    ∑ a ∈ A, H.degree a = ∑ a ∈ A, m := Finset.sum_congr rfl hdegree
    _ = m*A.card := by simp [Nat.mul_comm]

end MinorFreeSpanners
