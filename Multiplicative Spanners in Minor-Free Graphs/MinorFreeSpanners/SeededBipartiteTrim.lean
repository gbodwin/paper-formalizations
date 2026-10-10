import MinorFreeSpanners.PostleBipartiteTrim
import MinorFreeSpanners.StarForestGraph
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! Actual degree regularization preserving an already chosen spanning
subgraph. The forced forest edges are never lost by neighbor selection. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Choose exactly m neighbors at each left vertex while retaining all
actual edges of a supplied subgraph whose left degrees are at most m. -/
theorem exists_left_regular_between (G T : SimpleGraph V) (hTG : T ≤ G) (A B : Finset V)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (m : ℕ)
    (hlow : ∀ a ∈ A, T.degree a ≤ m)
    (hdeg : ∀ a ∈ A, m ≤ G.degree a) :
    ∃ H : SimpleGraph V, T ≤ H ∧ H ≤ G ∧ H.IsBipartiteWith (A:Set V) (B:Set V) ∧
      (∀ a ∈ A, H.degree a = m) ∧ H.edgeFinset.card = m*A.card := by
  classical
  have hex : ∀ a : A, ∃ N : Finset V, T.neighborFinset a.val ⊆ N ∧
      N ⊆ G.neighborFinset a.val ∧ N.card = m := by
    intro a
    apply Finset.exists_subsuperset_card_eq
    · intro x hx
      exact (G.mem_neighborFinset _ _).mpr (hTG ((T.mem_neighborFinset _ _).mp hx))
    · simpa using hlow a.val a.property
    · simpa using hdeg a.val a.property
  choose N hTN hN hcard using hex
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
  let : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
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
    simp only [S,dite_eq_left ha]
    exact hcard ⟨a,ha⟩
  have hTH : T ≤ H := by
    intro a b hab
    rcases hG.mem_of_adj (hTG hab) with ⟨ha,_⟩|⟨_,hb⟩
    · change a ∈ A at ha
      apply Or.inl
      dsimp [S]
      rw [dite_eq_left ha]
      exact hTN ⟨a,ha⟩ ((T.mem_neighborFinset a b).mpr hab)
    · change b ∈ A at hb
      apply Or.inr
      dsimp [S]
      rw [dite_eq_left hb]
      exact hTN ⟨b,hb⟩ ((T.mem_neighborFinset b a).mpr hab.symm)
  refine ⟨H,hTH,hHG,hH,hdegree,?_⟩
  rw [← isBipartiteWith_sum_degrees_eq_card_edges hH]
  calc
    ∑ a ∈ A, H.degree a = ∑ a ∈ A, m := Finset.sum_congr rfl hdegree
    _ = m*A.card := by simp [Nat.mul_comm]

/-- The constructed genuine star forest is preserved by degree trimming;
all chosen center-leaf edges survive in the actual regularized graph. -/
theorem IsStarPacking.exists_regular_supergraph_of_forest (G : SimpleGraph V)
    (A B C : Finset V) (ell m : ℕ) (L : V → Finset V)
    (h : IsStarPacking G A C ell L) (hAC : Disjoint A C)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hm : 1 ≤ m)
    (hdeg : ∀ a ∈ A, m ≤ G.degree a) :
    ∃ H : SimpleGraph V, starForestGraph C L ≤ H ∧ H ≤ G ∧
      H.IsBipartiteWith (A:Set V) (B:Set V) ∧
      (∀ a ∈ A, H.degree a=m) ∧ H.edgeFinset.card=m*A.card := by
  exact exists_left_regular_between G (starForestGraph C L) h.starForest_le A B hG m
    (fun _ ha => (h.starForest_left_degree_le_one hAC ha).trans hm) hdeg

end MinorFreeSpanners
