import MinorFreeSpanners.RightStarQuotient
import MinorFreeSpanners.VertexDeletionBudget

/-! Pay the actual edge loss from deleting only uncovered left singleton
branches after the full star contraction. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

/-- Every deleted quotient vertex is a genuine singleton original left
vertex, whose quotient degree is bounded by its original degree. -/
theorem IsStarPacking.right_quotient_edge_budget {G : SimpleGraph V}
    {A B C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L)
    (hAB : Disjoint A B) (hCB : C ⊆ B) (hcover : A ∪ B=Finset.univ)
    (m : ℕ) (hdeg : ∀ a ∈ A, G.degree a ≤ m) :
    (fullStarContraction G C L).edgeFinset.card ≤
      (rightStarQuotient G B C L).edgeFinset.card+m*(A \ C.biUnion L).card := by
  classical
  have hAC : Disjoint A C := hAB.mono_right hCB
  have hd : ∀ i ∈ Finset.univ \ rightStarKeep B C L,
      (fullStarContraction G C L).degree i ≤ m := by
    intro i hi
    cases i with
    | inl b => simp [rightStarKeep] at hi
    | inr x =>
      have hn : x.val ∉ B := by simpa [rightStarKeep] using hi
      have ha : x.val ∈ A := by
        have hm : x.val ∈ A ∪ B := hcover.symm ▸ Finset.mem_univ _
        exact (Finset.mem_union.mp hm).resolve_right hn
      have hs := (h.fullMinorModel hAC).singleton_branch_degree (.inr x) x.val
        (by intro z hz; simpa [IsStarPacking.fullMinorModel,fullStarBranch] using hz)
      exact hs.trans (hdeg x.val ha)
  have hsum : (∑ i ∈ Finset.univ \ rightStarKeep B C L,
      (fullStarContraction G C L).degree i) ≤ m*(A \ C.biUnion L).card := by
    calc
      _ ≤ ∑ _i ∈ Finset.univ \ rightStarKeep B C L, m := Finset.sum_le_sum hd
      _ = m*(Finset.univ \ rightStarKeep B C L).card := by simp [mul_comm]
      _ = _ := by rw [right_deleted_card hAB hCB hcover]
  have he := induced_vertex_deletion_edge_budget (fullStarContraction G C L)
    (rightStarKeep B C L)
  have he' : (fullStarContraction G C L).edgeFinset.card ≤
      (rightStarQuotient G B C L).edgeFinset.card+
      ∑ i ∈ Finset.univ \ rightStarKeep B C L, (fullStarContraction G C L).degree i := by
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at he ⊢
    convert he using 1
    congr 2
    ext i
    simp
  omega

end MinorFreeSpanners
