import MinorFreeSpanners.InducedDegreeBudget

/-! The actual surviving graph after a small deletion from the robust core. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
attribute [local instance] Classical.propDecidable

theorem robust_core_survives (G : SimpleGraph V) (D : ℕ) (hD : 0 < D)
    (hsize : Fintype.card V ≤ 12*D) (hdeg : ∀ x, 4*D ≤ G.degree x)
    (hrob : DeletionConnected G (2*D)) (S : Finset V) (hS : S.card ≤ D) :
    let A : Finset V := Finset.univ \ S
    (G.induce (A:Set V)).Connected ∧
      Fintype.card A ≤ 4*(3*D) ∧
      ∀ x : A, 3*D ≤ (G.induce (A:Set V)).degree x := by
  classical
  let A : Finset V := Finset.univ \ S
  change (G.induce (A:Set V)).Connected ∧ Fintype.card A ≤ 4*(3*D) ∧
    ∀ x : A, 3*D ≤ (G.induce (A:Set V)).degree x
  have hAset : (A : Set V) = {x | x ∉ S} := by ext x; simp [A]
  have hpre : (G.induce (A:Set V)).Preconnected := by
    rw [hAset]
    exact hrob S (by omega)
  have hAne : A.Nonempty := by
    by_contra hempty
    have hsall : Finset.univ ⊆ S := by
      intro x _
      by_contra hxs
      exact hempty ⟨x,by simp [A,hxs]⟩
    have hc := Finset.card_le_card hsall
    simp only [Finset.card_univ] at hc
    have hd := hdeg (Classical.arbitrary V)
    have hu := G.degree_lt_card_verts (Classical.arbitrary V)
    omega
  have hnonempty : Nonempty A := ⟨⟨hAne.choose,hAne.choose_spec⟩⟩
  let := hnonempty
  refine ⟨{ preconnected := hpre },?_,?_⟩
  · have hc := Finset.card_le_card (Finset.subset_univ A)
    rw [Finset.card_univ] at hc
    rw [Fintype.card_coe]
    exact hc.trans (by omega)
  · intro x
    have hsep := degree_induce_add_separator G A S (by
      intro u _ v _
      by_cases hv : v ∈ S
      · exact Or.inr hv
      · exact Or.inl (by simp [A,hv])) x
    have hd := hdeg x.val
    omega

end MinorFreeSpanners
