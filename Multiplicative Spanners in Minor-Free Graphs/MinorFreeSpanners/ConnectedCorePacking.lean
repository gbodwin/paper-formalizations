import MinorFreeSpanners.ConnectedFinsetGrowth

/-! Finite maximum packing of actual connected cores. The residual has no
connected set as large as a core; no packing oracle is assumed. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

theorem exists_connected_core_packing {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (hk : 0<k) :
    ∃ P : Finset (Finset V),
      (∀ S∈P, S.card=k ∧ ConnectedWithin G S) ∧
      (∀ S∈P, ∀ T∈P, S≠T → Disjoint S T) ∧
      (∀ T : Finset V, ConnectedWithin G T →
        Disjoint T (P.biUnion id) → T.card < k) := by
  classical
  let good (P : Finset (Finset V)) :=
    (∀ S∈P, S.card=k ∧ ConnectedWithin G S) ∧
    (∀ S∈P, ∀ T∈P, S≠T → Disjoint S T)
  let candidates := (Finset.univ : Finset (Finset (Finset V))).filter good
  have h0 : (∅ : Finset (Finset V))∈candidates := by simp [candidates,good]
  obtain ⟨P,hP,hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨_,h0⟩
  have hp := (Finset.mem_filter.mp hP).2
  refine ⟨P,hp.1,hp.2,?_⟩
  intro T hT hd
  by_contra hn
  obtain ⟨S,hST,hcard,hS⟩ := hT.exists_subset_card k (by omega)
  have hSP : S∉P := by
    intro hs
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0<S.card by omega)
    exact Finset.disjoint_left.mp hd (hST hv) (Finset.mem_biUnion.mpr ⟨S,hs,hv⟩)
  have hdis (U : Finset V) (hU : U∈P) : Disjoint S U := by
    apply Finset.disjoint_left.mpr
    intro v hv hu
    exact Finset.disjoint_left.mp hd (hST hv) (Finset.mem_biUnion.mpr ⟨U,hU,hu⟩)
  have hnew : good (insert S P) := by
    constructor
    · intro U hU
      rcases Finset.mem_insert.mp hU with rfl | hU
      · exact ⟨hcard,hS⟩
      · exact hp.1 U hU
    · intro U hU W hW hne
      rcases Finset.mem_insert.mp hU with he | hUP
      · subst U
        rcases Finset.mem_insert.mp hW with he | hWP
        · exact (hne he.symm).elim
        · exact hdis W hWP
      · rcases Finset.mem_insert.mp hW with he | hWP
        · subst W
          exact (hdis U hUP).symm
        · exact hp.2 U hUP W hWP hne
  have hh := hmax (insert S P) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnew⟩)
  rw [Finset.card_insert_of_notMem hSP] at hh
  omega

end MinorFreeSpanners
