import MinorFreeSpanners.ShortCycleCore

/-! A genuine finite maximum of disjoint eligible carriers. Every remaining
eligible original three-piece path would augment this maximum. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} [Fintype I] {A B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem exists_short_cycle_packing (C : ClusterFamily (I := I) A w D)
    (H : SimpleGraph I) (d : I → ℝ) (L : ℝ) (R : Finset I) :
    ∃ P : Finset (Finset I),
      (∀ S∈P,S⊆R ∧ C.ShortCycleCore H d L B S) ∧
      (∀ S∈P,∀ T∈P,S≠T → Disjoint S T) ∧
      ∀ S : Finset I,S⊆R → Disjoint S (P.biUnion id) → ¬C.ShortCycleCore H d L B S := by
  classical
  let good (P : Finset (Finset I)) :=
    (∀ S∈P,S⊆R ∧ C.ShortCycleCore H d L B S) ∧
    (∀ S∈P,∀ T∈P,S≠T → Disjoint S T)
  let candidates := (Finset.univ : Finset (Finset (Finset I))).filter good
  have h0 : (∅ : Finset (Finset I))∈candidates := by simp [candidates,good]
  obtain ⟨P,hPc,hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨_,h0⟩
  have hP := (Finset.mem_filter.mp hPc).2
  refine ⟨P,hP.1,hP.2,?_⟩
  intro S hSR hdis hcore
  have hne := hcore.nonempty C
  have hnot : S∉P := by
    intro hS
    exact Finset.disjoint_left.mp hdis hne.choose_spec
      (Finset.mem_biUnion.mpr ⟨S,hS,hne.choose_spec⟩)
  have hdS (T : Finset I) (hT : T∈P) : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro v hv ht
    exact Finset.disjoint_left.mp hdis hv (Finset.mem_biUnion.mpr ⟨T,hT,ht⟩)
  have hnew : good (insert S P) := by
    constructor
    · intro T hT
      rcases Finset.mem_insert.mp hT with rfl|hT
      · exact ⟨hSR,hcore⟩
      · exact hP.1 T hT
    · intro T hT U hU hneTU
      rcases Finset.mem_insert.mp hT with he|hTP
      · subst T
        rcases Finset.mem_insert.mp hU with he|hUP
        · exact (hneTU he.symm).elim
        · exact hdS U hUP
      · rcases Finset.mem_insert.mp hU with he|hUP
        · subst U
          exact (hdS T hTP).symm
        · exact hP.2 T hTP U hUP hneTU
  have hm := hmax (insert S P) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnew⟩)
  rw [Finset.card_insert_of_notMem hnot] at hm
  omega

end ClusterFamily
end MinorFreeSpanners
