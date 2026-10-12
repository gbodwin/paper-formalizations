import MinorFreeSpanners.FourArmCoreBudget

/-! A genuine finite maximum of disjoint eligible carriers. Every remaining
eligible pair of original far-endpoint paths would augment this maximum. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} [Fintype I] {A B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem exists_four_arm_packing (C : ClusterFamily (I := I) A w D)
    (H : SimpleGraph I) (d : I → ℝ) (L : ℝ) (R : Finset I) :
    ∃ P : Finset (Finset I),
      (∀ S∈P,S⊆R ∧ C.FourArmCore H d L B S) ∧
      (∀ S∈P,∀ T∈P,S≠T → Disjoint S T) ∧
      ∀ S : Finset I,S⊆R → Disjoint S (P.biUnion id) → ¬C.FourArmCore H d L B S := by
  classical
  let good (P : Finset (Finset I)) :=
    (∀ S∈P,S⊆R ∧ C.FourArmCore H d L B S) ∧
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

omit [Fintype I] in
 theorem no_residual_four_arm_edge (C : ClusterFamily (I := I) A w D)
    (H : SimpleGraph I) (d : I → ℝ) (L : ℝ) (R U : Finset I)
    (hmax : ∀ S : Finset I,S⊆R → Disjoint S U → ¬C.FourArmCore H d L B S)
    {u v s t x y : I} (p : H.Walk u v) (q : H.Walk s t)
    (hp : p.IsPath) (hq : q.IsPath)
    (hpq : Disjoint p.support.toFinset q.support.toFinset)
    (hR : p.support.toFinset∪q.support.toFinset⊆R)
    (hU : Disjoint (p.support.toFinset∪q.support.toFinset) U)
    (hx : WeightedInterior (fun i => d i+1) L p x)
    (hy : WeightedInterior (fun i => d i+1) L q y)
    (hL : 0<L) (hd : ∀ i∈R,d i≤D)
    {a b : V} (ha : a∈C.branch x) (hb : b∈C.branch y) : ¬B.Adj a b := by
  intro hab
  obtain ⟨S,hS,hsub⟩ := C.four_arm_core_of_paths H d L B p q hp hq hpq hx hy hL
    (fun i hi => hd i (hR hi)) ha hb hab
  exact hmax S (hsub.trans hR) (Finset.disjoint_of_subset_left hsub hU) hS

end ClusterFamily
end MinorFreeSpanners
