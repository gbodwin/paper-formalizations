import MinorFreeSpanners.ResidualHeavyAttachment

/-! Original unpaid heavy edges internally determine owners in an actual
root-carrier family. The orientation is changed only to put the root endpoint
first, exactly as required by the confined heavy-absorption walks. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} [Fintype I] [Fintype V]
variable {A B G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem exists_original_heavy_owners (C : ClusterFamily (I:=I) A w D)
    (hB : B≤G) (P : Finset (Finset I)) (R paid roots : Finset I)
    (root : {r // r∈roots} → Finset I) (hroot : ∀ r,r.val∈root r)
    (M : ℝ) (hweight : ∀ e∈B.edgeSet,w e≤M)
    (hsub : ∀ S∈P,S⊆R)
    (hcover : ∀ i,i∈R ∨ i∈paid ∨ i∈roots)
    (hno : ∀ i∈R,∀ j∈R,i∉paid → j∉paid →
      ∀ x∈C.branch i,∀ y∈C.branch j,¬B.Adj x y) :
    ∃ owner : {S // S∈C.heavyAttachmentBlocks B P paid} → {r // r∈roots},
    ∃ source target : {S // S∈C.heavyAttachmentBlocks B P paid} → V,
      (∀ S,∃ i∈root (owner S),source S∈C.branch i) ∧
      (∀ S,∃ i∈S.val,target S∈C.branch i) ∧
      (∀ S,G.Adj (source S) (target S)) ∧
      (∀ S,w s(source S,target S)≤M) ∧
      (∀ S,s(source S,target S)∈C.unpaidTouchingEdges B S.val paid) ∧
      (∀ S∈P,S∉C.heavyAttachmentBlocks B P paid → C.unpaidTouchingEdges B S paid=∅) := by
  obtain ⟨o,port,x,y,hp,hempty⟩ := C.exists_actual_heavy_attachments P R paid roots hsub hcover hno
  let owner := fun S => (⟨(o S).val,(Finset.mem_sdiff.mp (o S).property).1⟩ : {r // r∈roots})
  refine ⟨owner,y,x,?_,?_,?_,?_,?_,hempty⟩
  · intro S
    exact ⟨(owner S).val,hroot (owner S),(hp S).2.2.1⟩
  · intro S
    exact ⟨port S,(Finset.mem_sdiff.mp (hp S).1).1,(hp S).2.1⟩
  · intro S
    exact hB (hp S).2.2.2.1.symm
  · intro S
    exact hweight _ (hp S).2.2.2.1.symm
  · intro S
    simpa only [Sym2.eq_swap] using (hp S).2.2.2.2

end ClusterFamily
end MinorFreeSpanners
