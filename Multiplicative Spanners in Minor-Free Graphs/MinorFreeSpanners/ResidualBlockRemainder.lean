import MinorFreeSpanners.SelectedResidualPathSlices
import MinorFreeSpanners.RootedPartitionMerge

/-! The internally segmented residual components yield a full disjoint block
family. Merging precisely the attachment blocks with the root retains every
other original path block and covers the exact chosen residual union. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem residual_attachment_remainder {I : Type*} (H : SimpleGraph I)
    (R : Finset I) (F : Finset (H.induce (R:Set I)).ConnectedComponent)
    (d : I → ℝ) (M L : ℝ) (N : ℕ)
    (port : (H.induce (R:Set I)).ConnectedComponent → I)
    (P : (H.induce (R:Set I)).ConnectedComponent → Finset (Finset I))
    (A ends : (H.induce (R:Set I)).ConnectedComponent → Finset I)
    (hpart : ∀ t∈F,ResidualAttachmentPartition H R t d M L N (port t) (P t) (A t) (ends t))
    (root : I) (hr : root∉R) :
    let allBlocks := F.biUnion P
    let selected := F.image A
    let out := insert (insert root (F.biUnion A)) (allBlocks\selected)
    (∀ S∈out,S.Nonempty) ∧
    (∀ S∈out,∀ T∈out,S≠T → Disjoint S T) ∧
    out.biUnion id=insert root (F.biUnion (ResidualComponents.block H R)) ∧
    (∀ S∈allBlocks\selected,∃ t∈F,S∈P t ∧ S≠A t) := by
  classical
  let allBlocks := F.biUnion P
  let selected := F.image A
  have hsub : ∀ t∈F,∀ S∈P t,S⊆ResidualComponents.block H R t := by
    intro t ht S hS i hi
    rw [←(hpart t ht).cover]
    exact Finset.mem_biUnion.mpr ⟨S,hS,hi⟩
  have hcover : allBlocks.biUnion id=F.biUnion (ResidualComponents.block H R) := by
    ext i
    simp only [allBlocks,Finset.mem_biUnion,id_eq]
    constructor
    · rintro ⟨S,⟨t,ht,hS⟩,hi⟩
      exact ⟨t,ht,hsub t ht S hS hi⟩
    · rintro ⟨t,ht,hi⟩
      rw [←(hpart t ht).cover] at hi
      obtain ⟨S,hS,hi⟩ := Finset.mem_biUnion.mp hi
      exact ⟨S,⟨t,ht,hS⟩,hi⟩
  have hselected : selected.biUnion id=F.biUnion A := by
    ext i
    simp [selected]
  have hsel : selected⊆allBlocks := by
    intro S hS
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hS
    exact Finset.mem_biUnion.mpr ⟨t,ht,(hpart t ht).member⟩
  have hdis : ∀ S∈allBlocks,∀ T∈allBlocks,S≠T → Disjoint S T := by
    intro S hS T hT hST
    obtain ⟨t,ht,hSt⟩ := Finset.mem_biUnion.mp hS
    obtain ⟨q,hq,hTq⟩ := Finset.mem_biUnion.mp hT
    by_cases he : t=q
    · subst q
      exact (hpart t ht).disjoint S hSt T hTq hST
    · exact (ResidualComponents.disjoint H R t q he).mono (hsub t ht S hSt) (hsub q hq T hTq)
  have hne : ∀ S∈allBlocks,S.Nonempty := by
    intro S hS
    obtain ⟨t,ht,hSt⟩ := Finset.mem_biUnion.mp hS
    obtain ⟨x,y,p,_,he,_,_⟩ := (hpart t ht).good S hSt
    exact ⟨x,he ▸ List.mem_toFinset.mpr p.start_mem_support⟩
  have hroot : root∉allBlocks.biUnion id := by
    intro hi
    rw [hcover] at hi
    obtain ⟨t,_,hi⟩ := Finset.mem_biUnion.mp hi
    exact hr (ResidualComponents.subset H R t hi)
  obtain ⟨hn,hd,hc⟩ := rooted_partition_merge allBlocks selected root hsel hroot hne hdis
  rw [hselected] at hn hd hc
  rw [hcover] at hc
  refine ⟨hn,hd,hc,?_⟩
  intro S hS
  obtain ⟨hS,hnot⟩ := Finset.mem_sdiff.mp hS
  obtain ⟨t,ht,hSt⟩ := Finset.mem_biUnion.mp hS
  exact ⟨t,ht,hSt,by intro he;exact hnot (Finset.mem_image.mpr ⟨t,ht,he.symm⟩)⟩

end MinorFreeSpanners
