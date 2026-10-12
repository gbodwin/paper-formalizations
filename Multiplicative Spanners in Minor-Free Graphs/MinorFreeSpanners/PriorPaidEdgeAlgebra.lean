import MinorFreeSpanners.OriginalUnpaidEdgeClassification

/-! Exact old-edge identities under an enlarged paid-label set. These equalities
retain incidences at both represented endpoints, without collapsing parallel
original edges or treating a paid root as an eligible absorption center. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} [Fintype I] [Fintype V]
variable {A B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem touching_edges_mono (C : ClusterFamily (I:=I) A w D)
    {S U : Finset I} (h : S⊆U) : C.touchingEdges B S⊆C.touchingEdges B U := by
  classical
  intro e he
  obtain ⟨hE,i,hi,j,x,hx,y,hy,he⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨hE,i,h hi,j,x,hx,y,hy,he⟩

 theorem touching_edges_union (C : ClusterFamily (I:=I) A w D) (S U : Finset I) :
    C.touchingEdges B (S∪U)=C.touchingEdges B S∪C.touchingEdges B U := by
  classical
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨hE,i,hi,j,x,hx,y,hy,he⟩ := Finset.mem_filter.mp he
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hE,i,hi,j,x,hx,y,hy,he⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hE,i,hi,j,x,hx,y,hy,he⟩)
  · exact Finset.union_subset (C.touching_edges_mono Finset.subset_union_left)
      (C.touching_edges_mono Finset.subset_union_right)

 theorem unpaid_touching_antitone (C : ClusterFamily (I:=I) A w D)
    (R : Finset I) {paid more : Finset I} (h : paid⊆more) :
    C.unpaidTouchingEdges B R more⊆C.unpaidTouchingEdges B R paid := by
  classical
  intro e he
  obtain ⟨he,hnot⟩ := Finset.mem_sdiff.mp he
  exact Finset.mem_sdiff.mpr ⟨he,fun hp => hnot (C.touching_edges_mono h hp)⟩

 theorem unpaid_touching_union (C : ClusterFamily (I:=I) A w D)
    (R paid prior : Finset I) :
    C.unpaidTouchingEdges B R (paid∪prior)=
      C.unpaidTouchingEdges B R paid\C.touchingEdges B prior := by
  classical
  simp only [unpaidTouchingEdges,C.touching_edges_union]
  ext e
  simp only [Finset.mem_sdiff,Finset.mem_union,not_or]
  tauto

end ClusterFamily
end MinorFreeSpanners
