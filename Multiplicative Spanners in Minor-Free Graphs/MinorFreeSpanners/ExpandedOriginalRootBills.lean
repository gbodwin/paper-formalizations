import MinorFreeSpanners.PriorPhaseOriginalPartition
import MinorFreeSpanners.RootPaymentUnion

/-! Absorbing new original labels preserves the high/weak distinction.
Expanded weak roots need their touching bill; expanded high roots need only
marked edges. Both increments are covered by the actual absorbed-label bill. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} [Fintype I] [Fintype V]
variable {A B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem touchingEdges_union (C : ClusterFamily (I:=I) A w D) (S U : Finset I) :
    C.touchingEdges B (S∪U)=C.touchingEdges B S∪C.touchingEdges B U := by
  classical
  ext e
  simp only [touchingEdges,Finset.mem_filter,Finset.mem_union]
  aesop

 theorem markedEdges_union_subset (C : ClusterFamily (I:=I) A w D) (S U : Finset I) :
    C.markedEdges B (S∪U)⊆C.markedEdges B S∪C.touchingEdges B U := by
  classical
  intro e he
  obtain ⟨he,i,hi,j,hj,x,hx,y,hy,rfl⟩ := Finset.mem_filter.mp he
  rcases Finset.mem_union.mp hi with hi|hi
  · rcases Finset.mem_union.mp hj with hj|hj
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he,i,hi,j,hj,x,hx,y,hy,rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he,j,hj,i,y,hy,x,hx,Sym2.eq_swap⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he,i,hi,j,x,hx,y,hy,rfl⟩)

omit [Fintype V] in
 theorem original_edge_union_weight_le (S U : Finset (Sym2 V))
    (hw : ∀ e∈S∪U,0≤w e) :
    (∑ e∈S∪U,w e)≤(∑ e∈S,w e)+(∑ e∈U,w e) := by
  classical
  have hn : 0≤∑ e∈S∩U,w e := Finset.sum_nonneg
    (fun e he => hw e (Finset.mem_union_left _ (Finset.mem_inter.mp he).1))
  have he : (∑ e∈S∪U,w e)+(∑ e∈S∩U,w e)=(∑ e∈S,w e)+(∑ e∈U,w e) :=
    Finset.sum_union_inter
  linarith

 theorem expanded_marked_weight_le (C : ClusterFamily (I:=I) A w D) (S U : Finset I)
    (hw : ∀ e∈B.edgeSet,0≤w e) :
    (∑ e∈C.markedEdges B (S∪U),w e)≤
      (∑ e∈C.markedEdges B S,w e)+(∑ e∈C.touchingEdges B U,w e) := by
  classical
  have hsub := C.markedEdges_union_subset (B:=B) S U
  have hnon : ∀ e∈C.markedEdges B S∪C.touchingEdges B U,0≤w e := by
    intro e he
    rcases Finset.mem_union.mp he with he|he
    · exact hw e (mem_edgeFinset.mp (Finset.mem_filter.mp he).1)
    · exact hw e (mem_edgeFinset.mp (Finset.mem_filter.mp he).1)
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e he _ => hnon e he)).trans
    (original_edge_union_weight_le _ _ hnon)

 theorem expanded_touching_weight_le (C : ClusterFamily (I:=I) A w D) (S U : Finset I)
    (hw : ∀ e∈B.edgeSet,0≤w e) :
    (∑ e∈C.touchingEdges B (S∪U),w e)≤
      (∑ e∈C.touchingEdges B S,w e)+(∑ e∈C.touchingEdges B U,w e) := by
  classical
  rw [C.touchingEdges_union]
  apply original_edge_union_weight_le
  intro e he
  rcases Finset.mem_union.mp he with he|he
  · exact hw e (mem_edgeFinset.mp (Finset.mem_filter.mp he).1)
  · exact hw e (mem_edgeFinset.mp (Finset.mem_filter.mp he).1)

 theorem expanded_original_root_bills (C : ClusterFamily (I:=I) A w D)
    (weak high newWeak newHigh : Finset I) (hw : ∀ e∈B.edgeSet,0≤w e) :
    (∑ e∈C.touchingEdges B (weak∪newWeak),w e)+(∑ e∈C.markedEdges B (high∪newHigh),w e)≤
      (∑ e∈C.touchingEdges B weak,w e)+(∑ e∈C.markedEdges B high,w e)+
        (∑ e∈C.touchingEdges B newWeak,w e)+(∑ e∈C.touchingEdges B newHigh,w e) := by
  have hwk := C.expanded_touching_weight_le weak newWeak hw
  have hhi := C.expanded_marked_weight_le high newHigh hw
  linarith

end ClusterFamily
end MinorFreeSpanners
