import MinorFreeSpanners.OriginalRootResidualPartition
import MinorFreeSpanners.MixedPriorEdgeTransport

/-! Original host edges split exactly into prior-paid incidences, remaining
selected-root edges, and remaining residual incidences. The first two are the
actual earlier-phase bills, not low-degree charges on collapsed roots. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} [Fintype I] [Fintype V]
variable {A B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem marked_sub_touching (C : ClusterFamily (I:=I) A w D) (U prior : Finset I) :
    C.markedEdges B U\C.touchingEdges B prior=C.markedEdges B (U\prior) := by
  classical
  have heq {i j : I} {x : V} (hi : x∈C.branch i) (hj : x∈C.branch j) : i=j := by
    by_contra h
    exact Set.disjoint_left.mp (C.disjoint i j h) hi hj
  ext e
  constructor
  · intro he
    obtain ⟨he,hnot⟩ := Finset.mem_sdiff.mp he
    obtain ⟨hBe,i,hi,j,hj,x,hx,y,hy,rfl⟩ := Finset.mem_filter.mp he
    have hip : i∉prior := fun h => hnot (C.original_edge_mem_touching prior h hx hy (mem_edgeFinset.mp hBe))
    have hjp : j∉prior := by
      intro h
      apply hnot
      simpa only [Sym2.eq_swap] using C.original_edge_mem_touching prior h hy hx (mem_edgeFinset.mp hBe).symm
    exact Finset.mem_filter.mpr ⟨hBe,i,Finset.mem_sdiff.mpr ⟨hi,hip⟩,
      j,Finset.mem_sdiff.mpr ⟨hj,hjp⟩,x,hx,y,hy,rfl⟩
  · intro he
    obtain ⟨hBe,i,hi,j,hj,x,hx,y,hy,rfl⟩ := Finset.mem_filter.mp he
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr
      ⟨hBe,i,(Finset.mem_sdiff.mp hi).1,j,(Finset.mem_sdiff.mp hj).1,x,hx,y,hy,rfl⟩,?_⟩
    intro hp
    obtain ⟨_,k,hk,l,u,hu,v,hv,he⟩ := Finset.mem_filter.mp hp
    rcases Sym2.eq_iff.mp he with ⟨hxu,_⟩ | ⟨_,hyu⟩
    · subst u
      exact (Finset.mem_sdiff.mp hi).2 ((heq hx hu) ▸ hk)
    · subst u
      exact (Finset.mem_sdiff.mp hj).2 ((heq hy hu) ▸ hk)

 theorem original_prior_root_residual_partition (C : ClusterFamily (I:=I) A w D)
    (hcover : ∀ x,∃ i,x∈C.branch i) (U prior : Finset I) :
    B.edgeFinset\C.touchingEdges B prior=
      C.markedEdges B (U\prior) ∪ C.unpaidTouchingEdges B (Finset.univ\U) prior ∧
    Disjoint (C.markedEdges B (U\prior)) (C.unpaidTouchingEdges B (Finset.univ\U) prior) := by
  classical
  have hp := C.original_root_residual_edge_partition (B:=B) hcover U
  constructor
  · rw [←hp.2,Finset.union_sdiff_distrib,C.marked_sub_touching]
    rfl
  · rw [←C.marked_sub_touching U prior]
    exact hp.1.mono Finset.sdiff_subset Finset.sdiff_subset

 theorem original_prior_root_residual_weight (C : ClusterFamily (I:=I) A w D)
    (hcover : ∀ x,∃ i,x∈C.branch i) (U prior : Finset I) :
    (∑ e∈B.edgeFinset,w e)=(∑ e∈C.touchingEdges B prior,w e)+
      (∑ e∈C.markedEdges B (U\prior),w e)+
      ∑ e∈C.unpaidTouchingEdges B (Finset.univ\U) prior,w e := by
  classical
  have hsub : C.touchingEdges B prior⊆B.edgeFinset := Finset.filter_subset _ _
  have hp := C.original_prior_root_residual_partition (B:=B) hcover U prior
  calc
    _ = (∑ e∈C.touchingEdges B prior,w e)+(∑ e∈B.edgeFinset\C.touchingEdges B prior,w e) :=
      by have hh := Finset.sum_sdiff (f:=w) hsub;linarith
    _ = _ := by rw [hp.1,Finset.sum_union hp.2];ring

 theorem mixed_total_prior_original_weight {G : SimpleGraph V} {D₁ : ℝ}
    (C : ClusterFamily (I:=I) A w D) (hA : A≤G)
    (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w D₁)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (hcover : ∀ x,∃ i,x∈C.branch i) (prior : Finset (SelectedResidualIndex P)) :
    (∑ e∈B.edgeFinset,w e)=(∑ e∈C.touchingEdges B (originalMixedLabels P prior),w e)+
      (∑ e∈C.markedEdges B (P.biUnion id\originalMixedLabels P prior),w e)+
      ∑ e∈(C.selectedResidual hA P F hbranch).unpaidTouchingEdges B
        (Finset.univ\selectedRoots P) prior,w e := by
  classical
  have hr := C.mixed_touching_edges_eq (B:=B) hA P F hbranch hcover
    (Finset.univ\selectedRoots P) (fun t => by simp [selectedRoots])
  rw [originalResidualIndices_all_residual] at hr
  have hu : (C.selectedResidual hA P F hbranch).unpaidTouchingEdges B
      (Finset.univ\selectedRoots P) prior=
      C.unpaidTouchingEdges B (Finset.univ\P.biUnion id) (originalMixedLabels P prior) := by
    simp only [unpaidTouchingEdges,hr,C.mixed_all_touching_edges_eq hA P F hbranch hcover]
  rw [hu]
  exact C.original_prior_root_residual_weight hcover (P.biUnion id) (originalMixedLabels P prior)

end ClusterFamily
end MinorFreeSpanners
