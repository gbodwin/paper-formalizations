import MinorFreeSpanners.MixedOriginalEdgeTransport
import MinorFreeSpanners.MixedSmallAbsorptionPhase

/-! Exact original-edge accounting separates selected-root interiors and
root-to-root edges from the residual-incident bag. The decomposition is on
host Sym2 edges, so neither orientation nor collapsed-root multiplicity is lost. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem originalResidualIndices_all_residual {I : Type*} [Fintype I]
    (P : Finset (Finset I)) :
    originalResidualIndices P (Finset.univ\selectedRoots P)=Finset.univ\P.biUnion id := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,j.property⟩
  · intro hi
    refine Finset.mem_image.mpr ⟨⟨i,(Finset.mem_sdiff.mp hi).2⟩,?_,rfl⟩
    simp [residualIndexPreimage,selectedRoots]

namespace ClusterFamily
variable {I V : Type*} [Fintype I] [Fintype V]
variable {A B G : SimpleGraph V} {w : Sym2 V → ℝ} {D D₁ : ℝ}

 theorem original_root_residual_edge_partition (C : ClusterFamily (I:=I) A w D)
    (hcover : ∀ x,∃ i,x∈C.branch i) (U : Finset I) :
    Disjoint (C.markedEdges B U) (C.touchingEdges B (Finset.univ\U)) ∧
    C.markedEdges B U ∪ C.touchingEdges B (Finset.univ\U)=B.edgeFinset := by
  classical
  have heq {i j : I} {x : V} (hi : x∈C.branch i) (hj : x∈C.branch j) : i=j := by
    by_contra h
    exact Set.disjoint_left.mp (C.disjoint i j h) hi hj
  constructor
  · apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨_,i,hi,j,hj,x,hx,y,hy,he⟩ := Finset.mem_filter.mp he
    obtain ⟨_,k,hk,l,u,hu,v,hv,hf⟩ := Finset.mem_filter.mp hf
    have hab : s(x,y)=s(u,v) := he.symm.trans hf
    rcases Sym2.eq_iff.mp hab with ⟨hxu,hyv⟩ | ⟨hxv,hyu⟩
    · subst u
      exact (Finset.mem_sdiff.mp hk).2 ((heq hx hu) ▸ hi)
    · subst u
      exact (Finset.mem_sdiff.mp hk).2 ((heq hy hu) ▸ hj)
  · apply Finset.Subset.antisymm
    · intro e he
      rcases Finset.mem_union.mp he with he | he
      · exact (Finset.mem_filter.mp he).1
      · exact (Finset.mem_filter.mp he).1
    · intro e he
      induction e using Sym2.inductionOn with
      | hf x y =>
        obtain ⟨i,hx⟩ := hcover x
        obtain ⟨j,hy⟩ := hcover y
        have hxy : B.Adj x y := mem_edgeFinset.mp he
        by_cases hi : i∈U
        · by_cases hj : j∈U
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he,i,hi,j,hj,x,hx,y,hy,rfl⟩)
          · apply Finset.mem_union_right
            have hh := C.original_edge_mem_touching (Finset.univ\U)
              (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hj⟩) hy hx hxy.symm
            simpa only [Sym2.eq_swap] using hh
        · exact Finset.mem_union_right _ (C.original_edge_mem_touching (Finset.univ\U)
            (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hi⟩) hx hy hxy)

 theorem mixed_total_original_weight (C : ClusterFamily (I:=I) A w D) (hA : A≤G)
    (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w D₁)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (hcover : ∀ x,∃ i,x∈C.branch i) :
    (∑ e∈B.edgeFinset,w e)=(∑ e∈C.markedEdges B (P.biUnion id),w e)+
      ∑ e∈(C.selectedResidual hA P F hbranch).touchingEdges B (Finset.univ\selectedRoots P),w e := by
  classical
  have ht := C.mixed_touching_edges_eq (B:=B) hA P F hbranch hcover (Finset.univ\selectedRoots P)
    (fun t => by simp [selectedRoots])
  rw [originalResidualIndices_all_residual] at ht
  rw [ht]
  have hp := C.original_root_residual_edge_partition (B:=B) hcover (P.biUnion id)
  rw [←Finset.sum_union hp.1,hp.2]

end ClusterFamily
end MinorFreeSpanners
