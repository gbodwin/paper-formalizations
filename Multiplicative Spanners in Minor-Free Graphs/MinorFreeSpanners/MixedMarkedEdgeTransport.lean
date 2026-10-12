import MinorFreeSpanners.MixedPriorEdgeTransport

/-! A marked mixed-label edge remains exactly the original unordered host
edge. This also counts heavy edges internal to an already collapsed root. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} [Fintype I] [Fintype V]
variable {A B G : SimpleGraph V} {w : Sym2 V → ℝ} {D E : ℝ}

omit [Fintype I] in
 theorem mixed_marked_edges_eq (C : ClusterFamily (I:=I) A w D) (hA : A≤G)
    (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (S : Finset (SelectedResidualIndex P)) :
    (C.selectedResidual hA P F hbranch).markedEdges B S=C.markedEdges B (originalMixedLabels P S) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨he,i,hi,j,hj,x,hx,y,hy,rfl⟩ := Finset.mem_filter.mp he
    obtain ⟨a,ha,hxa⟩ := (C.mixed_branch_original hA P F hbranch i x).mp hx
    obtain ⟨b,hb,hyb⟩ := (C.mixed_branch_original hA P F hbranch j y).mp hy
    exact Finset.mem_filter.mpr ⟨he,a,Finset.mem_biUnion.mpr ⟨i,hi,ha⟩,
      b,Finset.mem_biUnion.mpr ⟨j,hj,hb⟩,x,hxa,y,hyb,rfl⟩
  · intro he
    obtain ⟨he,a,ha,b,hb,x,hx,y,hy,rfl⟩ := Finset.mem_filter.mp he
    obtain ⟨i,hi,hai⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨j,hj,hbj⟩ := Finset.mem_biUnion.mp hb
    exact Finset.mem_filter.mpr ⟨he,i,hi,j,hj,x,
      (C.mixed_branch_original hA P F hbranch i x).mpr ⟨a,hai,hx⟩,y,
      (C.mixed_branch_original hA P F hbranch j y).mpr ⟨b,hbj,hy⟩,rfl⟩

end ClusterFamily
end MinorFreeSpanners
