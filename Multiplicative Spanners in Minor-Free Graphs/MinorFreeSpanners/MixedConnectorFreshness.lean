import MinorFreeSpanners.ExactConnectorPooling
import MinorFreeSpanners.SelectedResidualClusters

/-! Actual old selected-root connectors are internal to the corresponding mixed
branch. Every connector of the later mixed phase therefore avoids all of them,
independently of orientation and of the choice of coarse graph for each carrier. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V J : Type*} [Fintype I] [Fintype J]
variable {A T G : SimpleGraph V} {w : Sym2 V → ℝ} {D D₁ : ℝ}

 theorem connectorEdges_endpoints (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (hT : T≤G) (H : SimpleGraph I) (hH : H≤C.graph T)
    (S : Finset I) {e : Sym2 V} (he : e∈C.connectorEdges hA hT H hH S) :
    ∃ x y,(∃ i∈S,x∈C.branch i) ∧ (∃ i∈S,y∈C.branch i) ∧ e=s(x,y) := by
  classical
  obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp he
  have hf := (Finset.mem_filter.mp f.property).2
  have hl := C.crossingEmbedding_label hA hT
    ⟨f.val,SimpleGraph.edgeSet_mono hH (mem_edgeFinset.mp (Finset.mem_filter.mp f.property).1)⟩
  have ht := (C.crossingEmbedding hA hT
    ⟨f.val,SimpleGraph.edgeSet_mono hH (mem_edgeFinset.mp (Finset.mem_filter.mp f.property).1)⟩).property
  generalize hd : (C.crossingEmbedding hA hT
    ⟨f.val,SimpleGraph.edgeSet_mono hH (mem_edgeFinset.mp (Finset.mem_filter.mp f.property).1)⟩).val=d at *
  obtain ⟨i,j,hij⟩ : ∃ i j,f.val=s(i,j) := by
    induction f.val using Sym2.inductionOn with
    | _ i j => exact ⟨i,j,rfl⟩
  change Sym2.map (C.minorModel hA hT).branchLabel d=Sym2.map some f.val at hl
  rw [hij] at hf hl
  obtain ⟨x,hx,y,hy,_,he⟩ := C.orient_crossing hA hT i j d ht hl
  exact ⟨x,y,⟨i,hf (by simp),hx⟩,⟨j,hf (by simp),hy⟩,he⟩

 theorem mixed_connectorPool_disjoint_prior (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (hT : T≤G) (P : Finset (Finset I))
    (F : ClusterFamily (I:={S // S∈P}) G w D₁)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (oldH : {S // S∈P} → SimpleGraph I) (holdH : ∀ S,oldH S≤C.graph T)
    (newH : J → SimpleGraph (SelectedResidualIndex P))
    (hnewH : ∀ j,newH j≤(C.selectedResidual hA P F hbranch).graph T)
    (carrier : J → Finset (SelectedResidualIndex P)) :
    Disjoint (C.connectorPool hA hT oldH holdH Subtype.val)
      ((C.selectedResidual hA P F hbranch).connectorPool le_rfl hT newH hnewH carrier) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e he hn
  obtain ⟨S,_,he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨x,y,hx,hy,rfl⟩ := C.connectorEdges_endpoints hA hT (oldH S) (holdH S) S.val he
  have hx' : x∈(C.selectedResidual hA P F hbranch).branch (Sum.inl S) := by
    change x∈F.branch S
    rw [hbranch]
    exact hx
  have hy' : y∈(C.selectedResidual hA P F hbranch).branch (Sum.inl S) := by
    change y∈F.branch S
    rw [hbranch]
    exact hy
  exact ((C.selectedResidual hA P F hbranch).connectorPool_fresh le_rfl hT newH hnewH carrier
    hn (Sum.inl S) x y hx' hy') rfl

end ClusterFamily
end MinorFreeSpanners
