import MinorFreeSpanners.MixedConnectorFreshness
import MinorFreeSpanners.ActualGroupReindex
import MinorFreeSpanners.SelectedResidualDegree
import MinorFreeSpanners.PartialResidualOwnership

/-! The literal two-stage connector union is internal to the expanded roots.
Any later connector crossing those roots therefore avoids the entire retained
union, regardless of the earlier choices of crossing representatives. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I J V : Type*} [Fintype I] [Fintype J]
variable {A T G : SimpleGraph V} {w : Sym2 V → ℝ} {D E : ℝ}

 theorem connectorPool_disjoint_internal (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (hT : T≤G) (H : J → SimpleGraph I) (hH : ∀ j,H j≤C.graph T)
    (S : J → Finset I) (prior : Finset (Sym2 V))
    (hprior : ∀ e∈prior,∃ i x y,x∈C.branch i ∧ y∈C.branch i ∧ e=s(x,y)) :
    Disjoint prior (C.connectorPool hA hT H hH S) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e he hn
  obtain ⟨i,x,y,hx,hy,rfl⟩ := hprior e he
  exact (C.connectorPool_fresh hA hT H hH S hn i x y hx hy) rfl

omit [Fintype I] [Fintype J] in
 theorem reindex_internal_edges (F : ClusterFamily (I:=I) G w E) (e : I ≃ J)
    (prior : Finset (Sym2 V))
    (hprior : ∀ f∈prior,∃ i x y,x∈F.branch i ∧ y∈F.branch i ∧ f=s(x,y)) :
    ∀ f∈prior,∃ j x y,x∈(F.reindex e.symm).branch j ∧ y∈(F.reindex e.symm).branch j ∧ f=s(x,y) := by
  intro f hf
  obtain ⟨i,x,y,hx,hy,he⟩ := hprior f hf
  exact ⟨e i,x,y,by simpa only [reindex,e.symm_apply_apply] using hx,
    by simpa only [reindex,e.symm_apply_apply] using hy,he⟩

attribute [-instance] instDecidableEqSum in
 theorem absorbed_connector_union_internal (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (hT : T≤G) (P : Finset (Finset I))
    (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (H : SimpleGraph (SelectedResidualIndex P))
    (O : ResidualOwnership H (selectedRoots P))
    (Q : Finset (H.induce ((Finset.univ\selectedRoots P : Finset (SelectedResidualIndex P)):Set _)).ConnectedComponent)
    {E' : ℝ} (Fnew : ClusterFamily (I:={r // r∈selectedRoots P}) G w E')
    (hnew : ∀ r,Fnew.branch r={x | ∃ i∈O.chosenFilled Q r,x∈(C.selectedResidual hA P F hbranch).branch i})
    (oldH : {S // S∈P} → SimpleGraph I) (holdH : ∀ S,oldH S≤C.graph T) :
    let C0 := C.selectedResidual hA P F hbranch
    ∀ e∈C.connectorPool hA hT oldH holdH Subtype.val ∪
      C0.connectorPool le_rfl hT (fun _ : {r // r∈selectedRoots P} => C0.graph T)
        (fun _ => le_rfl) (O.chosenFilled Q),
      ∃ r x y,x∈Fnew.branch r ∧ y∈Fnew.branch r ∧ e=s(x,y) := by
  classical
  intro C0 e he
  rcases Finset.mem_union.mp he with he|he
  · obtain ⟨S,_,he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨x,y,hx,hy,rfl⟩ := C.connectorEdges_endpoints hA hT (oldH S) (holdH S) S.val he
    let r : {r // r∈selectedRoots P} := ⟨Sum.inl S,by simp [selectedRoots]⟩
    refine ⟨r,x,y,?_,?_,rfl⟩
    · rw [hnew r]
      exact ⟨r.val,Finset.mem_insert_self _ _,by change x∈F.branch S;rw [hbranch];exact hx⟩
    · rw [hnew r]
      exact ⟨r.val,Finset.mem_insert_self _ _,by change y∈F.branch S;rw [hbranch];exact hy⟩
  · obtain ⟨r,_,he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨x,y,hx,hy,rfl⟩ := C0.connectorEdges_endpoints le_rfl hT (C0.graph T) le_rfl (O.chosenFilled Q r) he
    exact ⟨r,x,y,by rw [hnew];exact hx,by rw [hnew];exact hy,rfl⟩

end ClusterFamily
end MinorFreeSpanners
