import LightEFTSpanners.SubdivisionCleanColor
import LightEFTSpanners.MissingEdgeConnectivity

namespace LightEFTSpanners.ParallelSubdivision
open SimpleGraph Finset
variable {V I : Type*} [Fintype V] [Fintype I] (C : SimpleGraph V)
attribute [local instance] Classical.propDecidable

/-- Actual base edges touched by a failed half-edge of the selected color. -/
noncomputable def badBaseIds (F : Finset (Sym2 (Vertex (I:=I) C))) (j : I) :
    Finset C.edgeSet := univ.filter (fun d =>
      ∃ a : V, a∈(d:Sym2 V) ∧ s(Sum.inl a,Sum.inr (d,j))∈F)

noncomputable def badBaseEdges (F : Finset (Sym2 (Vertex (I:=I) C))) (j : I) :
    Finset (Sym2 V) := (badBaseIds C F j).map (Function.Embedding.subtype _)

/-- Each touched base edge can be charged injectively to a distinct actual
failed subdivision edge of that color. Faults that are nonedges do not count. -/
theorem badBaseEdges_card_le (F : Finset (Sym2 (Vertex (I:=I) C))) (j : I) :
    (badBaseEdges C F j).card ≤ (F ∩ (colorGraph C j).edgeFinset).card := by
  classical
  rw [badBaseEdges,card_map]
  have hp (d : {d // d∈badBaseIds C F j}) :
      ∃ a : V, a∈(d.val:Sym2 V) ∧ s(Sum.inl a,Sum.inr (d.val,j))∈F :=
    (mem_filter.mp d.property).2
  let a (d : {d // d∈badBaseIds C F j}) : V := Classical.choose (hp d)
  have ha (d : {d // d∈badBaseIds C F j}) :
      a d∈(d.val:Sym2 V) ∧ s(Sum.inl (a d),Sum.inr (d.val,j))∈F :=
    Classical.choose_spec (hp d)
  let phi : {d // d∈badBaseIds C F j} →
      {e // e∈F ∩ (colorGraph C j).edgeFinset} := fun d =>
    ⟨s(Sum.inl (a d),Sum.inr (d.val,j)),mem_inter.mpr
      ⟨(ha d).2,mem_edgeFinset.mpr ⟨(ha d).1,rfl⟩⟩⟩
  apply card_le_card_of_injective (f:=phi)
  intro d e heq
  apply Subtype.ext
  have hpair := congrArg Subtype.val heq
  change s(Sum.inl (a d),Sum.inr (d.val,j))=
    s(Sum.inl (a e),Sum.inr (e.val,j)) at hpair
  rcases Sym2.eq_iff.mp hpair with hpair | hpair
  · exact congrArg Prod.fst (Sum.inr.inj hpair.2)
  · cases hpair.1

omit [Fintype I] in
/-- Removing the projected failed base edges makes every remaining base edge
lift to an actual clean two-edge path of the chosen color. -/
theorem projected_faults_lift {u v : V}
    (F : Finset (Sym2 (Vertex (I:=I) C))) (j : I)
    (h : (afterFaults C (badBaseEdges C F j)).Reachable u v) :
    (afterFaults (graph (I:=I) C) F).Reachable (Sum.inl u) (Sum.inl v) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | @cons a b z hab p ih =>
    have hbase : C.Adj a b := hab.1
    apply (base_edge_reachable C hbase j F ?_).trans ih
    intro x hx hF
    let d : C.edgeSet := ⟨s(a,b),(mem_edgeSet C).mpr hbase⟩
    have hd : d∈badBaseIds C F j := mem_filter.mpr ⟨mem_univ _,x,hx,hF⟩
    apply (deleteEdges_adj.mp hab).2
    exact (show s(a,b)∈badBaseEdges C F j from mem_map.mpr ⟨d,hd,rfl⟩)
end LightEFTSpanners.ParallelSubdivision
