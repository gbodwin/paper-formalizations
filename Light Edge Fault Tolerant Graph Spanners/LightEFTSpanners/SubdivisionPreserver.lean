import LightEFTSpanners.SubdivisionCleanColor

/-! The actual unit-edge certificate for the Section4.1 lower construction.
Unlike the invalid Section4.2 certificate, this does not claim that every
branch vertex remains connected after faults; only the core must remain linked. -/
namespace LightEFTSpanners.ParallelSubdivision
open SimpleGraph Finset
variable {V I : Type*} [Fintype V] [Fintype I] (C : SimpleGraph V)
attribute [local instance] Classical.propDecidable

/-- One localized bad base edge can be bypassed in a bridgeless connected base,
so the chosen subdivision color still connects every original core vertex. -/
theorem core_reachable_after_one_color_fault [Nonempty C.edgeSet]
    (hC : C.Preconnected) (hbridge : ∀ e∈C.edgeSet,¬C.IsBridge e)
    (F : Finset (Sym2 (Vertex (I:=I) C))) (j : I)
    (hj : (F ∩ (colorGraph C j).edgeFinset).card≤1) :
    ∀ u v : V,(afterFaults (graph (I:=I) C) F).Reachable (Sum.inl u) (Sum.inl v) := by
  classical
  obtain ⟨d,hd⟩ := exists_bad_base_edge C F j hj
  let D := C.deleteEdges {(d:Sym2 V)}
  have hD : D.Preconnected :=
    (hC.connected_deleteEdges_of_not_isBridge (hbridge d d.property)).preconnected
  have transport {u v : V} (p : D.Walk u v) :
      (afterFaults (graph (I:=I) C) F).Reachable (Sum.inl u) (Sum.inl v) := by
    induction p with
    | nil => exact Reachable.refl _
    | @cons u v z huv p ih =>
      have hbase : C.Adj u v := (deleteEdges_adj.mp huv).1
      let e : C.edgeSet := ⟨s(u,v),(mem_edgeSet C).mpr hbase⟩
      have hed : e≠d := by
        intro heq
        apply (deleteEdges_adj.mp huv).2
        exact Set.mem_singleton_iff.mpr (congrArg Subtype.val heq)
      exact (base_edge_reachable C hbase j F (hd e hed)).trans ih
  intro u v
  obtain ⟨p⟩ := hD u v
  exact transport p

def coreGraph (D : SimpleGraph V) : SimpleGraph (Vertex (I:=I) C) where
  Adj a b := match a,b with
    | Sum.inl u,Sum.inl v => D.Adj u v
    | _,_ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> simp [adj_comm]⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

/-- F parallel subdivisions of a bridgeless connected base preserve arbitrary
added core-to-core edges against fewer than 2F faults. The conclusion is the
full actual connectivity-preserver definition, not just core connectivity. -/
theorem unit_graph_isFTPreserver [Nonempty C.edgeSet]
    (hC : C.Preconnected) (hbridge : ∀ e∈C.edgeSet,¬C.IsBridge e)
    (D : SimpleGraph V) (q : ℕ) (hq : q<2*Fintype.card I) :
    IsFTConnectivityPreserver (graph (I:=I) C ⊔ coreGraph C D) (graph (I:=I) C) q := by
  classical
  refine ⟨le_sup_left,?_⟩
  intro F hF u v
  obtain ⟨j,hj⟩ := exists_clean_color C F (hF.trans_lt hq)
  have hcore := core_reachable_after_one_color_fault C hC hbridge F j hj
  have hedge (a b : Vertex (I:=I) C)
      (hab : (afterFaults (graph (I:=I) C ⊔ coreGraph C D) F).Adj a b) :
      (afterFaults (graph (I:=I) C) F).Reachable a b := by
    obtain ⟨hab,hnot⟩ := deleteEdges_adj.mp hab
    rcases hab with hab | hab
    · exact (deleteEdges_adj.mpr ⟨hab,hnot⟩).reachable
    · cases a with
      | inl a =>
        cases b with
        | inl b => exact hcore a b
        | inr b => exact False.elim hab
      | inr a =>
        cases b <;> exact False.elim hab
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact Reachable.refl _
    | @cons a b z hab p ih => exact (hedge a b hab).trans ih
  · exact Reachable.mono (afterFaults_mono le_sup_left F)
end LightEFTSpanners.ParallelSubdivision
