import LightEFTSpanners.NativePackingInduction

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph
variable {V E : Type*} [Fintype E]
attribute [local instance] Classical.propDecidable

/-- The finite native multigraph partition condition constructs k genuinely
edge-disjoint spanning trees of original edge identities. No initial tree
family, maximal coloring, or replacement path is an input. -/
theorem exists_native_tree_packing (G : Graph V E) [Fintype G.vertexSet]
    [Nonempty G.vertexSet] (k : ℕ) (hp : TreePartitionCriterion G k) :
    ∃ F : Fin k → Set E,
      (∀ c,F c⊆G.edgeSet ∧
        (∀ e∈(G.restrict (F c)).edgeSet,(G.restrict (F c)).IsBridge e) ∧
        (G.restrict (F c)).toSimpleGraph.Connected ∧
        Nat.card (F c)+1=Nat.card G.vertexSet) ∧
      Pairwise (fun i j => Disjoint (F i) (F j)) := by
  classical
  obtain ⟨color,ht⟩ := exists_native_tree_coloring G k hp
  let F : Fin k → Set E := fun c => (actualColorClass G color c.castSucc : Set E)
  have hF (c : Fin k) : F c⊆G.edgeSet := by
    intro e he
    exact ((mem_actualColorClass G color c.castSucc e).mp he).1
  have htree (c : Fin k) :
      (∀ e∈(G.restrict (F c)).edgeSet,(G.restrict (F c)).IsBridge e) ∧
        (G.restrict (F c)).toSimpleGraph.Connected := by
    have hEq := actualColorClass_graph G color c.castSucc
    exact (congrArg (fun K : Graph V E =>
      (∀ e∈K.edgeSet,K.IsBridge e) ∧ K.toSimpleGraph.Connected) hEq).mpr (ht c)
  refine ⟨F,?_,?_⟩
  · intro c
    let : Finite (G.restrict (F c)).vertexSet := inferInstanceAs (Finite G.vertexSet)
    have hc := native_tree_card (G.restrict (F c)) (htree c).1 (htree c).2
    have hEdge : (G.restrict (F c)).edgeSet=F c := Set.inter_eq_right.mpr (hF c)
    change Nat.card (G.restrict (F c)).edgeSet+1=Nat.card G.vertexSet at hc
    rw [hEdge] at hc
    exact ⟨hF c,(htree c).1,(htree c).2,hc⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro e hei hej
    have hi := ((mem_actualColorClass G color i.castSucc e).mp hei).2
    have hj := ((mem_actualColorClass G color j.castSucc e).mp hej).2
    exact hij (Fin.castSucc_inj.mp (hi.symm.trans hj))
end LightEFTSpanners.MultigraphCuts
