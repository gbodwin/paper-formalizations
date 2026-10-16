import LightEFTSpanners.NativePackingExtension

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph
variable {V E : Type*} [Fintype E]
attribute [local instance] Classical.propDecidable

theorem treePartitionCriterion_mono (G : Graph V E) {j k : ℕ} (hjk : j≤k)
    (h : TreePartitionCriterion G k) : TreePartitionCriterion G j := by
  intro m label hsurj
  exact (Nat.mul_le_mul_right (m-1) hjk).trans (h m label hsurj)

/-- A true maximum is constructed from the inductive seed, and its last color
is then proved connected by the actual improving-countercase contradiction. -/
theorem exists_native_connected_residual (G : Graph V E) [Fintype G.vertexSet]
    [Nonempty G.vertexSet] {k : ℕ} (hp : TreePartitionCriterion G (k+1))
    (seed : E → Fin (k+1)) (hseed : earlierColorTrees G seed) :
    ∃ color : E → Fin (k+1),earlierColorTrees G color ∧
      (G.restrict {e | color e=Fin.last k}).toSimpleGraph.Connected := by
  obtain ⟨color,ht,hmax⟩ := exists_maximal_native_decomposition G
    (Nat.card G.vertexSet*Nat.card G.vertexSet) seed hseed
  let : Nonempty (G.restrict {e | color e=Fin.last k}).vertexSet :=
    inferInstanceAs (Nonempty G.vertexSet)
  refine ⟨color,ht,⟨?_⟩⟩
  exact maximal_native_last_reachable G color hp ht hmax

/-- Full finite induction: the actual partition crossing budget constructs
all earlier-color spanning trees, without a supplied seed or packing oracle.
The extra last color contains the unused original edge identities. -/
theorem exists_native_tree_coloring (G : Graph V E) [Fintype G.vertexSet]
    [Nonempty G.vertexSet] (k : ℕ) (hp : TreePartitionCriterion G k) :
    ∃ color : E → Fin (k+1),earlierColorTrees G color := by
  classical
  induction k with
  | zero =>
    refine ⟨fun _ => 0,?_⟩
    intro c
    exact Fin.elim0 c
  | succ k ih =>
    obtain ⟨seed,hseed⟩ := ih (treePartitionCriterion_mono G (Nat.le_succ k) hp)
    obtain ⟨color,ht,hconn⟩ := exists_native_connected_residual G hp seed hseed
    let : Finite (G.restrict {e | color e=Fin.last k}).vertexSet :=
      inferInstanceAs (Finite G.vertexSet)
    obtain ⟨F,hF,hbridge,hconnected,hcard⟩ :=
      exists_native_spanning_tree (G.restrict {e | color e=Fin.last k}) hconn
    have hcolor : ∀ e∈F,color e=Fin.last k := fun e he => (hF he).2
    have hEq : (G.restrict {e | color e=Fin.last k}).restrict F=G.restrict F := by
      rw [Graph.restrict_restrict]
      apply congrArg G.restrict
      exact Set.inter_eq_right.mpr (show F ⊆ {e | color e=Fin.last k} from hcolor)
    have htree : (∀ e∈(G.restrict F).edgeSet,(G.restrict F).IsBridge e) ∧
        (G.restrict F).toSimpleGraph.Connected :=
      (congrArg (fun K : Graph V E =>
        (∀ e∈K.edgeSet,K.IsBridge e) ∧ K.toSimpleGraph.Connected) hEq).mp ⟨hbridge,hconnected⟩
    exact ⟨extendTreeColor color F,
      extendTreeColor_earlier_trees G color ht F hcolor htree.1 htree.2⟩
end LightEFTSpanners.MultigraphCuts
