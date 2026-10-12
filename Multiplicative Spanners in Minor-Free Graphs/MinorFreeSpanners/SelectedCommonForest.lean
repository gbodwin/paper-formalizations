import MinorFreeSpanners.SelectedLabelPartition
import MinorFreeSpanners.CoveringClusterConnectivity

/-! Join the forest actually returned by the branching phase to the final
selected root partition. Extending before quotienting, then retaining all
singleton residual edges, keeps the original forest adjacency exactly. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem forest_residual_endpoints {I : Type*} (Q H : SimpleGraph I) (R : Set I)
    (hreach : H.Reachable=(withinVertices Q R).Reachable) :
    ∀ i j,H.Adj i j → i∈R := by
  intro i j hij
  have hr := hij.reachable
  rw [hreach] at hr
  obtain ⟨p⟩ := hr
  cases p with
  | nil => exact (hij.ne rfl).elim
  | cons h _ => exact h.2.1

namespace ClusterFamily
variable {I V : Type*} [Fintype I] {A G T : SimpleGraph V}
variable {w : Sym2 V → ℝ} {D E : ℝ}

 theorem exists_selected_common_tree (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (hcover : ∀ x,∃ i,x∈C.branch i) (hT : T.Connected)
    (R : Set I) (H : SimpleGraph I) (hHQ : H≤C.graph T) (hforest : H.IsAcyclic)
    (hreach : H.Reachable=(withinVertices (C.graph T) R).Reachable)
    (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (hres : ∀ i,i∉P.biUnion id → i∈R) :
    ∃ K : SimpleGraph (SelectedResidualIndex P),
      K≤(C.selectedResidual hA P F hbranch).graph T ∧ K.IsTree ∧
      ∀ i j : {i // i∉P.biUnion id},K.Adj (Sum.inr i) (Sum.inr j) ↔ H.Adj i.val j.val := by
  classical
  have : Nonempty V := hT.nonempty
  obtain ⟨i,_⟩ := hcover (Classical.arbitrary V)
  have : Nonempty I := ⟨i⟩
  have hc := C.graph_connected_of_cover hcover hT
  have hQ : (C.graph T).Connected := ⟨fun i j => by
    obtain ⟨p,_⟩ := hc i (mem_univ i) j (mem_univ j)
    exact ⟨p⟩⟩
  obtain ⟨T₀,hHT,hTQ,hT₀,hrestrict⟩ := exists_tree_preserving_chosen_forest
    (C.graph T) H R hQ hHQ hforest (hreach) (forest_residual_endpoints _ _ _ hreach)
  obtain ⟨K,hKQ,hK,hKres⟩ := C.exists_selected_residual_tree hA P F hbranch T₀ hT₀ hTQ
  refine ⟨K,hKQ,hK,?_⟩
  intro i j
  rw [hKres]
  have he := congrArg (fun M : SimpleGraph I => M.Adj i.val j.val) hrestrict
  simpa only [withinVertices,hres i.val i.property,hres j.val j.property,and_true] using Iff.of_eq he

end ClusterFamily
end MinorFreeSpanners
