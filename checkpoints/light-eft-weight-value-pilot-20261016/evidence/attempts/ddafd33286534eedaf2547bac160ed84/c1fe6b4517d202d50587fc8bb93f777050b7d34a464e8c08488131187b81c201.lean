import LightEFTSpanners.NativeTreeCertification
import LightEFTSpanners.NativeDeleteNonbridge

namespace LightEFTSpanners.MultigraphCuts
open Finset SimpleGraph
variable {V E : Type*} [Fintype E]
attribute [local instance] Classical.propDecidable

/-- Add an actual edge to an actual native spanning tree and remove a distinct
old edge that is a nonbridge after insertion. The resulting original-edge
subgraph is constructed, connected and genuinely acyclic, including parallel
identity semantics. The nonbridge condition is the explicit exchange premise. -/
theorem native_tree_exchange (G : Graph V E) [Finite G.vertexSet]
    (F : Finset E) (hF : (F:Set E)⊆G.edgeSet) {e d : E}
    (he : e∈G.edgeSet) (heF : e∉F) (hdF : d∈F)
    (hforest : ∀ q∈(G.restrict (F:Set E)).edgeSet,(G.restrict (F:Set E)).IsBridge q)
    (hconn : (G.restrict (F:Set E)).toSimpleGraph.Connected)
    (hnb : ¬(G.restrict ((insert e F:Finset E):Set E)).IsBridge d) :
    let T' := (G.restrict ((insert e F:Finset E):Set E)).deleteEdges {d}
    (∀ q∈T'.edgeSet,T'.IsBridge q) ∧ T'.toSimpleGraph.Connected ∧
      Nat.card T'.edgeSet=F.card := by
  classical
  let H := G.restrict ((insert e F:Finset E):Set E)
  let : Finite (G.restrict (F:Set E)).vertexSet := inferInstanceAs (Finite G.vertexSet)
  let : Finite H.vertexSet := inferInstanceAs (Finite G.vertexSet)
  let : Finite (H.deleteEdges {d}).vertexSet := inferInstanceAs (Finite G.vertexSet)
  have hHconn : H.toSimpleGraph.Connected := by
    let : Nonempty H.vertexSet := hconn.nonempty
    refine ⟨?_⟩
    intro a b
    apply (hconn.preconnected a b).mono
    intro x y hxy
    obtain ⟨hne,q,hq,hlink⟩ := hxy
    exact ⟨hne,q,mem_insert_of_mem hq,hlink⟩
  have hc := native_connected_delete_nonbridge H hnb hHconn
  have hHE : H.edgeSet=((insert e F:Finset E):Set E) := Set.inter_eq_right.mpr (by
    intro q hq
    rcases mem_insert.mp hq with rfl | hq
    · exact he
    · exact hF hq)
  have hTE : (G.restrict (F:Set E)).edgeSet=(F:Set E) := Set.inter_eq_right.mpr hF
  have htreecard := native_tree_card (G.restrict (F:Set E)) hforest hconn
  have hFcard : F.card+1=Nat.card G.vertexSet := by
    change Nat.card (G.restrict (F:Set E)).edgeSet+1=Nat.card G.vertexSet at htreecard
    simpa only [hTE,Nat.card_coe_set_eq,Set.ncard_coe_finset] using htreecard
  have hcard : Nat.card (H.deleteEdges {d}).edgeSet=F.card := by
    change Nat.card ↥(H.edgeSet\{d})=F.card
    rw [hHE]
    have heq : (((insert e F:Finset E):Set E)\{d})=((insert e F).erase d:Set E) := by
      ext q
      simp only [Set.mem_sdiff,mem_coe,mem_erase,Set.mem_singleton_iff]
      tauto
    rw [heq,Nat.card_coe_set_eq,Set.ncard_coe_finset,card_erase_of_mem (mem_insert_of_mem hdF),card_insert_of_notMem heF]
    omega
  have htree : ∀ q∈(H.deleteEdges {d}).edgeSet,(H.deleteEdges {d}).IsBridge q :=
    native_all_bridges_of_connected_card _ hc (by
      change Nat.card (H.deleteEdges {d}).edgeSet+1=Nat.card G.vertexSet
      omega)
  exact ⟨htree,hc,hcard⟩
end LightEFTSpanners.MultigraphCuts
