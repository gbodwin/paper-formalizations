import LightEFTSpanners.NativePartitionLower

namespace LightEFTSpanners.MultigraphCuts
open Finset SimpleGraph
variable {V E : Type*} [Fintype E]
attribute [local instance] Classical.propDecidable

/-- Pairwise disjoint actual connected spanning subgraphs force the complete
partition budget. Acyclicity is not needed for this necessary direction. -/
theorem native_connected_packing_partitionCriterion (G : Graph V E) {k : ℕ}
    (F : Fin k → Set E)
    (hconn : ∀ c,(G.restrict (F c)).toSimpleGraph.Connected)
    (hdis : Pairwise (fun i j => Disjoint (F i) (F j))) :
    TreePartitionCriterion G k := by
  classical
  intro m label hsurj
  let C : Fin k → Finset E := fun c =>
    (actualPartitionCrossings G label).filter (fun e => e∈F c)
  have hc (c : Fin k) : m-1≤(C c).card := by
    have h := connected_partition_crossing_lower (G.restrict (F c)) (hconn c) label hsurj
    simpa only [actualPartitionCrossings_restrict] using h
  have hd : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint C := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    exact Set.disjoint_left.mp (hdis hij) (Finset.mem_filter.mp hei).2
      (Finset.mem_filter.mp hej).2
  have hs := Finset.sum_le_sum (s:=Finset.univ)
    (fun c (_ : c∈(Finset.univ : Finset (Fin k))) => hc c)
  have hsum : (∑ c : Fin k,(C c).card)≤(actualPartitionCrossings G label).card := by
    rw [← Finset.card_biUnion hd]
    apply Finset.card_le_card
    intro e he
    obtain ⟨c,_,hc⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_filter.mp hc).1
  have hconstant : (∑ _ : Fin k,(m-1))=k*(m-1) := by simp
  rw [hconstant] at hs
  exact hs.trans hsum
end LightEFTSpanners.MultigraphCuts
