import LightEFTSpanners.NativePackingNecessity
import LightEFTSpanners.NativeTreePacking

namespace LightEFTSpanners.MultigraphCuts
variable {V E : Type*} [Fintype E]

/-- A family of edge-disjoint native spanning trees uses original edge
identities, all actual vertices, and native bridges (so parallel cycles count).
No partition inequality or maximality conclusion is part of the definition. -/
def HasNativeTreePacking (G : Graph V E) (k : ℕ) : Prop :=
  ∃ F : Fin k → Set E,
    (∀ c,F c⊆G.edgeSet ∧
      (∀ e∈(G.restrict (F c)).edgeSet,(G.restrict (F c)).IsBridge e) ∧
      (G.restrict (F c)).toSimpleGraph.Connected) ∧
    Pairwise (fun i j => Disjoint (F i) (F j))

/-- Finite native Nash-Williams/Tutte tree-packing equivalence. This covers
the printed Theorem22's positive integer domain and also k=0, with a finite
nonempty actual vertex set. It makes no algorithmic runtime assertion. -/
theorem native_tree_packing_iff_partitionCriterion (G : Graph V E)
    [Fintype G.vertexSet] [Nonempty G.vertexSet] (k : ℕ) :
    HasNativeTreePacking G k ↔ TreePartitionCriterion G k := by
  constructor
  · rintro ⟨F,hF,hdis⟩
    exact native_connected_packing_partitionCriterion G F (fun c => (hF c).2.2) hdis
  · intro hp
    obtain ⟨F,hF,hdis⟩ := exists_native_tree_packing G k hp
    exact ⟨F,fun c => ⟨(hF c).1,(hF c).2.1,(hF c).2.2.1⟩,hdis⟩
end LightEFTSpanners.MultigraphCuts
