import LightEFTSpanners.SimpleNativeForestTransport

namespace LightEFTSpanners.EvenSplitting
open SimpleGraph MultigraphCuts
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

/-- The finite Eulerian forest packing on genuine simple graphs, obtained
from the constructed native packing, without a supplied family. -/
theorem exists_simple_eulerian_forest_packing (G : SimpleGraph V) (k : ℕ)
    (heven : ∀ v,Even (G.degree v)) :
    ∃ T : Fin k → SimpleGraph V,
      (∀ c,T c≤G ∧ (T c).IsAcyclic) ∧
      Pairwise (fun c d => Disjoint (T c) (T d)) ∧
      ∀ c a b,G.IsEdgeReachable (2*k) a b → (T c).Reachable a b := by
  classical
  have hd (v : V) : Even (nativeDegree (Graph.ofSimpleGraph G) v) := by
    rw [ofSimpleGraph_nativeDegree]
    rcases heven v with ⟨n,hn⟩
    exact ⟨n,by exact_mod_cast hn⟩
  obtain ⟨A,hA,hdisj,hjoin⟩ := exists_native_eulerian_forest_packing
    (Graph.ofSimpleGraph G) k rfl hd
  refine ⟨fun c => G ⊓ fromEdgeSet (A c),?_,?_,?_⟩
  · intro c
    refine ⟨inf_le_left,?_⟩
    exact (nativeSelectedIso G (A c)).isAcyclic_iff.mp
      (acyclic_of_all_edges_bridge _ (hA c).2)
  · intro c d hcd
    apply SimpleGraph.disjoint_left.mpr
    intro x y hc hd
    exact Set.disjoint_left.mp (hdisj hcd) hc.2.1 hd.2.1
  · intro c a b hab
    have h := hjoin c ⟨a,Set.mem_univ _⟩ ⟨b,Set.mem_univ _⟩
      ((ofSimpleGraph_faultConnected_iff G).mpr hab)
    exact h.map (nativeSelectedIso G (A c)).toHom
end LightEFTSpanners.EvenSplitting
