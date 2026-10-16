import LightEFTSpanners.ContractedCoreCuts
import LightEFTSpanners.MultigraphFaultConnectivity

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph Finset
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

/-- Embed an actual retained core vertex in the native contracted graph's
vertex set; the witness is its original preimage, not an added phantom vertex. -/
noncomputable def coreVertex (G : SimpleGraph V) (K : Finset V) (a : (K:Set V)) :
    ((Graph.ofSimpleGraph G).map (collapseOutside (K:Set V))).vertexSet :=
  ⟨some a,⟨a.val,Set.mem_univ _,by simp [collapseOutside,a.property]⟩⟩

/-- A minimal deficient core is genuinely fault-connected in its actual
complement contraction. Every allowed deletion is by original edge identity,
and the conclusion gives native surviving walks between retained vertices.
This is the connectivity conclusion used in CS09 Lemma 2.4. -/
theorem minimal_core_faultConnected (G : SimpleGraph V) (K : Finset V) {k : ℕ}
    (hmin : ∀ A : Finset V,A⊂K → A.Nonempty →
      k≤(ConnectivityCuts.edges G (A:Set V)).card)
    (a b : (K:Set V)) :
    FaultConnected ((Graph.ofSimpleGraph G).map (collapseOutside (K:Set V))) k
      (coreVertex G K a) (coreVertex G K b) := by
  apply faultConnected_of_cut_lower
  intro S ha hb
  exact minimal_core_contracted_cut_lower G K hmin a b S ha hb

/-- On actual simple graphs, the finite edge-identified semantics agrees
exactly with mathlib's native set-based edge reachability. -/
theorem ofSimpleGraph_faultConnected_iff (G : SimpleGraph V) {a b : V} {k : ℕ} :
    FaultConnected (Graph.ofSimpleGraph G) k ⟨a,Set.mem_univ _⟩ ⟨b,Set.mem_univ _⟩ ↔
      G.IsEdgeReachable k a b := by
  rw [faultConnected_iff_cut_lower,ConnectivityCuts.edgeReachable_iff_cut_lower]
  simp only [ofSimpleGraph_cut,Finset.toFinset_coe]

/-- In a genuine basic simple-graph instance with two different connectivity
islands, construct the proper core and its real contracted fault connectivity
from native graph hypotheses. No minimal-core or final-connectivity certificate
is supplied as an extra premise. -/
theorem exists_basic_faultConnected_core (G : SimpleGraph V) {u v : V} {k : ℕ}
    (hsep : ¬G.IsEdgeReachable k u v)
    (hbasic : ∀ a : V,∃ b : V,a≠b ∧ G.IsEdgeReachable k a b) :
    ∃ K : Finset V,K⊂univ ∧ 2≤K.card ∧
      (ConnectivityCuts.edges G (K:Set V)).card<k ∧
      (∀ a∈K,∀ b,G.IsEdgeReachable k a b → b∈K) ∧
      ∀ a b : (K:Set V),
        FaultConnected ((Graph.ofSimpleGraph G).map (collapseOutside (K:Set V))) k
          (coreVertex G K a) (coreVertex G K b) := by
  obtain ⟨K,hproper,htwo,hsmall,hclosed,hmin⟩ :=
    ConnectivityCuts.exists_basic_small_core G hsep hbasic
  exact ⟨K,hproper,htwo,hsmall,hclosed,fun a b => minimal_core_faultConnected G K hmin a b⟩
end LightEFTSpanners.MultigraphCuts
