import LightEFTSpanners.SubdivisionConnectivity
import LightEFTSpanners.SubdivisionPackingProjection
import LightEFTSpanners.SeededForestPacking

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners HostCounting ParallelSubdivision
variable {V K : Type*} [Fintype V] [DecidableEq V] [DecidableEq K]
attribute [local instance] Classical.propDecidable

/-- The required upper-bound family can be supplied on the actual simple
2-subdivision of Q. Connectivity multiplication, actual walk projection, native
forest trimming and congestion two are discharged internally. Existence of
this edge-disjoint connectivity-preserving packing is still a hypothesis. -/
theorem seeded_output_from_doubled_packing {G Q : SimpleGraph V} {w : Sym2 V → ℝ}
    {eps : ℝ} {f k h q : ℕ} (hQ : IsMinimumFTPreserver G Q w q)
    (indices : Finset K) (T : K → SimpleGraph (Vertex (I:=Fin 2) Q))
    (hT : ∀ i∈indices,T i≤graph Q)
    (hdisj : (indices:Set K).PairwiseDisjoint T)
    (hnumber : q + 1 ≤ indices.card) (hbudget : 2*f+h≤q+1)
    (hconn : ∀ i∈indices,∀ a b,
      (graph (I:=Fin 2) Q).IsEdgeReachable (2*(q+1)) a b → (T i).Reachable a b)
    (hw0 : ∀ e,0≤w e) (hw : ∀ e∈G.edgeSet,0<w e)
    (hf : 0<f) (hk : 0<k) (heps : 0<eps) (hh : 0<h) :
    IsEFTSpanner G (output G Q w ((1+eps)*(2*k-1)) f) w ((1+eps)*(2*k-1)) f ∧
    competitiveLightness (output G Q w ((1+eps)*(2*k-1)) f) Q w ≤
      1+8*(f:ℝ)*(8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹))/h := by
  obtain ⟨F,hF,hreach,hcong⟩ := exists_projected_forest_family Q indices T hT hdisj
  apply seeded_output_from_connectivity_forests hQ indices F
    (fun i hi => (hF i hi).2) (fun i hi => (hF i hi).1) hnumber hbudget
  · intro i hi a b hab
    apply hreach i hi a b
    apply hconn i hi
    simpa [mul_comm] using core_edge_connectivity (I:=Fin 2) Q hab
  · intro e _
    simpa [hosts] using hcong e
  · exact hw0
  · exact hw
  · exact hf
  · exact hk
  · exact heps
  · exact hh
end LightEFTSpanners
