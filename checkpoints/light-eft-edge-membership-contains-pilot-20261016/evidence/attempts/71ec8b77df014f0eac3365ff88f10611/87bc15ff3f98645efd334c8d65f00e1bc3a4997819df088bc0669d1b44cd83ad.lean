import LightEFTSpanners.SimpleEulerianForestPacking
import LightEFTSpanners.SubdivisionDegrees
import LightEFTSpanners.SeededSubdivisionPacking

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners HostCounting ParallelSubdivision EvenSplitting
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Construct the doubled-subdivision forest family internally, then use its
actual projected hosts in the optimum-seeded greedy output. The seed baseline
one and the exact positive surplus h are retained. No forest packing is supplied. -/
theorem seeded_output_from_constructed_packing {G Q : SimpleGraph V}
    {w : Sym2 V → ℝ} {eps : ℝ} {f k h q : ℕ}
    (hQ : IsMinimumFTPreserver G Q w q) (hbudget : 2*f+h≤q+1)
    (hw0 : ∀ e,0≤w e) (hw : ∀ e∈G.edgeSet,0<w e)
    (hf : 0<f) (hk : 0<k) (heps : 0<eps) (hh : 0<h) :
    IsEFTSpanner G (output G Q w ((1+eps)*(2*k-1)) f) w ((1+eps)*(2*k-1)) f ∧
    competitiveLightness (output G Q w ((1+eps)*(2*k-1)) f) Q w ≤
      1+8*(f:ℝ)*(8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹))/h := by
  classical
  obtain ⟨T,hT,hd,hc⟩ := exists_simple_eulerian_forest_packing
    (graph (I:=Fin 2) Q) (q+1) (doubled_even_degrees Q)
  apply seeded_output_from_doubled_packing hQ (univ : Finset (Fin (q+1))) T
    (fun i _ => (hT i).1)
  · intro i _ j _ hij
    exact hd hij
  · simp
  · exact hbudget
  · exact fun i _ a b hab => hc i a b hab
  · exact hw0
  · exact hw
  · exact hf
  · exact hk
  · exact heps
  · exact hh
end LightEFTSpanners
