import LightEFTSpanners.ConstructedSeededPacking
import LightEFTSpanners.SeededExtremalForests
import LightEFTSpanners.ExactExtremalDefinition
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.Real.Sqrt

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners HostCounting ParallelSubdivision EvenSplitting
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- The actual optimum-2f-seeded greedy output has square-root fault dependence.
All doubled forests, projected hosts and heavy/light assignments are constructed. -/
theorem constructed_output_extremal_sqrt_bound {G Q : SimpleGraph V}
    {w : Sym2 V → ℝ} {eps : ℝ} {f k : ℕ}
    (hQ : IsMinimumFTPreserver G Q w (2*f))
    (hw0 : ∀ e,0≤w e) (hw : ∀ e∈G.edgeSet,0<w e)
    (hf : 0<f) (hk : 0<k) (heps : 0<eps) :
    IsEFTSpanner G (output G Q w ((1+eps)*(2*k-1)) f) w ((1+eps)*(2*k-1)) f ∧
    competitiveLightness (output G Q w ((1+eps)*(2*k-1)) f) Q w ≤
      1+16*(Nat.sqrt f:ℝ)*(extremalLightness (Fintype.card V) ((1+eps)*(2*k-1)+1)) := by
  classical
  obtain ⟨T,hT,hd,hc⟩ := exists_simple_eulerian_forest_packing
    (graph (I:=Fin 2) Q) (2*f+1) (doubled_even_degrees Q)
  obtain ⟨F,hF,hreach,hcong⟩ := exists_projected_forest_family Q
    (univ : Finset (Fin (2*f+1))) T (fun i _ => (hT i).1)
    (fun i _ j _ hij => hd hij)
  apply seeded_output_from_extremal_forests hQ univ F
    (fun i hi => (hF i hi).2) (fun i hi => (hF i hi).1)
  · simp
  · rfl
  · intro i hi a b hab
    apply hreach i hi a b
    apply hc i
    simpa [mul_comm] using core_edge_connectivity (I:=Fin 2) Q hab
  · intro e _
    simpa [hosts] using hcong e
  · exact hw0
  · exact hw
  · exact hf
  · exact hk
  · exact heps
  · exact Nat.sqrt_pos.mpr hf
  · exact Nat.sqrt_le_self f
  · have hh := Nat.sqrt_le_add f
    have hr := Nat.sqrt_pos.mpr hf
    nlinarith

/-- Finite simple-graph existence at exact competition 2f. The additive seed
baseline and total division convention are explicit, including zero optimum. -/
theorem exists_eft_spanner_extremal_sqrt_bound (G : SimpleGraph V) (w : Sym2 V → ℝ)
    {eps : ℝ} {f k : ℕ}
    (hw0 : ∀ e,0≤w e) (hw : ∀ e∈G.edgeSet,0<w e)
    (hf : 0<f) (hk : 0<k) (heps : 0<eps) :
    ∃ Q H : SimpleGraph V,IsMinimumFTPreserver G Q w (2*f) ∧
      IsEFTSpanner G H w ((1+eps)*(2*k-1)) f ∧
      competitiveLightness H Q w ≤
        1+16*Real.sqrt (f:ℝ)*(extremalLightness (Fintype.card V) ((1+eps)*(2*k-1)+1)) := by
  obtain ⟨Q,hQ⟩ := exists_minimum_preserver G w (2*f)
  obtain ⟨hs,hb⟩ := constructed_output_extremal_sqrt_bound hQ hw0 hw hf hk heps
  refine ⟨Q,output G Q w ((1+eps)*(2*k-1)) f,hQ,hs,hb.trans ?_⟩
  have hsq : (Nat.sqrt f:ℝ)≤Real.sqrt (f:ℝ) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    exact_mod_cast Nat.sqrt_le' f
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num : (0:ℝ)≤16))
    (extremalLightness_nonneg (Fintype.card V) (actual_threshold_gt_two heps hk))
  linarith
end LightEFTSpanners
