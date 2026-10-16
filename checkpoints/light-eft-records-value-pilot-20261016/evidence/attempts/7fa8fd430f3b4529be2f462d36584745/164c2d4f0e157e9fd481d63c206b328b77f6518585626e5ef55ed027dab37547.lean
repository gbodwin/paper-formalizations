import LightEFTSpanners.ExtremalMultipleHosts
import LightEFTSpanners.ConstructedSeededPacking
import LightEFTSpanners.RoundedCompetition

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners HostCounting ParallelSubdivision EvenSplitting
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Exact-quantity multiple-host bound for the actual optimum-seeded output.
The required Eulerian forests and all their hosts are constructed internally. -/
theorem constructed_output_extremal_vote_bound {G Q : SimpleGraph V}
    {w : Sym2 V → ℝ} {eps : ℝ} {f k h q : ℕ}
    (hQ : IsMinimumFTPreserver G Q w q) (hbudget : 2*f+h≤q+1)
    (hw0 : ∀ e,0≤w e) (hw : ∀ e∈G.edgeSet,0<w e)
    (hf : 0<f) (hk : 0<k) (heps : 0<eps) (hh : 0<h) :
    IsEFTSpanner G (output G Q w ((1+eps)*(2*k-1)) f) w ((1+eps)*(2*k-1)) f ∧
    competitiveLightness (output G Q w ((1+eps)*(2*k-1)) f) Q w ≤
      1+8*(f:ℝ)*extremalLightness (Fintype.card V) ((1+eps)*(2*k-1)+1)/h := by
  classical
  obtain ⟨T,hT,hd,hc⟩ := exists_simple_eulerian_forest_packing
    (graph (I:=Fin 2) Q) (q+1) (doubled_even_degrees Q)
  obtain ⟨F,hF,hreach,hcong⟩ := exists_projected_forest_family Q
    (univ : Finset (Fin (q+1))) T (fun i _ => (hT i).1) (fun i _ j _ hij => hd hij)
  have hQG : Q≤G := hQ.1.1
  have ht : (1:ℝ)≤(1+eps)*(2*k-1) := by linarith [actual_threshold_gt_two heps hk]
  have hsp := output_isEFTSpanner G Q hQG w ((1+eps)*(2*k-1)) f ht hw0
  refine ⟨hsp,?_⟩
  have hL := extremalLightness_nonneg (Fintype.card V) (actual_threshold_gt_two heps hk)
  by_cases hz : totalWeight Q w=0
  · simp only [competitiveLightness,hz,div_zero]
    positivity
  · have hQnn : 0≤totalWeight Q w := by unfold totalWeight;exact sum_nonneg (fun e _ => hw0 e)
    have hQpos : 0<totalWeight Q w := lt_of_le_of_ne hQnn (Ne.symm hz)
    obtain ⟨B,hB⟩ := output_has_blocking G Q hQG w ((1+eps)*(2*k-1)) f (by linarith)
    apply forest_extremal_vote_bound (seed_le_output G Q w _ f) hQpos hB
      univ F (fun i hi => (hF i hi).2) (fun i hi => (hF i hi).1)
    · intro a b hab habQ
      have hr := hQ.1.missing_edge_edgeReachable (hsp.1 hab) habQ
      have hall (i : Fin (q+1)) : (F i).Reachable a b := by
        apply hreach i (mem_univ _) a b
        apply hc i
        simpa [mul_comm] using core_edge_connectivity (I:=Fin 2) Q hr
      simpa [hall] using hbudget
    · intro e _
      simpa [hosts] using hcong e
    · exact fun e he => hw e (edgeSet_mono hsp.1 he)
    · exact hf
    · exact hk
    · exact heps
    · exact hh

/-- The corrected exact extremal comparison at real higher competition.
The argument is stretch+1; exact floor arithmetic and baseline1 are retained. -/
theorem exists_eft_spanner_extremal_rounded_bound (G : SimpleGraph V) (w : Sym2 V → ℝ)
    {eps eta : ℝ} {f k : ℕ}
    (hw0 : ∀ e,0≤w e) (hw : ∀ e∈G.edgeSet,0<w e)
    (hf : 0<f) (hk : 0<k) (heps : 0<eps) (heta : 0<eta) :
    ∃ Q H : SimpleGraph V,IsMinimumFTPreserver G Q w ⌊(2+eta)*(f:ℝ)⌋₊ ∧
      IsEFTSpanner G H w ((1+eps)*(2*k-1)) f ∧
      competitiveLightness H Q w ≤
        1+8*extremalLightness (Fintype.card V) ((1+eps)*(2*k-1)+1)/eta := by
  obtain ⟨Q,hQ⟩ := exists_minimum_preserver G w ⌊(2+eta)*(f:ℝ)⌋₊
  have hbudget : 2*f+(⌊eta*(f:ℝ)⌋₊+1)≤⌊(2+eta)*(f:ℝ)⌋₊+1 := by
    rw [rounded_fault_budget f heta.le]
    omega
  obtain ⟨hs,hb⟩ := constructed_output_extremal_vote_bound hQ hbudget hw0 hw hf hk heps (Nat.succ_pos _)
  refine ⟨Q,output G Q w ((1+eps)*(2*k-1)) f,hQ,hs,hb.trans ?_⟩
  exact rounded_charging_le f heta (extremalLightness_nonneg _ (actual_threshold_gt_two heps hk))
end LightEFTSpanners
