import LightEFTSpanners.ConstructedVotingWeight
import LightEFTSpanners.ConnectivityOptimum

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset LightSpanners
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- The seed optimum and all forest hosts are chosen internally. The conclusion
concerns the actual empirical tape's output on its own accuracy event. Finite
existence of the optimum does not assert a polynomial implementation. -/
theorem exists_optimum_voting_good_event (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (q f h k : ℕ) (eps : ℝ) (hbudget : 2*f+h≤q+1)
    (hf : 0<f) (hh : 0<h) (hk : 0<k) (heps : 0<eps)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ Q : SimpleGraph V,IsMinimumFTPreserver G Q w q ∧
      ∃ F : Fin (q+1) → SimpleGraph V,
        (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
        ∀ tape : Tape V (ForestComponentIndex F),
          AccurateTrace Q.edgeFinset w ((1+eps)*(2*k-1)) f
            (componentEligible univ F) (componentHost F) tape h (input G Q w) →
          IsEFTSpanner G (output G Q w ((1+eps)*(2*k-1))
            (componentEligible univ F) (componentHost F) tape h) w ((1+eps)*(2*k-1)) f ∧
          competitiveLightness (output G Q w ((1+eps)*(2*k-1))
            (componentEligible univ F) (componentHost F) tape h) Q w≤
            1+64*(f:ℝ)*extremalLightness (Fintype.card V) ((1+eps)*(2*k-1)+1)/h := by
  obtain ⟨Q,hQ⟩ := exists_minimum_preserver G w q
  obtain ⟨F,hF,hout⟩ := exists_constructed_voting_weight hQ.1 hbudget w eps k hf hh hk heps hw hwpos
  refine ⟨Q,hQ,F,hF,?_⟩
  intro tape hacc
  obtain ⟨hs,hb⟩ := hout tape hacc
  refine ⟨hs,?_⟩
  have hL := extremalLightness_nonneg (Fintype.card V) (actual_threshold_gt_two heps hk)
  by_cases hz : totalWeight Q w=0
  · simp only [competitiveLightness,hz,div_zero]
    positivity
  · have hn : 0≤totalWeight Q w := by unfold totalWeight;exact sum_nonneg (fun e _ => hw e)
    have hp : 0<totalWeight Q w := lt_of_le_of_ne hn (Ne.symm hz)
    exact (div_le_iff₀ hp).mpr hb

/-- Corrected Algorithm2's actual one-vote output has baseline1 plus64f times
lambda at stretch+1, on the same reached-state accuracy event as correctness. -/
theorem exists_algorithm_two_good_event (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (f k : ℕ) (eps : ℝ) (hf : 0<f) (hk : 0<k) (heps : 0<eps)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ Q : SimpleGraph V,IsMinimumFTPreserver G Q w (2*f) ∧
      ∃ F : Fin (2*f+1) → SimpleGraph V,
        (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
        ∀ tape : Tape V (ForestComponentIndex F),
          AccurateTrace Q.edgeFinset w ((1+eps)*(2*k-1)) f
            (componentEligible univ F) (componentHost F) tape 1 (input G Q w) →
          IsEFTSpanner G (output G Q w ((1+eps)*(2*k-1))
            (componentEligible univ F) (componentHost F) tape 1) w ((1+eps)*(2*k-1)) f ∧
          competitiveLightness (output G Q w ((1+eps)*(2*k-1))
            (componentEligible univ F) (componentHost F) tape 1) Q w≤
            1+64*(f:ℝ)*extremalLightness (Fintype.card V) ((1+eps)*(2*k-1)+1) := by
  simpa only [Nat.cast_one,div_one] using
    exists_optimum_voting_good_event G w (2*f) f 1 k eps (by omega) hf (by decide) hk heps hw hwpos

/-- Corrected Algorithm3 with exact floor rounding. The actual output's
competitive lightness retains baseline1, works for every eta>0 and still uses
the corrected extremal argument stretch+1. Concentration remains separate. -/
theorem exists_algorithm_three_good_event (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (f k : ℕ) (eps eta : ℝ) (hf : 0<f) (hk : 0<k) (heps : 0<eps) (heta : 0<eta)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ Q : SimpleGraph V,IsMinimumFTPreserver G Q w ⌊(2+eta)*(f:ℝ)⌋₊ ∧
      ∃ F : Fin (⌊(2+eta)*(f:ℝ)⌋₊+1) → SimpleGraph V,
        (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
        ∀ tape : Tape V (ForestComponentIndex F),
          AccurateTrace Q.edgeFinset w ((1+eps)*(2*k-1)) f
            (componentEligible univ F) (componentHost F) tape (⌊eta*(f:ℝ)⌋₊+1) (input G Q w) →
          IsEFTSpanner G (output G Q w ((1+eps)*(2*k-1))
            (componentEligible univ F) (componentHost F) tape (⌊eta*(f:ℝ)⌋₊+1)) w ((1+eps)*(2*k-1)) f ∧
          competitiveLightness (output G Q w ((1+eps)*(2*k-1))
            (componentEligible univ F) (componentHost F) tape (⌊eta*(f:ℝ)⌋₊+1)) Q w≤
            1+64*extremalLightness (Fintype.card V) ((1+eps)*(2*k-1)+1)/eta := by
  have hbudget : 2*f+(⌊eta*(f:ℝ)⌋₊+1)≤⌊(2+eta)*(f:ℝ)⌋₊+1 := by
    rw [rounded_fault_budget f heta.le];omega
  obtain ⟨Q,hQ,F,hF,hout⟩ := exists_optimum_voting_good_event G w ⌊(2+eta)*(f:ℝ)⌋₊
    f (⌊eta*(f:ℝ)⌋₊+1) k eps hbudget hf (Nat.succ_pos _) hk heps hw hwpos
  refine ⟨Q,hQ,F,hF,?_⟩
  intro tape hacc
  obtain ⟨hs,hb⟩ := hout tape hacc
  refine ⟨hs,hb.trans ?_⟩
  have hL := extremalLightness_nonneg (Fintype.card V) (actual_threshold_gt_two heps hk)
  have hc := rounded_charging_le f heta (mul_nonneg (show (0:ℝ)≤8 by norm_num) hL)
  convert hc using 1 <;> ring
end LightEFTSpanners.SampledGreedy
