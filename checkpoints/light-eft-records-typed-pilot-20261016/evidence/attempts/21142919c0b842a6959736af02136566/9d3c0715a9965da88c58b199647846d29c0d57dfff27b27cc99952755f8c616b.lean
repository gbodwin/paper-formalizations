import LightEFTSpanners.NativeResidualExtremal
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.Real.Sqrt

/-! Heavy/light aggregation for the native original-ID output. The sample and
cycle lemmas are constructed, and their pruning loss L+1 is retained. -/
namespace LightEFTSpanners.NativeWeighted
open Finset LightSpanners
open scoped NNReal
variable {V E : Type*} [Fintype V] [Fintype E]
attribute [local instance] Classical.propDecidable

/-- Both candidate subfamilies use one full traced blocker family. Heavy
candidates use residual cap r and one host; light candidates use cap f and
2r+1 hosts. This is a weight inequality, with no zero-denominator convention. -/
theorem native_heavy_light_candidate_bound {G : Graph V E} {w : E → ℝ≥0}
    {H : Finset E} {f : ℕ} {T : Fin (2*f+1) → Finset E}
    (hb : SeedForestBudget G w H (2*f) T) (t : ℝ≥0) (ht : 2 < t+1)
    (hf : 0 < f) (r : ℕ) (hr : 0 < r) (hrf : r ≤ f) (hfr : f ≤ r*(2*r+1))
    (es : List E) (hn : es.Nodup) (hsort : es.Pairwise (fun e d => w d ≤ w e))
    (hH : H ⊆ inputEdges G) (hinput : ∀ e ∈ es, e ∈ inputEdges G) :
    (totalWeight w (nativeGreedy G w t f H es \ H) : ℝ) ≤
      16*(r : ℝ)*(extremalLightness (Fintype.card V) ((t+1 : ℝ≥0) : ℝ)+1)*(totalWeight w H : ℝ) := by
  classical
  obtain ⟨block,hblock,_⟩ := exists_traced_blockers G w t f H es hsort
  let U := nativeGreedy G w t f H es \ H
  let heavy := U.filter fun e => (block e \ H).card ≤ r
  let light := U.filter fun e => ¬ (block e \ H).card ≤ r
  let L := extremalLightness (Fintype.card V) ((t+1 : ℝ≥0) : ℝ)
  have hc : ∀ e ∈ U, (block e).card ≤ f := fun e he => (hblock.sampling e he).1
  have hh := native_residual_candidate_charge hb t ht f f 1 r hr (by omega) es hn hsort hH hinput
    heavy (filter_subset _ _) block hblock
    (fun e he => (card_le_card inter_subset_left).trans (hc e (mem_filter.mp he).1))
    (fun e he => (mem_filter.mp he).2)
  have hl := native_residual_candidate_charge hb t ht f (f-r) (2*r+1) f hf (by omega) es hn hsort hH hinput
    light (filter_subset _ _) block hblock
    (fun e he => native_light_seed_cap (block e) H f r (hc e (mem_filter.mp he).1) (mem_filter.mp he).2)
    (fun e he => (card_le_card sdiff_subset).trans (hc e (mem_filter.mp he).1))
  simp only [Nat.cast_one,one_mul] at hh
  change (totalWeight w heavy : ℝ) ≤ 8*(r : ℝ)*(L+1)*(totalWeight w H : ℝ) at hh
  change ((2*r+1 : ℕ) : ℝ)*(totalWeight w light : ℝ) ≤ 8*(f : ℝ)*(L+1)*(totalWeight w H : ℝ) at hl
  have hL : 0 ≤ L := extremalLightness_nonneg _ (by exact_mod_cast ht)
  have hfrR : (f : ℝ) ≤ (r : ℝ)*(2*(r : ℝ)+1) := by exact_mod_cast hfr
  have hscale : 0 ≤ 8*(L+1)*(totalWeight w H : ℝ) := by positivity
  have hfscale := mul_le_mul_of_nonneg_right hfrR hscale
  have hlb : (totalWeight w light : ℝ) ≤ 8*(r : ℝ)*(L+1)*(totalWeight w H : ℝ) := by
    push_cast at hl
    have hden : 0 < 2*(r : ℝ)+1 := by positivity
    nlinarith
  have hsum : (totalWeight w heavy : ℝ)+(totalWeight w light : ℝ) = (totalWeight w U : ℝ) := by
    exact_mod_cast native_heavy_light_weight_partition w U H block r
  change (totalWeight w U : ℝ) ≤ _
  nlinarith

/-- Seed add-back is exact and valid even when its weight is zero. -/
theorem nativeOutput_heavy_light_bound {G : Graph V E} {w : E → ℝ≥0}
    {H : Finset E} {f : ℕ} {T : Fin (2*f+1) → Finset E}
    (hb : SeedForestBudget G w H (2*f) T) (t : ℝ≥0) (ht : 1 < t)
    (hf : 0 < f) (r : ℕ) (hr : 0 < r) (hrf : r ≤ f) (hfr : f ≤ r*(2*r+1))
    (hH : H ⊆ inputEdges G) :
    (totalWeight w (nativeOutput G w t f H) : ℝ) ≤
      (1+16*(r : ℝ)*(extremalLightness (Fintype.card V) ((t+1 : ℝ≥0) : ℝ)+1))*(totalWeight w H : ℝ) := by
  classical
  have hc := native_heavy_light_candidate_bound hb t (by linarith) hf r hr hrf hfr
    (nativeInput G w) (nativeInput_nodup G w) (nativeInput_sorted G w) hH
    (fun e he => (mem_nativeInput G w e).mp he)
  have hs : totalWeight w (nativeOutput G w t f H \ H)+totalWeight w H =
      totalWeight w (nativeOutput G w t f H) := sum_sdiff (nativeOutput_seed_subset G w t f H)
  have hs' : (totalWeight w (nativeOutput G w t f H \ H) : ℝ)+(totalWeight w H : ℝ) =
      (totalWeight w (nativeOutput G w t f H) : ℝ) := by exact_mod_cast hs
  change (totalWeight w (nativeOutput G w t f H \ H) : ℝ) ≤ _ at hc
  nlinarith

/-- Nat.sqrt f satisfies every integer heavy/light condition for positive f. -/
theorem native_sqrt_parameters (f : ℕ) (hf : 0 < f) :
    0 < Nat.sqrt f ∧ Nat.sqrt f ≤ f ∧ f ≤ Nat.sqrt f*(2*Nat.sqrt f+1) := by
  refine ⟨Nat.sqrt_pos.mpr hf,Nat.sqrt_le_self f,?_⟩
  have h := Nat.sqrt_le_add f
  have hr := Nat.sqrt_pos.mpr hf
  nlinarith

/-- The native square-root bound for the canonical output seeded by an
attained optimum. No simple-graph or positive-weight assumption is made. -/
theorem exists_native_sqrt_output (G : Graph V E) (w : E → ℝ≥0)
    (t : ℝ≥0) (ht : 1 < t) (f : ℕ) (hf : 0 < f) :
    ∃ H : Finset E, IsConnectivityPreserver G (inputEdges G) H (2*f) ∧
      totalWeight w H = minimumPreserverWeight G w (inputEdges G) (2*f) ∧
      IsEFTSpanner G w (inputEdges G) (nativeOutput G w t f H) f t ∧
      (totalWeight w (nativeOutput G w t f H) : ℝ) ≤
        (1+16*(Nat.sqrt f : ℝ)*(extremalLightness (Fintype.card V) ((t+1 : ℝ≥0) : ℝ)+1))*
          (minimumPreserverWeight G w (inputEdges G) (2*f) : ℝ) := by
  obtain ⟨H,T,hH,hw,_,hb,_⟩ := exists_minimum_seed_budget G w (2*f)
  obtain ⟨hr,hrf,hfr⟩ := native_sqrt_parameters f hf
  refine ⟨H,hH,hw,nativeOutput_sound G w t ht.le f H hH.1,?_⟩
  simpa only [hw] using nativeOutput_heavy_light_bound hb t ht hf (Nat.sqrt f) hr hrf hfr hH.1

/-- Real square-root specialization retains the seed baseline and L+1. -/
theorem exists_native_sqrt_bound (G : Graph V E) (w : E → ℝ≥0)
    (t : ℝ≥0) (ht : 1 < t) (f : ℕ) (hf : 0 < f) :
    ∃ S : Finset E, IsEFTSpanner G w (inputEdges G) S f t ∧
      (totalWeight w S : ℝ) ≤
        (1+16*Real.sqrt (f : ℝ)*(extremalLightness (Fintype.card V) ((t+1 : ℝ≥0) : ℝ)+1))*
          (minimumPreserverWeight G w (inputEdges G) (2*f) : ℝ) := by
  obtain ⟨H,_,_,hS,hw⟩ := exists_native_sqrt_output G w t ht f hf
  refine ⟨nativeOutput G w t f H,hS,hw.trans ?_⟩
  have hsq : (Nat.sqrt f : ℝ) ≤ Real.sqrt (f : ℝ) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    exact_mod_cast Nat.sqrt_le' f
  have hL : 0 ≤ extremalLightness (Fintype.card V) ((t+1 : ℝ≥0) : ℝ) :=
    extremalLightness_nonneg _ (by exact_mod_cast (show 2 < t+1 by linarith))
  apply mul_le_mul_of_nonneg_right _ (NNReal.coe_nonneg _)
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) (by positivity)

/-- The corrected numerical paper specialization now has sqrt(f), rather
than the earlier linear-f baseline. The additive pruning cost remains in 9. -/
theorem exists_native_paper_sqrt (G : Graph V E) (w : E → ℝ≥0)
    (eps : ℝ≥0) (k f : ℕ) (heps : 0 < eps) (hk : 0 < k) (hf : 0 < f) :
    ∃ S : Finset E, IsEFTSpanner G w (inputEdges G) S f (nativePaperStretch eps k) ∧
      (totalWeight w S : ℝ) ≤
        (1+16*Real.sqrt (f : ℝ)*(9+2048/(eps : ℝ)*(Fintype.card V : ℝ)^((k : ℝ)⁻¹)))*
          (minimumPreserverWeight G w (inputEdges G) (2*f) : ℝ) := by
  obtain ⟨S,hS,hw⟩ := exists_native_sqrt_bound G w (nativePaperStretch eps k)
    (nativePaperStretch_gt_one heps hk) f hf
  refine ⟨S,hS,hw.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (NNReal.coe_nonneg _)
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left (nativePaper_extremal_envelope (Fintype.card V) heps hk) (by positivity)

/-- At zero optimum the constructed positive-budget output itself has weight
zero. This is stronger than defining a ratio with zero denominator. -/
theorem exists_native_sqrt_zero (G : Graph V E) (w : E → ℝ≥0)
    (t : ℝ≥0) (ht : 1 < t) (f : ℕ) (hf : 0 < f)
    (hz : minimumPreserverWeight G w (inputEdges G) (2*f) = 0) :
    ∃ H : Finset E, IsEFTSpanner G w (inputEdges G) (nativeOutput G w t f H) f t ∧
      totalWeight w (nativeOutput G w t f H) = 0 := by
  obtain ⟨H,_,_,hS,hw⟩ := exists_native_sqrt_output G w t ht f hf
  rw [hz,NNReal.coe_zero,mul_zero] at hw
  exact ⟨H,hS,by exact_mod_cast (le_antisymm hw (NNReal.coe_nonneg _))⟩

end LightEFTSpanners.NativeWeighted
