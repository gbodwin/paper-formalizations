import LightEFTSpanners.NativeCompleteInput

/-! Attained native seed and explicit parameters. The pruning loss L+1 stays
visible. The sampling estimate requires positive working fault budget. -/
namespace LightEFTSpanners.NativeWeighted
open Finset LightSpanners
open scoped NNReal
variable {V E : Type*} [Fintype V] [Fintype E]
attribute [local instance] Classical.propDecidable

/-- Adding back the seed turns the candidate estimate into a total-weight
bound without division by the multiplicity or optimum. -/
theorem nativeOutput_weight_charge {G : Graph V E} {w : E → ℝ≥0} {H : Finset E}
    {q : ℕ} {T : Fin (q+1) → Finset E} (hb : SeedForestBudget G w H q T)
    (t : ℝ≥0) (ht : 2 < t+1) (f h : ℕ) (hf : 0 < f) (hcount : 2*f+h ≤ q+1)
    (hH : H ⊆ inputEdges G) :
    (h : ℝ) * (totalWeight w (nativeOutput G w t f H) : ℝ) ≤
      ((h : ℝ) + 8*(f : ℝ)*(extremalLightness (Fintype.card V) ((t+1 : ℝ≥0) : ℝ)+1)) *
        (totalWeight w H : ℝ) := by
  classical
  have hc := native_candidate_extremal_charge hb t ht f h hf hcount (nativeInput G w)
    (nativeInput_nodup G w) (nativeInput_sorted G w) hH (fun e he => (mem_nativeInput G w e).mp he)
  have hs : totalWeight w (nativeOutput G w t f H \ H) + totalWeight w H =
      totalWeight w (nativeOutput G w t f H) := sum_sdiff (nativeOutput_seed_subset G w t f H)
  have hs' : (totalWeight w (nativeOutput G w t f H \ H) : ℝ) + (totalWeight w H : ℝ) =
      (totalWeight w (nativeOutput G w t f H) : ℝ) := by exact_mod_cast hs
  change (h : ℝ) * (totalWeight w (nativeOutput G w t f H \ H) : ℝ) ≤ _ at hc
  nlinarith

/-- The canonical complete native greedy output, seeded by an attained
q-connectivity optimum. h=0 is permitted here, but gives only a vacuous charge. -/
theorem exists_native_minimum_output (G : Graph V E) (w : E → ℝ≥0)
    (t : ℝ≥0) (ht : 1 < t) (f q h : ℕ) (hf : 0 < f) (hcount : 2*f+h ≤ q+1) :
    ∃ H : Finset E,
      IsConnectivityPreserver G (inputEdges G) H q ∧
      totalWeight w H = minimumPreserverWeight G w (inputEdges G) q ∧
      IsEFTSpanner G w (inputEdges G) (nativeOutput G w t f H) f t ∧
      (h : ℝ) * (totalWeight w (nativeOutput G w t f H) : ℝ) ≤
        ((h : ℝ) + 8*(f : ℝ)*(extremalLightness (Fintype.card V) ((t+1 : ℝ≥0) : ℝ)+1)) *
          (minimumPreserverWeight G w (inputEdges G) q : ℝ) := by
  obtain ⟨H,T,hH,hw,_,hb,_⟩ := exists_minimum_seed_budget G w q
  refine ⟨H,hH,hw,nativeOutput_sound G w t ht.le f H hH.1,?_⟩
  simpa only [hw] using nativeOutput_weight_charge hb t (by linarith) f h hf hcount hH.1

/-- A ratio-form coefficient requires h>0, never a positive seed weight. -/
theorem exists_native_minimum_output_bound (G : Graph V E) (w : E → ℝ≥0)
    (t : ℝ≥0) (ht : 1 < t) (f q h : ℕ) (hf : 0 < f) (hh : 0 < h)
    (hcount : 2*f+h ≤ q+1) :
    ∃ S : Finset E, IsEFTSpanner G w (inputEdges G) S f t ∧
      (totalWeight w S : ℝ) ≤
        (1 + 8*(f : ℝ)*(extremalLightness (Fintype.card V) ((t+1 : ℝ≥0) : ℝ)+1)/(h : ℝ)) *
          (minimumPreserverWeight G w (inputEdges G) q : ℝ) := by
  obtain ⟨H,_,_,hs,hc⟩ := exists_native_minimum_output G w t ht f q h hf hcount
  refine ⟨nativeOutput G w t f H,hs,?_⟩
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  apply (mul_le_mul_iff_right₀ hh').mp
  calc
    (totalWeight w (nativeOutput G w t f H) : ℝ) * h ≤
        ((h : ℝ) + 8*(f : ℝ)*(extremalLightness (Fintype.card V) ((t+1 : ℝ≥0) : ℝ)+1)) *
          (minimumPreserverWeight G w (inputEdges G) q : ℝ) := by simpa only [mul_comm] using hc
    _ = _ := by field_simp; ring

/-- Concrete positive-budget parameters q=2f and h=1 satisfy host coverage. -/
theorem exists_native_baseline (G : Graph V E) (w : E → ℝ≥0)
    (t : ℝ≥0) (ht : 1 < t) (f : ℕ) (hf : 0 < f) :
    ∃ S : Finset E, IsEFTSpanner G w (inputEdges G) S f t ∧
      (totalWeight w S : ℝ) ≤
        (1 + 8*(f : ℝ)*(extremalLightness (Fintype.card V) ((t+1 : ℝ≥0) : ℝ)+1)) *
          (minimumPreserverWeight G w (inputEdges G) (2*f) : ℝ) := by
  simpa using exists_native_minimum_output_bound G w t ht f (2*f) 1 hf (by omega) (by omega)

/-- A safe all-budget specialization uses max 1 f as the working budget.
For f=0 the comparator is opt_2, not opt_0; the positive sampler is not
applied with f=0 and its factor is not silently replaced by zero. -/
theorem exists_native_baseline_all_budgets (G : Graph V E) (w : E → ℝ≥0)
    (t : ℝ≥0) (ht : 1 < t) (f : ℕ) :
    ∃ S : Finset E, IsEFTSpanner G w (inputEdges G) S f t ∧
      (totalWeight w S : ℝ) ≤
        (1 + 8*(max 1 f : ℝ)*(extremalLightness (Fintype.card V) ((t+1 : ℝ≥0) : ℝ)+1)) *
          (minimumPreserverWeight G w (inputEdges G) (2*max 1 f) : ℝ) := by
  obtain ⟨S,hS,hw⟩ := exists_native_baseline G w t ht (max 1 f) (by omega)
  exact ⟨S,hS.fault_mono (le_max_right _ _),by exact_mod_cast hw⟩

/-- Zero optimum is handled directly for f≤q, including f=q=0 and h=0.
This assertion does not rely on the sampling bound or divide by any weight. -/
theorem exists_native_zero_optimum (G : Graph V E) (w : E → ℝ≥0)
    (t : ℝ≥0) (f q : ℕ) (hf : f ≤ q)
    (hz : minimumPreserverWeight G w (inputEdges G) q = 0) :
    ∃ H : Finset E, IsEFTSpanner G w (inputEdges G) H f t ∧ totalWeight w H = 0 := by
  obtain ⟨H,hH,hw,_⟩ := minimumPreserverWeight_attained G w (inputEdges G) q
  have hzero := hw.trans hz
  exact ⟨H,zero_weight_preserver_isEFT hH hf hzero t,hzero⟩

end LightEFTSpanners.NativeWeighted
