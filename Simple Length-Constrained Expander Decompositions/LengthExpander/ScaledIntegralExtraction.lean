import LengthExpander.DemandExtraction
import Mathlib.Algebra.BigOperators.Field

/-! Rescale an integral demand with enlarged budgets, then use the proved
support-preserving extraction. The resulting size loss is explicit. -/
namespace LengthExpander
open Finset
variable {V : Type*} [Fintype V]

theorem exists_integral_of_scaled_budgets (C : Demand V) (A : NodeWeight V)
    (b : ℕ) (hb : 0 < b) (hC : Respects C (fun u => b*A u)) :
    ∃ D : Demand V, Respects D A ∧ (∀ u v, 0 < D u v → 0 < C u v) ∧
      demandSize C ≤ 2*b*demandSize D := by
  classical
  let F : V → V → ℝ := fun u v => (C u v : ℝ)/b
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hrow (u : V) : (∑ v, F u v) ≤ A u := by
    simp only [F,← sum_div,← Nat.cast_sum]
    apply (div_le_iff₀ hb').mpr
    have hc : ((∑ v, C u v : ℕ) : ℝ) ≤ (b:ℝ)*A u := by exact_mod_cast hC.1 u
    nlinarith
  have hcol (v : V) : (∑ u, F u v) ≤ A v := by
    simp only [F,← sum_div,← Nat.cast_sum]
    apply (div_le_iff₀ hb').mpr
    have hc : ((∑ u, C u v : ℕ) : ℝ) ≤ (b:ℝ)*A v := by exact_mod_cast hC.2 v
    nlinarith
  obtain ⟨D,hD,hs,hm⟩ := exists_integral_support_extraction F A
    (fun _ _ => div_nonneg (Nat.cast_nonneg _) hb'.le) hrow hcol
  refine ⟨D,hD,?_,?_⟩
  · intro u v huv
    have hf := hs u v huv
    have hc : (0 : ℝ) < C u v := (div_pos_iff_of_pos_right hb').mp hf
    exact_mod_cast hc
  · have hm' : (demandSize C : ℝ)/(b:ℝ) ≤ 2*(demandSize D : ℝ) := by
      simpa only [F,← sum_div,← Nat.cast_sum,demandSize] using hm
    have hm'' := (div_le_iff₀ hb').mp hm'
    have hc : (demandSize C : ℝ) ≤ 2*(b:ℝ)*(demandSize D:ℝ) := by nlinarith
    exact_mod_cast hc

end LengthExpander
