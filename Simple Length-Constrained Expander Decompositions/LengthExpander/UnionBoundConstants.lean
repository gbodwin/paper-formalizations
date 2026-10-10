import LengthExpander.UnionSparsity

/-! Remove the ceiling and doubled-copy terms from the repaired union loss,
yielding an explicit constant in the paper's s*|A|^(2/s) order. -/
namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

theorem union_loss_bound {N s : ℕ} (hN : 0 < N) (hs : 2 ≤ s) :
    (16:ℝ)*(densityBudget (2*N) s+1:ℕ) ≤ 512*(s:ℝ)*(N:ℝ)^(2/(s:ℝ)) := by
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hsr : (2:ℝ) ≤ s := by exact_mod_cast hs
  have hsp : (0:ℝ) < s := by linarith
  have he : (0:ℝ) ≤ 2/(s:ℝ) := by positivity
  have he1 : (2:ℝ)/s ≤ 1 := (div_le_one hsp).mpr hsr
  have hp : (1:ℝ) ≤ (2*(N:ℝ))^(2/(s:ℝ)) := Real.one_le_rpow (by linarith) he
  have htwo : (2:ℝ)^(2/(s:ℝ)) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) he1
  have hpow : (2*(N:ℝ))^(2/(s:ℝ)) ≤ 2*(N:ℝ)^(2/(s:ℝ)) := by
    rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg N)]
    exact mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hx : (2:ℝ) ≤ 8*(s:ℝ)*(2*(N:ℝ))^(2/(s:ℝ)) := by nlinarith
  have hc := Nat.ceil_lt_add_one
    (by positivity : (0:ℝ) ≤ 8*(s:ℝ)*(2*(N:ℝ))^(2/(s:ℝ)))
  have hc' : (⌈8*(s:ℝ)*(2*(N:ℝ))^(2/(s:ℝ))⌉₊ : ℝ)+1 ≤
      2*(8*(s:ℝ)*(2*(N:ℝ))^(2/(s:ℝ))) := by linarith
  unfold densityBudget
  push_cast
  have hm := mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ) ≤ 256*(s:ℝ))
  nlinarith

/-- Explicit improved union bound: loss at most 512s*|A|^(2/s).
The input is any finite nonnegative cut sequence of positive total volume. -/
theorem union_sparseCut_explicit {V : Type*} [Fintype V]
    (G : SimpleGraph V) (U : Sym2 V → ℕ) (A : NodeWeight V)
    (w : EdgeLength V) (h : ℝ) (s : ℕ) (Cs : List (EdgeLength V))
    (hCs : NonnegativeCuts Cs) (hh : 0 ≤ h) (hs : 2 ≤ s)
    (hvol : 0 < sequenceVolume G A h s w Cs) :
    SparseCut G U w A (2*h) (((s:ℝ)-1)/2)
      (512*(s:ℝ)*(weightSize A:ℝ)^(2/(s:ℝ))*cutCost G U (totalCut Cs) /
        (sequenceVolume G A h s w Cs:ℝ)) (unionCut Cs s) := by
  have hc := union_sparseCut G U A w h s Cs hCs hh hs hvol
  have hA : 0 < weightSize A := hc.2.1.trans_le (volume_le_weightSize G w (unionCut Cs s) A (2*h) (((s:ℝ)-1)/2))
  have hl := union_loss_bound hA hs
  have hcost := cutCost_nonneg G U (nonnegativeCuts_total hCs)
  have hphi := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl hcost)
    (Nat.cast_nonneg (sequenceVolume G A h s w Cs))
  refine ⟨hc.1,hc.2.1,hc.2.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hphi (Nat.cast_nonneg _)

end LengthExpander
