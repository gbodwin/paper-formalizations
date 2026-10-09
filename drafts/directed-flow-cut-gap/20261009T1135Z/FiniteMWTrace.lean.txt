import DirectedFlowCutGap.MultiplicativeWeights

/-!
# Multiplicative-weights bounds for retained finite traces

The selected cuts may depend on fresh random input at every call. In
particular, equal cost vectors need not produce equal cuts. These lemmas use
the actual retained counts and a proved potential bound, without extending a
randomized or partial oracle to a deterministic total selector.
-/
namespace DirectedFlowCutGap.FiniteMWTrace
open scoped BigOperators

variable {E : Type*} [Fintype E]

/-- The logarithmic count estimate only needs the actual terminal potential. -/
theorem count_log_bound (w : E → ℝ) (α η : ℝ)
    (hw : ∀ e, 0 < w e) (hα : 0 < α) (hη : 0 ≤ η)
    (k : E → ℕ) (t : ℕ)
    (hpotential : mwPotential w (mwCost w α η k) ≤
      (∑ e, w e) * (1 + η) ^ t) (e : E) :
    (k e : ℝ) * Real.log (1 + η / (w e * α)) ≤
      (t : ℝ) * η + Real.log ((∑ a, w a) / w e) := by
  have hW : 0 < ∑ a, w a := lt_of_lt_of_le (hw e)
    (Finset.single_le_sum (fun a _ => (hw a).le) (Finset.mem_univ e))
  have hbase : 0 < 1 + η := by linarith
  have hpow := (mwCost_mul_weight_le w α η hw hα hη k e).trans hpotential
  have hlog := Real.log_le_log
    (mul_pos (mwCost_pos w α η hw hα hη k e) (hw e)) hpow
  rw [Real.log_mul (ne_of_gt (mwCost_pos w α η hw hα hη k e)) (hw e).ne',
    Real.log_mul hW.ne' (pow_ne_zero t hbase.ne')] at hlog
  simp only [mwCost, Real.log_pow] at hlog
  have heta := Real.log_le_sub_one_of_pos hbase
  have hmul := mul_le_mul_of_nonneg_left heta (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
  rw [Real.log_div hW.ne' (hw e).ne']
  nlinarith

/-- A terminal potential bound controls arbitrary actual selection counts. -/
theorem count_le (w : E → ℝ) (α η : ℝ)
    (hw : ∀ e, 0 < w e) (hα : 0 < α) (hη : 0 < η)
    (hscale : ∀ e, η ≤ w e * α) (k : E → ℕ) (t : ℕ)
    (hpotential : mwPotential w (mwCost w α η k) ≤
      (∑ e, w e) * (1 + η) ^ t) (e : E) :
    (k e : ℝ) ≤
      2 * (w e * α) * ((t : ℝ) + Real.log ((∑ a, w a) / w e) / η) := by
  have hx : 0 < w e * α := mul_pos (hw e) hα
  have hz : 0 ≤ η / (w e * α) := (div_pos hη hx).le
  have hz1 : η / (w e * α) ≤ 1 := (div_le_one hx).2 (hscale e)
  have hlower := mul_le_mul_of_nonneg_left (mw_half_le_log_one_add hz hz1)
    (Nat.cast_nonneg (k e))
  have hbound := hlower.trans (count_log_bound w α η hw hα hη.le k t hpotential e)
  apply (mul_le_mul_iff_left₀ hη).mp
  calc
    (k e : ℝ) * η = ((k e : ℝ) * (η / (w e * α) / 2)) *
        (2 * (w e * α)) := by field_simp [(hw e).ne', hα.ne']
    _ ≤ ((t : ℝ) * η + Real.log ((∑ a, w a) / w e)) * (2 * (w e * α)) :=
      mul_le_mul_of_nonneg_right hbound (mul_nonneg (by norm_num) hx.le)
    _ = (2 * (w e * α) *
        ((t : ℝ) + Real.log ((∑ a, w a) / w e) / η)) * η := by
      field_simp [hη.ne']

/-- The finite-horizon marginal bound is pointwise on every successful trace. -/
theorem marginal_le_four (w : E → ℝ) (α η : ℝ)
    (hw : ∀ e, 0 < w e) (hα : 0 < α) (hη : 0 < η)
    (hscale : ∀ e, η ≤ w e * α) (k : E → ℕ) (t : ℕ) (ht : 0 < t)
    (hpotential : mwPotential w (mwCost w α η k) ≤
      (∑ e, w e) * (1 + η) ^ t) (e : E)
    (hhorizon : Real.log ((∑ a, w a) / w e) ≤ η * (t : ℝ)) :
    (k e : ℝ) / (t : ℝ) ≤ 4 * w e * α := by
  have hdiv : Real.log ((∑ a, w a) / w e) / η ≤ (t : ℝ) := by
    apply (div_le_iff₀ hη).2
    simpa [mul_comm] using hhorizon
  have hbound := count_le w α η hw hα hη hscale k t hpotential e
  have hmul := mul_le_mul_of_nonneg_left hdiv
    (show 0 ≤ 2 * (w e * α) from mul_nonneg (by norm_num) (mul_pos (hw e) hα).le)
  apply (div_le_iff₀ (Nat.cast_pos.mpr ht)).2
  nlinarith

end DirectedFlowCutGap.FiniteMWTrace
