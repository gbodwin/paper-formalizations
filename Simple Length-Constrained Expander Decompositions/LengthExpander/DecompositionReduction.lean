import LengthExpander.FiniteTermination

/-! The correct maximality-to-decomposition reduction. The unscaled sum
is the expanding output. A bound on a larger scaled sum bounds its cost;
we do not assume expansion is monotone under length increases. -/
namespace LengthExpander
open Finset SimpleGraph
variable {V : Type*} [Fintype V]

theorem cutCost_scale (G : SimpleGraph V) (U : Sym2 V → ℕ)
    (C : EdgeLength V) (q : ℝ) :
    cutCost G U (fun e => q * C e) = q * cutCost G U C := by
  classical
  simp only [cutCost, mul_sum]
  apply sum_congr rfl
  intro e he
  ring

theorem cutCost_le_scaled (G : SimpleGraph V) (U : Sym2 V → ℕ)
    {C : EdgeLength V} {q : ℝ} (hC : ∀ e, 0 ≤ C e) (hq : 1 ≤ q) :
    cutCost G U C ≤ cutCost G U (fun e => q * C e) := by
  rw [cutCost_scale]
  have hc := cutCost_nonneg G U hC
  nlinarith

/-- Conditional reduction used by Theorem 5.1. The hypothesis `unionBound`
is a precisely exposed remaining obligation; it is not assumed to be proved
by this module. Finite maximality and the returned decomposition are constructed. -/
theorem exists_decomposition_of_union_cost_bound
    (G : SimpleGraph V) (U : Sym2 V → ℕ) (A : NodeWeight V)
    (w : EdgeLength V) (h s φ κ q : ℝ)
    (hh : 0 ≤ h) (hs : 1 ≤ s) (hq : 1 ≤ q)
    (unionBound : ∀ Cs, SparseSequence G U A h s φ w Cs →
      cutCost G U (fun e => q * totalCut Cs e) ≤ κ * φ * (weightSize A : ℝ)) :
    ∃ C, IsDecomposition G U w A h s φ κ C := by
  obtain ⟨Cs,hCs,hExp,_hLen⟩ := exists_finite_maximal_sequence G U A h s φ hh hs w
  have hnonneg := sequence_total_nonneg hCs
  refine ⟨totalCut Cs, hnonneg, ?_, hExp⟩
  exact (cutCost_le_scaled G U hnonneg hq).trans (unionBound Cs hCs)

/-- Parameter multiplier in the paper is at least one for s≥2. -/
theorem rescaling_ge_one {s : ℝ} (hs : 2 ≤ s) : 1 ≤ 1 + 1/(s-1) := by
  have hp : 0 < s-1 := by linarith
  exact le_add_of_nonneg_right (div_nonneg (by norm_num) hp.le)

end LengthExpander
