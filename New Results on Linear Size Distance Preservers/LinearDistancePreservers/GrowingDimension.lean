import LinearDistancePreservers.CoefficientBounds
import LinearDistancePreservers.RateFactorBounds

namespace LinearDistancePreservers.TheoremFourGeneral
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- Convert the literal natural power into its exponential budget. -/
theorem dimension_power_le_exp {d : ℕ} (hd : 0 < d) {x : ℝ}
    (h : 100*(d:ℝ)^3*Real.log d ≤ x) : (d:ℝ)^(100*d^3) ≤ Real.exp x := by
  have hdR : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hh : (d:ℝ)^(100*d^3) = Real.exp (Real.log d * (100*d^3:ℕ)) := by
    exact (Real.rpow_natCast (d:ℝ) (100*d^3)).symm.trans (Real.rpow_def_of_pos hdR _)
  rw [hh]
  apply Real.exp_le_exp.mpr
  push_cast
  convert h using 1 <;> ring

/-- Absorb a coefficient bounded by exp(x) into one additional unit of
exponential loss. All multiplication and sign conditions are explicit. -/
theorem absorb_coefficient {P E K c x : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hK : K ≤ Real.exp x) (hc : c ≤ 4) (hx : 0 ≤ x)
    (hbound : P*Real.exp (-c*x) ≤ K*E) :
    P*Real.exp (-5*x) ≤ E := by
  have hloss : Real.exp (-5*x) ≤ Real.exp (-c*x)*Real.exp (-x) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hc hx
    linarith
  calc
    _ ≤ P*(Real.exp (-c*x)*Real.exp (-x)) := mul_le_mul_of_nonneg_left hloss hP
    _ = (P*Real.exp (-c*x))*Real.exp (-x) := by ring
    _ ≤ (K*E)*Real.exp (-x) := mul_le_mul_of_nonneg_right hbound (Real.exp_nonneg _)
    _ ≤ (Real.exp x*E)*Real.exp (-x) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK hE) (Real.exp_nonneg _)
    _ = E := by rw [mul_right_comm,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]

/-- A genuinely uniform growing-dimensional rate in a weaker range. The
single numerical condition controls all dimension-dependent constants.
This does not assert the source's much larger d=O(sqrt(log N)) range. -/
theorem displayed_lower_bound_growing {N T : ℕ} (n : ℕ)
    (hT : 2 ≤ T) (hTN : T ≤ N)
    (hbudget : 100*((n+3 : ℕ):ℝ)^3*Real.log (n+3) ≤ Real.sqrt (Real.log N)) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        (N : ℝ)^((2 : ℝ)/(n+4)) *
          (T : ℝ)^((((2*(n+3)+1)*(n+2) : ℕ) : ℝ)/(((n+3)*(n+4) : ℕ) : ℝ)) *
          Real.exp (-5*Real.sqrt (Real.log N)) ≤ (H.edgeFinset.card : ℝ) := by
  have hpow := dimension_power_le_exp (d := n+3) (by omega : 0 < n+3)
    (x := Real.sqrt (Real.log N)) (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hbudget)
  have hc : 4*((n+2 : ℕ):ℝ)/((n+3 : ℕ):ℝ) ≤ 4 := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr (show 0<n+3 by omega))).mpr
    push_cast
    linarith only [(Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))]
  have hC := LatticeCaps.explicitRadius_bound n
  have hroot := HigherProduct.rateFactor_root_dimension_bound (by omega : 3 ≤ n+3) hC
  obtain ⟨G,S,hS,hG⟩ := displayed_lower_bound_explicit n hT hTN
  refine ⟨G,S,hS,?_⟩
  intro H hHG hpres
  have hb := hG H hHG hpres
  apply absorb_coefficient (hbound := hb)
  · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      (Real.rpow_nonneg (Nat.cast_nonneg T) _)
  · exact Nat.cast_nonneg _
  · exact hroot.trans hpow
  · exact hc
  · exact Real.sqrt_nonneg _

end LinearDistancePreservers.TheoremFourGeneral
