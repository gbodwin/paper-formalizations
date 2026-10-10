import LinearDistancePreservers.QuantitativeRate

namespace LinearDistancePreservers.TheoremFourGeneral
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- Spend the explicit dimension loss directly rather than requiring it
to fit entirely inside the square-root loss. -/
theorem optimized_dimension_gain {d L : ℝ} (hd : 3 ≤ d) (hL : 0 ≤ L)
    (hcost : 200*d^5*Real.log d ≤ L)
    (hsize : 12*d^2 ≤ Real.sqrt L) :
    Real.sqrt L ≤ ((3*d*(1/d)+1/d-2/3)/(d*(d+1)))*L -
      4*Real.sqrt L-100*d^3*Real.log d := by
  have hd0 : 0<d := by linarith
  have hden : 0<2*d^2 := by positivity
  have hinv : (1/d)*d^2 = d := by field_simp [ne_of_gt hd0]
  have heta : 1/d^2 ≤ (3*d*(1/d)+1/d-2/3)/(d*(d+1)) := by
    have heq : 3*d*(1/d)+1/d-2/3 = 7/3+1/d := by field_simp; ring
    rw [heq]
    apply (div_le_div_iff₀ (sq_pos_of_pos hd0) (mul_pos hd0 (by linarith))).mpr
    rw [add_mul,hinv]
    nlinarith
  have hcost' : 100*d^3*Real.log d ≤ L/(2*d^2) := by
    apply (le_div_iff₀ hden).mpr
    convert hcost using 1 <;> ring
  have hx0 := Real.sqrt_nonneg L
  have hx2 := Real.sq_sqrt hL
  have hsize' : 6*Real.sqrt L ≤ L/(2*d^2) := by
    apply (le_div_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_right hsize hx0
    nlinarith
  have hgain := mul_le_mul_of_nonneg_right heta hL
  have hdiv : (1/d^2)*L = 2*(L/(2*d^2)) := by field_simp
  rw [hdiv] at hgain
  linarith

/-- A stronger finite superquadratic range from the explicit dimension
cost. Both displayed numerical conditions are uniform in all parameters;
no optimized asymptotic parameter selection is assumed. -/
theorem superquadratic_optimized_budget {N T : ℕ} (n : ℕ)
    (hT : 2 ≤ T) (hTN : T ≤ N)
    (hcap : (T:ℝ) ≤ (N:ℝ)^((2:ℝ)/3-1/(n+3)))
    (hcost : 200*((n+3:ℕ):ℝ)^5*Real.log (n+3) ≤ Real.log N)
    (hsize : 12*((n+3:ℕ):ℝ)^2 ≤ Real.sqrt (Real.log N)) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        (T:ℝ)^2*Real.exp (Real.sqrt (Real.log N)) ≤ (H.edgeFinset.card:ℝ) := by
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hd : (3:ℝ)≤(n:ℝ)+3 := by linarith [(Nat.cast_nonneg n : (0:ℝ)≤n)]
  have hc : 200*((n:ℝ)+3)^5*Real.log ((n:ℝ)+3) ≤ Real.log N := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hcost
  have hs : 12*((n:ℝ)+3)^2 ≤ Real.sqrt (Real.log N) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hsize
  have hg := optimized_dimension_gain hd (Real.log_nonneg hN1) hc hs
  obtain ⟨G,S,hS,hG⟩ := terminal_lower_bound_quantitative n (1/(n+3)) hT hTN hcap
  refine ⟨G,S,hS,?_⟩
  intro H hHG hpres
  have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hg) (sq_nonneg (T:ℝ))
  apply hh.trans
  simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc,show (3:ℝ)+1=4 by norm_num]
    using hG H hHG hpres

end LinearDistancePreservers.TheoremFourGeneral
