import LinearDistancePreservers.OptimizedGap

namespace LinearDistancePreservers.TheoremFourGeneral
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- Choose a genuine integer dimension from a sixth-root scale, retaining
explicit rounding bounds and both quantitative cost conditions. -/
theorem sixth_root_dimension {R : ℝ} (hR : 16 ≤ R) :
    ∃ d : ℕ, 3 ≤ d ∧ R ≤ 8*(d:ℝ) ∧
      200*(d:ℝ)^5*Real.log d ≤ R^6 ∧ 12*(d:ℝ)^2 ≤ R^3 := by
  let d := ⌊R/4⌋₊
  have hR0 : 0 ≤ R := by linarith
  have hdu : (d:ℝ) ≤ R/4 := Nat.floor_le (by positivity)
  have hdl : R/4 < (d:ℝ)+1 := Nat.lt_floor_add_one _
  have hd3 : (3:ℝ) ≤ d := by linarith
  have hd0 : (0:ℝ)<d := by linarith
  have hdn : 3 ≤ d := by exact_mod_cast hd3
  have hround : R ≤ 8*(d:ℝ) := by linarith
  have hlog : Real.log (d:ℝ) ≤ d := by linarith [Real.log_le_sub_one_of_pos hd0]
  have hp : (4*(d:ℝ))^6 ≤ R^6 :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hcost : 200*(d:ℝ)^5*Real.log d ≤ R^6 := by
    calc
      _ ≤ 200*(d:ℝ)^5*(d:ℝ) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 200*(d:ℝ)^6 := by ring
      _ ≤ 4096*(d:ℝ)^6 := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (4*(d:ℝ))^6 := by ring
      _ ≤ _ := hp
  have hdR : (d:ℝ) ≤ R := by linarith
  have hsize : 12*(d:ℝ)^2 ≤ R^3 := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg d) hdR 2
    have hh' := mul_le_mul_of_nonneg_right hR (sq_nonneg R)
    nlinarith
  exact ⟨d,hdn,hround,hcost,hsize⟩

/-- A clean corrected near-threshold range with completely explicit finite
size threshold. The exponent 5/6 is deliberately conservative and does not
claim the original square-root-exponential deficit. -/
theorem superquadratic_sixth_root {N T : ℕ} (hT : 2 ≤ T) (hTN : T ≤ N)
    (hN : (16:ℝ)^6 ≤ Real.log N)
    (hcap : (T:ℝ) ≤ (N:ℝ)^((2:ℝ)/3)*
      Real.exp (-8*(Real.log N)^((5:ℝ)/6))) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        (T:ℝ)^2*Real.exp (Real.sqrt (Real.log N)) ≤ (H.edgeFinset.card:ℝ) := by
  let L := Real.log (N:ℝ)
  let R := L^((6:ℝ)⁻¹)
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have hR0 : 0 ≤ R := Real.rpow_nonneg hL _
  have hR6 : R^6 = L := Real.rpow_inv_natCast_pow hL (by decide : (6:ℕ) ≠ 0)
  have hR : 16 ≤ R := by
    apply (pow_le_pow_iff_left₀ (by norm_num) hR0 (by decide : (6:ℕ) ≠ 0)).mp
    simpa only [hR6,L] using hN
  have hRpos : 0<R := by linarith
  have hR5 : R^5 = L^((5:ℝ)/6) := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast hL]
    norm_num
  obtain ⟨d,hd3,hround,hcost,hsize⟩ := sixth_root_dimension hR
  have hd0 : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hsize' : 12*(d:ℝ)^2 ≤ Real.sqrt L := by
    have heq : R^3 = Real.sqrt L := by
      apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg L)).mp
      rw [Real.sq_sqrt hL,← hR6]
      ring
    rwa [← heq]
  have hcost' : 200*(d:ℝ)^5*Real.log d ≤ L := by rwa [hR6] at hcost
  have hloss : L/(d:ℝ) ≤ 8*R^5 := by
    apply (div_le_iff₀ hd0).mpr
    calc
      _ = R*R^5 := by rw [← hR6]; ring
      _ ≤ (8*(d:ℝ))*R^5 := mul_le_mul_of_nonneg_right hround (by positivity)
      _ = _ := by ring
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hcap' : (T:ℝ) ≤ (N:ℝ)^((2:ℝ)/3-1/(d:ℝ)) := by
    apply hcap.trans
    rw [← hR5]
    rw [Real.rpow_def_of_pos hN0,Real.rpow_def_of_pos hN0,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    change L*(2/3)+ -8*R^5 ≤ L*(2/3-1/(d:ℝ))
    calc
      _ ≤ L*(2/3)-L/(d:ℝ) := by linarith only [hloss]
      _ = _ := by ring
  have hn : d-3+3=d := Nat.sub_add_cancel hd3
  have hnr : ((d-3:ℕ):ℝ)+3=(d:ℝ) := by exact_mod_cast hn
  apply superquadratic_optimized_budget (d-3) hT hTN
  · simpa only [hnr] using hcap'
  · simpa only [hn,hnr,L] using hcost'
  · simpa only [hn,L] using hsize'

end LinearDistancePreservers.TheoremFourGeneral
