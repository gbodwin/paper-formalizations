import LinearDistancePreservers.GrowingDimension
import LinearDistancePreservers.FixedGap

namespace LinearDistancePreservers.TheoremFourGeneral
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- The quantitative dimension budget is strong enough for a uniform gain
at terminal exponent 2/3-1/d. -/
theorem growing_gain {d L : ℝ} (hd : 3 ≤ d) (hL : 0 ≤ L)
    (hbudget : 100*d^3*Real.log d ≤ Real.sqrt L) :
    Real.exp (Real.sqrt L) ≤
      Real.exp (L/d^2)*Real.exp (-5*Real.sqrt L) := by
  have hd0 : 0 < d := by linarith
  have hinv : d⁻¹ ≤ 1/2 := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) (by linarith : (2:ℝ)≤d)
  have hlog : 1/2 ≤ Real.log d := by
    linarith [Real.one_sub_inv_le_log_of_pos hd0]
  have hx0 := Real.sqrt_nonneg L
  have hx2 := Real.sq_sqrt hL
  have hlarge : 6*d^2 ≤ Real.sqrt L := by
    have hh := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 100*d^3)
    have hh' := mul_le_mul_of_nonneg_right hd (sq_nonneg d)
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hlarge hx0
  have hg : 6*Real.sqrt L ≤ L/d^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hd0)).mpr
    nlinarith
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- A corrected finite growing-dimensional superquadratic range. The
parameters may vary together, subject only to the displayed numerical
budget and terminal cap. This leaves the source's sharper range open. -/
theorem superquadratic_growing {N T : ℕ} (n : ℕ) (hT : 2 ≤ T)
    (hTN : T ≤ N)
    (hcap : (T:ℝ) ≤ (N:ℝ)^((2:ℝ)/3-1/(n+3)))
    (hbudget : 100*((n+3:ℕ):ℝ)^3*Real.log (n+3) ≤ Real.sqrt (Real.log N)) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        (T:ℝ)^2*Real.exp (Real.sqrt (Real.log N)) ≤ (H.edgeFinset.card:ℝ) := by
  let d := ((n+3:ℕ):ℝ)
  let η := (7/3+1/d)/(d*(d+1))
  have hd : 3 ≤ d := by dsimp [d]; exact_mod_cast (show 3 ≤ n+3 by omega)
  have hd0 : 0 < d := by linarith
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0:ℝ) < N := by linarith
  have hT0 : (0:ℝ) < T := by exact_mod_cast (show 0<T by omega)
  have hβ : (((2*(n+3)+1)*(n+2):ℕ):ℝ)/(((n+3)*(n+4):ℕ):ℝ) ≤ 2 := by
    push_cast
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hη : (2:ℝ)/(n+4)+
      ((((2*(n+3)+1)*(n+2):ℕ):ℝ)/(((n+3)*(n+4):ℕ):ℝ)-2)*
      ((2:ℝ)/3-1/(n+3)) = η := by
    dsimp [η,d]
    push_cast
    field_simp
    ring
  have hηlow : 1/d^2 ≤ η := by
    dsimp [η]
    apply (div_le_div_iff₀ (sq_pos_of_pos hd0) (mul_pos hd0 (by linarith))).mpr
    have hcancel : (1/d)*d^2 = d := by field_simp [ne_of_gt hd0]
    rw [add_mul,hcancel]
    nlinarith
  have hr := terminal_rate_lower hN0 hT0 hcap hβ hη
  have hp : (N:ℝ)^(1/d^2) ≤ (N:ℝ)^η :=
    Real.rpow_le_rpow_of_exponent_le hN1 hηlow
  have hb : 100*d^3*Real.log d ≤ Real.sqrt (Real.log N) := by
    simpa only [d,Nat.cast_add,Nat.cast_ofNat] using hbudget
  have hg := growing_gain hd (Real.log_nonneg hN1) hb
  have he : Real.exp (Real.sqrt (Real.log N)) ≤
      (N:ℝ)^(1/d^2)*Real.exp (-5*Real.sqrt (Real.log N)) := by
    rw [Real.rpow_def_of_pos hN0]
    convert hg using 1 <;> congr 1 <;> ring
  obtain ⟨G,S,hS,hG⟩ := displayed_lower_bound_growing n hT hTN hbudget
  refine ⟨G,S,hS,?_⟩
  intro H hHG hpres
  calc
    _ ≤ (T:ℝ)^2*((N:ℝ)^(1/d^2)*Real.exp (-5*Real.sqrt (Real.log N))) :=
      mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ ≤ (T:ℝ)^2*((N:ℝ)^η*Real.exp (-5*Real.sqrt (Real.log N))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)) (sq_nonneg _)
    _ = ((T:ℝ)^2*(N:ℝ)^η)*Real.exp (-5*Real.sqrt (Real.log N)) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right hr (Real.exp_nonneg _)).trans (hG H hHG hpres)

end LinearDistancePreservers.TheoremFourGeneral
