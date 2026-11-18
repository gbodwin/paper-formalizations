import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The exponent rearrangements at the end of Appendices A and B. -/

namespace OnlineReachabilityPreservers

/-- Rewrite a single term of a branching-count comparison in vertex and path counts.
The window is C p / (ℓ d²), with ℓ=M/p and d=M/n. -/
theorem incidence_monomial_bound {M n p C K u v w : ℝ}
    (hM : 0 < M) (hn : 0 < n) (hp : 0 < p) (hC : 0 < C) (hK : 0 ≤ K)
    (positive_exponent : 0 < 4-u-v+3*w)
    (comp : let ℓ := M/p; let d := M/n
            ℓ^2 * d^2 ≤ K * ℓ^u * d^v * (C*p/(ℓ*d^2))^w) :
    M ≤ (K * C^w)^(1/(4-u-v+3*w)) *
      n^((2-v+2*w)/(4-u-v+3*w)) * p^((2-u+2*w)/(4-u-v+3*w)) := by
  let ℓ := M/p
  let d := M/n
  let x := 2-u+w
  let y := 2-v+2*w
  let r := 4-u-v+3*w
  have hℓ : 0 < ℓ := div_pos hM hp
  have hd : 0 < d := div_pos hM hn
  have length_power : ℓ^x * ℓ^u = ℓ^2 * ℓ^w := by
    rw [← Real.rpow_two, ← Real.rpow_add hℓ, ← Real.rpow_add hℓ]
    congr 1
    dsimp [x]
    ring
  have degree_power : d^y * d^v = d^2 * d^(2*w) := by
    rw [← Real.rpow_two, ← Real.rpow_add hd, ← Real.rpow_add hd]
    congr 1
    dsimp [y]
    ring
  have height_power : (C*p/(ℓ*d^2))^w = (C^w * p^w)/(ℓ^w * d^(2*w)) := by
    rw [Real.div_rpow (mul_nonneg hC.le hp.le) (mul_nonneg hℓ.le (sq_nonneg _)),
      Real.mul_rpow hC.le hp.le, Real.mul_rpow hℓ.le (sq_nonneg _)]
    rw [← Real.rpow_natCast_mul hd.le 2]
    norm_num
  change ℓ^2 * d^2 ≤ K * ℓ^u * d^v * (C*p/(ℓ*d^2))^w at comp
  have shifted : ℓ^x * d^y ≤ K * C^w * p^w := by
    apply le_of_mul_le_mul_right (a := ℓ^u * d^v) _ (by positivity)
    calc
      _ = (ℓ^x * ℓ^u) * (d^y * d^v) := by ring
      _ = (ℓ^2 * d^2) * (ℓ^w * d^(2*w)) := by rw [length_power, degree_power]; ring
      _ ≤ (K * ℓ^u * d^v * (C*p/(ℓ*d^2))^w) * (ℓ^w * d^(2*w)) :=
        mul_le_mul_of_nonneg_right comp (by positivity)
      _ = (K * C^w * p^w) * (ℓ^u * d^v) := by
        rw [height_power]
        field_simp
  have at_mass : M^r ≤ (K * C^w) * n^y * p^(2-u+2*w) := by
    dsimp only [ℓ, d] at shifted
    rw [Real.div_rpow hM.le hp.le, Real.div_rpow hM.le hn.le, div_mul_div_comm,
      ← Real.rpow_add hM, div_le_iff₀ (by positivity)] at shifted
    have eq : x+y = r := by dsimp [x, y, r]; ring
    rw [eq] at shifted
    refine shifted.trans_eq ?_
    calc
      _ = (K*C^w) * n^y * (p^x * p^w) := by ring
      _ = _ := by
        have hpowers : x+w = 2-u+2*w := by dsimp [x]; ring
        rw [← Real.rpow_add hp, hpowers]
  have hr : 0 < r := positive_exponent
  have at_root := Real.rpow_le_rpow (Real.rpow_nonneg hM.le _) at_mass
    (show 0 ≤ (1/r : ℝ) from (one_div_pos.mpr hr).le)
  rw [← Real.rpow_mul hM.le, mul_one_div, div_self hr.ne', Real.rpow_one] at at_root
  rw [Real.mul_rpow (by positivity : 0 ≤ (K*C^w) * n^y) (by positivity),
    Real.mul_rpow (by positivity : 0 ≤ K*C^w) (by positivity),
    ← Real.rpow_mul hn.le, ← Real.rpow_mul hp.le, mul_one_div, mul_one_div] at at_root
  exact at_root

/-- The first online term in the Lemma 37 rearrangement. -/
theorem lemma37_first_term {M n p C K b : ℝ}
    (hM : 0 < M) (hn : 0 < n) (hp : 0 < p) (hC : 0 < C) (hK : 0 ≤ K) (hb : 0 < b)
    (comp : let ℓ := M/p; let d := M/n
           ℓ^2*d^2 ≤ K*ℓ^2*d*(C*p/(ℓ*d^2))^(1/b)) :
    M ≤ (K*C^(1/b))^(b/(3+b)) * n^((2+b)/(3+b)) * p^(2/(3+b)) := by
  have he : 0 < 4-(2:ℝ)-1+3*(1/b) := by positivity
  have comp' : let ℓ := M/p; let d := M/n
      ℓ^2*d^2 ≤ K*ℓ^(2:ℝ)*d^(1:ℝ)*(C*p/(ℓ*d^2))^(1/b) := by simpa using comp
  have h := incidence_monomial_bound hM hn hp hC hK he comp'
  have hne : (3+b : ℝ) ≠ 0 := by positivity
  have e0 : 1/(4-(2:ℝ)-1+3*(1/b)) = b/(3+b) := by field_simp; ring
  have e1 : (2-(1:ℝ)+2*(1/b))/(4-2-1+3*(1/b)) = (2+b)/(3+b) := by field_simp; ring
  have e2 : (2-(2:ℝ)+2*(1/b))/(4-2-1+3*(1/b)) = 2/(3+b) := by field_simp; ring
  simpa only [e0, e1, e2] using h

/-- The third offline term in Lemma 42. Its vertex exponent is 1/(b+1). -/
theorem lemma42_third_term {M n p C K b : ℝ}
    (hM : 0 < M) (hn : 0 < n) (hp : 0 < p) (hC : 0 < C) (hK : 0 ≤ K) (hb : 0 < b)
    (comp : let ℓ := M/p; let d := M/n
           ℓ^2*d^2 ≤ K*ℓ^(1/b)*d^2*(C*p/(ℓ*d^2))^(1/b)) :
    M ≤ (K*C^(1/b))^(b/(2*b+2)) * n^(1/(b+1)) * p^((2*b+1)/(2*b+2)) := by
  have he : 0 < 4-(1/b)-2+3*(1/b) := by
    have hib : 0 < 1/b := one_div_pos.mpr hb
    linarith
  have comp' : let ℓ := M/p; let d := M/n
      ℓ^2*d^2 ≤ K*ℓ^(1/b)*d^(2:ℝ)*(C*p/(ℓ*d^2))^(1/b) := by simpa using comp
  have h := incidence_monomial_bound hM hn hp hC hK he comp'
  have hne : (2*b+2 : ℝ) ≠ 0 := by positivity
  have hne' : (b+1 : ℝ) ≠ 0 := by positivity
  have hd : 4-1/b-2+3*(1/b) = (2*b+2)/b := by
    field_simp
    ring
  have e0 : 1/(4-(1/b)-2+3*(1/b)) = b/(2*b+2) := by
    rw [hd, one_div_div]
  have e1 : (2-(2:ℝ)+2*(1/b))/(4-(1/b)-2+3*(1/b)) = 1/(b+1) := by
    rw [hd]
    field_simp [hne, hne']
    ring
  have e2 : (2-(1/b)+2*(1/b))/(4-(1/b)-2+3*(1/b)) = (2*b+1)/(2*b+2) := by
    rw [hd]
    field_simp [hne]
    ring
  simpa only [e0, e1, e2] using h

/-- The third online term gives the numerator used by the corrected recurrence. -/
theorem lemma37_third_term {M n p C K b : ℝ}
    (hM : 0 < M) (hn : 0 < n) (hp : 0 < p) (hC : 0 < C) (hK : 0 ≤ K)
    (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 3/4)
    (comp : let ℓ := M/p; let d := M/n
           ℓ^2*d^2 ≤ K*ℓ^(1/b)*d^2*(C*p/(ℓ*d^2))^((4*b-2*b^2-1)/b^2)) :
    let w := (4*b-2*b^2-1)/b^2
    let den := 11*b-4*b^2-3
    M ≤ (K*C^w)^(b^2/den) * n^((8*b-4*b^2-2)/den) * p^((7*b-2*b^2-2)/den) := by
  let w := (4*b-2*b^2-1)/b^2
  let den := 11*b-4*b^2-3
  have hb : 0 < b := by linarith
  have bsq : 0 < b^2 := sq_pos_of_pos hb
  have hden : 0 < den := by
    have hsq : b*b ≤ (3/4 : ℝ)*(3/4) := mul_le_mul hb₁ hb₁ hb.le (by norm_num)
    dsimp [den]
    nlinarith only [hb₀, hsq]
  have ed : 4-1/b-2+3*w = den/b^2 := by
    dsimp [w, den]
    field_simp
    ring
  have en : 2-2+2*w = (8*b-4*b^2-2)/b^2 := by
    dsimp [w]
    field_simp
    ring
  have ep : 2-1/b+2*w = (7*b-2*b^2-2)/b^2 := by
    dsimp [w]
    field_simp
    ring
  have comp' : let ℓ := M/p; let d := M/n
      ℓ^2*d^2 ≤ K*ℓ^(1/b)*d^(2:ℝ)*(C*p/(ℓ*d^2))^w := by simpa only [w, Real.rpow_two] using comp
  have h := incidence_monomial_bound hM hn hp hC hK (ed.symm ▸ div_pos hden bsq) comp'
  have cancel (x : ℝ) : (x / b^2) / (den / b^2) = x/den := by
    field_simp [hden.ne']
  rw [ed, en, ep, one_div_div, cancel, cancel] at h
  exact h

/-- The vertex exponent yielded by Lemma 42 agrees with the iteration in Theorem 43. -/
theorem lemma42_vertex_exponent {b : ℝ} (hb : 0 < b) :
    2 - 2*((2*b+1)/(2*b+2)) = 1/(b+1) := by
  have h : (2*b+2 : ℝ) ≠ 0 := by positivity
  have h' : (b+1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem lemma42_printed_vertex_exponent_ne {b : ℝ} (hb : 0 < b) :
    2/(b+1) ≠ 2 - 2*((2*b+1)/(2*b+2)) := by
  rw [lemma42_vertex_exponent hb]
  exact (div_lt_div_of_pos_right one_lt_two (by positivity : 0 < b+1)).ne'

end OnlineReachabilityPreservers
