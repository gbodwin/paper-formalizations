import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic

/-! Geometric estimates on finite sets of dyadic scales. -/

namespace OnlineReachabilityPreservers

open Finset

private theorem dyadic_rpow (r : ℝ) (j : ℕ) : ((2:ℝ)^j)^r = ((2:ℝ)^r)^j := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2), mul_comm,
    Real.rpow_mul (by norm_num), Real.rpow_natCast]

/-- A truncated geometric sum of positive powers of dyadic values. -/
theorem dyadic_sum_below (s : Finset ℕ) {r X : ℝ} (hr : 0 < r) (hX : 0 < X)
    (cut : ∀ j ∈ s, (2:ℝ)^j ≤ X) :
    (∑ j ∈ s, ((2:ℝ)^j)^r) ≤ ((2:ℝ)^r/((2:ℝ)^r-1))*X^r := by
  let q := (2:ℝ)^r
  have hq : 1 < q := by
    change 1 < (2:ℝ)^r
    conv_lhs => rw [← Real.rpow_zero (2:ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hr
  have hd : 0 < q-1 := sub_pos.mpr hq
  have hp : 0 ≤ q := zero_le_one.trans hq.le
  change _ ≤ q/(q-1)*X^r
  rcases s.eq_empty_or_nonempty with he | hn
  · rw [he, sum_empty]
    exact mul_nonneg (div_nonneg hp hd.le) (Real.rpow_nonneg hX.le _)
  let m := s.max' hn
  have hm : m ∈ s := max'_mem _ _
  have hcap : q^m ≤ X^r := by
    change ((2:ℝ)^r)^m ≤ _
    rw [← dyadic_rpow]
    exact Real.rpow_le_rpow (by positivity) (cut m hm) hr.le
  calc
    _ = ∑ j ∈ s, q^j := by simp only [q, dyadic_rpow]
    _ ≤ ∑ j ∈ range (m+1), q^j := sum_le_sum_of_subset_of_nonneg
      (fun j hj => mem_range.mpr (Nat.lt_succ_of_le (le_max' _ _ hj)))
      (fun j _ _ => pow_nonneg hp j)
    _ = (q^(m+1)-1)/(q-1) := geom_sum_eq hq.ne' _
    _ ≤ q^(m+1)/(q-1) := div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) hd.le
    _ = (q/(q-1))*q^m := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcap (div_nonneg hp hd.le)

/-- A truncated geometric sum of negative powers of dyadic values. -/
theorem dyadic_sum_above (s : Finset ℕ) {r X : ℝ} (hr : r < 0) (hX : 0 < X)
    (cut : ∀ j ∈ s, X ≤ (2:ℝ)^j) :
    (∑ j ∈ s, ((2:ℝ)^j)^r) ≤ 1/(1-(2:ℝ)^r)*X^r := by
  let q := (2:ℝ)^r
  have hq : q < 1 := by
    change (2:ℝ)^r < 1
    conv_rhs => rw [← Real.rpow_zero (2:ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hr
  have hp : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hd := sub_pos.mpr hq
  change _ ≤ 1/(1-q)*X^r
  rcases s.eq_empty_or_nonempty with he | hn
  · rw [he, sum_empty]
    exact mul_nonneg (one_div_pos.mpr hd).le (Real.rpow_nonneg hX.le _)
  let m := s.min' hn
  let M := s.max' hn
  have hm : m ∈ s := min'_mem _ _
  have hcap : q^m ≤ X^r := by
    change ((2:ℝ)^r)^m ≤ _
    rw [← dyadic_rpow]
    exact Real.rpow_le_rpow_of_nonpos hX (cut m hm) hr.le
  calc
    _ = ∑ j ∈ s, q^j := by simp only [q, dyadic_rpow]
    _ ≤ ∑ j ∈ Ico m (M+1), q^j := sum_le_sum_of_subset_of_nonneg (fun j hj =>
      mem_Ico.mpr ⟨min'_le _ _ hj, Nat.lt_succ_of_le (le_max' _ _ hj)⟩)
      (fun j _ _ => pow_nonneg hp j)
    _ ≤ q^m/(1-q) := geom_sum_Ico_le_of_lt_one hp hq
    _ ≤ X^r/(1-q) := div_le_div_of_nonneg_right hcap hd.le
    _ = _ := by ring

/-- The square root is subadditive on nonnegative reals. -/
theorem sqrt_add_le_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a+b) ≤ Real.sqrt a+Real.sqrt b := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt (add_nonneg ha hb), add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
  linarith only [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

private theorem sqrt_rpow {x : ℝ} (hx : 0 ≤ x) (r : ℝ) :
    Real.sqrt (x^r) = x^(r/2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  congr 1
  ring

private theorem dyadic_low_term {z x t : ℝ} (hz : 0 < z) (hx : 0 < x) :
    x*Real.sqrt ((2*z/x)^t) = (2*z)^(t/2)*x^(1-t/2) := calc
  _ = x*((2*z/x)^(t/2)) := by rw [sqrt_rpow (by positivity)]
  _ = x*((2*z)^(t/2)/x^(t/2)) := by rw [Real.div_rpow (by positivity) hx.le]
  _ = (2*z)^(t/2)*(x/x^(t/2)) := by ring
  _ = _ := by
    have h : x/x^(t/2)=x^(1-t/2) := by rw [Real.rpow_sub hx, Real.rpow_one]
    rw [h]

private theorem dyadic_high_term {z x c e K t : ℝ} (hz : 0 < z) (hx : 0 < x)
    (hc : 0 ≤ c) (hK : 0 ≤ K) :
    x*Real.sqrt ((2*z/x)^(t-1)*K*(z*c/x^e)) =
      (Real.sqrt ((2:ℝ)^(t-1)*K)*z^(t/2))*(Real.sqrt c*x^((3-t-e)/2)) := by
  have zShift : z^(t-1)*z = z^t := by
    calc
      _ = z^(t-1)*z^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hz, sub_add_cancel]
  have xShift : x^2/(x^(t-1)*x^e)=x^(3-t-e) := by
    rw [← Real.rpow_add hx, ← Real.rpow_two, ← Real.rpow_sub hx]
    congr 1
    ring
  have hz1 : 0 ≤ (2:ℝ)^(t-1)*K := by positivity
  have identity : x^2*((2*z/x)^(t-1)*K*(z*c/x^e)) =
      ((2:ℝ)^(t-1)*K)*(z^t*(c*x^(3-t-e))) := calc
    _ = x^2*(((2:ℝ)^(t-1)*z^(t-1)/x^(t-1))*K*(z*c/x^e)) := by
      rw [Real.div_rpow (by positivity) hx.le, Real.mul_rpow (by norm_num) hz.le]
    _ = ((2:ℝ)^(t-1)*K)*((z^(t-1)*z)*(c*(x^2/(x^(t-1)*x^e)))) := by ring
    _ = _ := by rw [zShift, xShift]
  calc
    _ = Real.sqrt (x^2*((2*z/x)^(t-1)*K*(z*c/x^e))) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hx.le]
    _ = Real.sqrt (((2:ℝ)^(t-1)*K)*(z^t*(c*x^(3-t-e)))) := by rw [identity]
    _ = _ := by
      rw [Real.sqrt_mul hz1, Real.sqrt_mul (Real.rpow_nonneg hz.le _), Real.sqrt_mul hc,
        sqrt_rpow hz.le, sqrt_rpow hx.le]
      ring


/-- A dyadic square-root sum with a deterministic cap and three high-threshold
tails. Constants can depend on the exponents and the envelope coefficients. -/
theorem dyadic_weighted_sqrt_sum {C K t r s : ℝ} (hC : 1 ≤ C) (hK : 0 ≤ K)
    (ht : 1 ≤ t) (ht' : t < 2) (hr : 3-t < r) (hs : 3-t < s) :
    ∃ A > 0, ∀ (J : Finset ℕ) {z d x₀ : ℝ}, 0 < z → 1 ≤ d → 1 ≤ x₀ →
      (∀ j ∈ J, (2:ℝ)^j ≤ d) →
      ∀ m : ℕ → ℝ,
      (∀ j ∈ J, m j ≤ (2*z/(2:ℝ)^j)^t) →
      (∀ j ∈ J, C < (2:ℝ)^j →
        let x : ℝ := (2:ℝ)^j
        m j ≤ (2*z/x)^(t-1)*K*(z*(1/d)/x+z*x₀^(r-1)/x^r+z*x₀^(s-1)/x^s)) →
      (∑ j ∈ J, (2:ℝ)^j*Real.sqrt (m j)) ≤ A*z^(t/2)*x₀^(1-t/2) := by
  let e := 1-t/2
  let R := (3-t-r)/2
  let S := (3-t-s)/2
  have he : 0 < e := by dsimp [e]; linarith
  have he' : e ≤ 1/2 := by dsimp [e]; linarith
  have hR : R < 0 := by dsimp [R]; linarith
  have hS : S < 0 := by dsimp [S]; linarith
  let g := (2:ℝ)^e/((2:ℝ)^e-1)
  let gR := 1/(1-(2:ℝ)^R)
  let gS := 1/(1-(2:ℝ)^S)
  have gau : 0 < g := by
    have h : (1:ℝ) < (2:ℝ)^e := by
      conv_lhs => rw [← Real.rpow_zero (2:ℝ)]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) he
    exact div_pos (zero_lt_one.trans h) (sub_pos.mpr h)
  have negCoeff {v : ℝ} (hv : v < 0) : 0 ≤ 1/(1-(2:ℝ)^v) := by
    have base : (2:ℝ)^v ≤ 1 :=
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hv.le).trans_eq (Real.rpow_zero _)
    exact div_nonneg zero_le_one (sub_nonneg.mpr base)
  let H := Real.sqrt ((2:ℝ)^(t-1)*K)
  let L := (2:ℝ)^(t/2)*C^e*g
  let U := H*(g+gR+gS)
  have hL : 0 < L := by
    exact mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le hC) _)) gau
  have hU : 0 ≤ U := mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (add_nonneg gau.le (negCoeff hR)) (negCoeff hS))
  refine ⟨L+U, add_pos_of_pos_of_nonneg hL hU, ?_⟩
  intro J z d x₀ hz hd hx₀ cap m det tail
  let X := C*x₀
  let lo := J.filter (fun j => (2:ℝ)^j ≤ X)
  let hi := J.filter (fun j => ¬ (2:ℝ)^j ≤ X)
  have x₀p := zero_lt_one.trans_le hx₀
  have dpos := zero_lt_one.trans_le hd
  have Cpos := zero_lt_one.trans_le hC
  have Xpos : 0 < X := mul_pos Cpos x₀p
  have le_X (j : ℕ) (hj : j ∈ hi) : X < (2:ℝ)^j := lt_of_not_ge (mem_filter.mp hj).2
  have x₀X : x₀ ≤ X :=
    (one_mul x₀).symm.le.trans (mul_le_mul_of_nonneg_right hC x₀p.le)
  have CX : C ≤ X :=
    (mul_one C).symm.le.trans (mul_le_mul_of_nonneg_left hx₀ Cpos.le)
  have lbound : (∑ j ∈ lo, (2:ℝ)^j*Real.sqrt (m j)) ≤ L*z^(t/2)*x₀^e := calc
    _ ≤ ∑ j ∈ lo, (2*z)^(t/2)*((2:ℝ)^j)^e := by
      apply sum_le_sum
      intro j hj
      exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (det j (mem_filter.mp hj).1))
        (pow_nonneg (by norm_num) j)).trans_eq (dyadic_low_term hz (pow_pos (by norm_num) j))
    _ = (2*z)^(t/2)*∑ j ∈ lo, ((2:ℝ)^j)^e := (mul_sum _ _ _).symm
    _ ≤ (2*z)^(t/2)*(g*X^e) :=
      mul_le_mul_of_nonneg_left (dyadic_sum_below lo he Xpos (fun j hj => (mem_filter.mp hj).2))
        (Real.rpow_nonneg (mul_nonneg (by norm_num) hz.le) _)
    _ = _ := by
      dsimp only [X, L]
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hz.le, Real.mul_rpow Cpos.le x₀p.le]
      ring
  let a₁ (j : ℕ) := Real.sqrt (1/d)*((2:ℝ)^j)^e
  let a₂ (j : ℕ) := Real.sqrt (x₀^(r-1))*((2:ℝ)^j)^R
  let a₃ (j : ℕ) := Real.sqrt (x₀^(s-1))*((2:ℝ)^j)^S
  have hpoint (j : ℕ) (hj : j ∈ hi) :
      (2:ℝ)^j*Real.sqrt (m j) ≤ (H*z^(t/2))*(a₁ j+a₂ j+a₃ j) := by
    let x := (2:ℝ)^j
    have xpos : 0 < x := pow_pos (by norm_num) j
    have xC : C < x := CX.trans_lt (le_X j hj)
    let k := (2*z/x)^(t-1)*K
    let a := z*(1/d)/x
    let b := z*x₀^(r-1)/x^r
    let c := z*x₀^(s-1)/x^s
    have haveTail : m j ≤ k*(a+b+c) := tail j (mem_filter.mp hj).1 xC
    have ka : 0 ≤ k*a := by dsimp only [k, a]; positivity
    have kb : 0 ≤ k*b := by dsimp only [k, b]; positivity
    have kc : 0 ≤ k*c := by dsimp only [k, c]; positivity
    have mid : Real.sqrt (k*(a+b+c)) ≤ Real.sqrt (k*a)+Real.sqrt (k*b)+Real.sqrt (k*c) := by
      rw [mul_add, mul_add]
      exact (sqrt_add_le_nonneg (add_nonneg ka kb) kc).trans
        (add_le_add (sqrt_add_le_nonneg ka kb) le_rfl)
    have there₁ : x*Real.sqrt (k*a) = (H*z^(t/2))*a₁ j := by
      dsimp only [k, a]
      have rr := dyadic_high_term (e := 1) (t := t) (K := K) (c := 1/d)
        hz xpos (one_div_nonneg.mpr dpos.le) hK
      rw [Real.rpow_one, show (3-t-1)/2 = e by dsimp [e]; ring] at rr
      exact rr
    have there₂ : x*Real.sqrt (k*b) = (H*z^(t/2))*a₂ j :=
      dyadic_high_term hz xpos (Real.rpow_nonneg x₀p.le _) hK
    have there₃ : x*Real.sqrt (k*c) = (H*z^(t/2))*a₃ j :=
      dyadic_high_term hz xpos (Real.rpow_nonneg x₀p.le _) hK
    change x*Real.sqrt (m j) ≤ _
    calc
      _ ≤ x*Real.sqrt (k*(a+b+c)) := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt haveTail) xpos.le
      _ ≤ x*(Real.sqrt (k*a)+Real.sqrt (k*b)+Real.sqrt (k*c)) := mul_le_mul_of_nonneg_left mid xpos.le
      _ = _ := by rw [mul_add, mul_add, there₁, there₂, there₃]; ring
  have a₁sum : (∑ j ∈ hi, a₁ j) ≤ g*x₀^e := by
    have hdPow : d^e ≤ d^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le hd he'
    have hxPow : 1 ≤ x₀^e := by
      conv_lhs => rw [← Real.one_rpow e]
      exact Real.rpow_le_rpow zero_le_one hx₀ he.le
    have sq : Real.sqrt (1/d)*d^e ≤ 1 := by
      rw [Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_eq_rpow, one_div, ← div_eq_inv_mul,
        div_le_iff₀ (Real.rpow_pos_of_pos dpos _), one_mul]
      exact hdPow
    calc
      _ = Real.sqrt (1/d)*∑ j ∈ hi, ((2:ℝ)^j)^e := (mul_sum _ _ _).symm
      _ ≤ Real.sqrt (1/d)*(g*d^e) := mul_le_mul_of_nonneg_left
        (dyadic_sum_below hi he dpos (fun j hj => cap j (mem_filter.mp hj).1)) (Real.sqrt_nonneg _)
      _ = g*(Real.sqrt (1/d)*d^e) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (sq.trans hxPow) gau.le
  have negSum {q : ℝ} (hq : (3-t-q)/2 < 0) :
      (∑ j ∈ hi, Real.sqrt (x₀^(q-1))*((2:ℝ)^j)^((3-t-q)/2)) ≤
        (1/(1-(2:ℝ)^((3-t-q)/2)))*x₀^e := by
    let v := (3-t-q)/2
    let W := 1/(1-(2:ℝ)^v)
    calc
      _ = Real.sqrt (x₀^(q-1))*∑ j ∈ hi, ((2:ℝ)^j)^v := (mul_sum _ _ _).symm
      _ ≤ Real.sqrt (x₀^(q-1))*(W*x₀^v) := mul_le_mul_of_nonneg_left
        (dyadic_sum_above hi hq x₀p (fun j hj => x₀X.trans (le_X j hj).le)) (Real.sqrt_nonneg _)
      _ = W*(x₀^((q-1)/2)*x₀^v) := by rw [sqrt_rpow x₀p.le]; ring
      _ = _ := by rw [← Real.rpow_add x₀p, show (q-1)/2+v=e by dsimp [v, e]; ring]
  have hbound : (∑ j ∈ hi, (2:ℝ)^j*Real.sqrt (m j)) ≤ U*z^(t/2)*x₀^e := calc
    _ ≤ ∑ j ∈ hi, (H*z^(t/2))*(a₁ j+a₂ j+a₃ j) :=
      sum_le_sum (fun j hj => hpoint j hj)
    _ = (H*z^(t/2))*((∑ j ∈ hi, a₁ j)+(∑ j ∈ hi, a₂ j)+(∑ j ∈ hi, a₃ j)) := by
      rw [← mul_sum, sum_add_distrib, sum_add_distrib]
    _ ≤ (H*z^(t/2))*(g*x₀^e+gR*x₀^e+gS*x₀^e) := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add a₁sum (negSum hR)) (negSum hS))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hz.le _))
    _ = _ := by dsimp only [U]; ring
  have split := (sum_filter_add_sum_filter_not J (fun j => (2:ℝ)^j ≤ X)
    (fun j => (2:ℝ)^j*Real.sqrt (m j))).symm
  rw [split]
  exact (add_le_add lbound hbound).trans_eq (by ring)


end OnlineReachabilityPreservers
