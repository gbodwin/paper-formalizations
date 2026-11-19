import OnlineReachabilityPreservers.DyadicSums
import OnlineReachabilityPreservers.OffBaseMoment
import OnlineReachabilityPreservers.OnBaseAverage

/-! The off-base dyadic estimate in Appendix A. -/

namespace OnlineReachabilityPreservers

open Finset

/-- At the first dyadic transition, the middle predecessor term is below the
deterministic cap. Its remaining contribution can be summed on its own. -/
private theorem middle_tail_at_threshold {a ℓ d h : ℝ} (ha : 7/10 ≤ a) (ha' : a ≤ 3/4)
    (hℓ : 0 < ℓ) (hh : 1 ≤ h) (hd : h ≤ d) {x₀ : ℝ} (hx₀ : h^(1/3:ℝ) ≤ x₀) :
    let r := 1/(2*a-1)
    let y := d*h
    (ℓ/d)*y^(a*r) ≤ (ℓ*y)*x₀^(r-1) := by
  dsimp only
  let r := 1/(2*a-1)
  let y := d*h
  let Y := y^(1/2:ℝ)
  have hp := zero_lt_one.trans_le hh
  have dp := hp.trans_le hd
  have yp : 0 < y := mul_pos dp hp
  have xp : 0 < x₀ := (Real.rpow_pos_of_pos hp _).trans_le hx₀
  have hden : 0 < 2*a-1 := by linarith
  have rlow : 1 ≤ r := (le_div_iff₀ hden).mpr (by linarith)
  have rhigh : r ≤ 5/2 := (div_le_iff₀ hden).mpr (by linarith)
  have shift : (2*a-1)*r = 1 := by dsimp only [r]; rw [← mul_div_assoc, mul_one, div_self hden.ne']
  have exp : a*r = 1+(1/2)*(r-1) := by nlinarith only [shift]
  have hratio : Y/x₀ ≤ d^(2/3:ℝ) := calc
    _ ≤ Y/h^(1/3:ℝ) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg yp.le _) (Real.rpow_pos_of_pos hp _) hx₀
    _ = d^(1/2:ℝ)*h^(1/6:ℝ) := by
      dsimp only [Y, y]
      rw [Real.mul_rpow dp.le hp.le, mul_div_assoc, ← Real.rpow_sub hp]
      norm_num
    _ ≤ d^(1/2:ℝ)*d^(1/6:ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hp.le hd (by norm_num)) (Real.rpow_nonneg dp.le _)
    _ = _ := by rw [← Real.rpow_add dp]; norm_num
  have hpow : (Y/x₀)^(r-1) ≤ d := calc
    _ ≤ (d^(2/3:ℝ))^(r-1) := Real.rpow_le_rpow (div_nonneg (Real.rpow_nonneg yp.le _) xp.le)
      hratio (sub_nonneg.mpr rlow)
    _ = d^((2/3)*(r-1)) := (Real.rpow_mul dp.le _ _).symm
    _ ≤ d^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (hh.trans hd) (by linarith)
    _ = _ := Real.rpow_one _
  have factor : Y^(r-1) ≤ d*x₀^(r-1) := by
    rw [Real.div_rpow (Real.rpow_nonneg yp.le _) xp.le, div_le_iff₀ (Real.rpow_pos_of_pos xp _)] at hpow
    exact hpow
  have yy : y^(a*r) = y*Y^(r-1) := by
    dsimp only [Y]
    rw [← Real.rpow_mul yp.le, exp, Real.rpow_add yp, Real.rpow_one]
  change (ℓ/d)*y^(a*r) ≤ (ℓ*y)*x₀^(r-1)
  calc
    _ = (ℓ*y/d)*Y^(r-1) := by rw [yy]; ring
    _ ≤ (ℓ*y/d)*(d*x₀^(r-1)) := mul_le_mul_of_nonneg_left factor (by positivity)
    _ = _ := by field_simp

private theorem last_tail_threshold {b h : ℝ} (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 3/4) (hh : 1 ≤ h) :
    let s := 1/(1-b)
    let x₀ := h^((1-b)/b)
    h^(1/3:ℝ) ≤ x₀ ∧ x₀^(s-1)=h := by
  dsimp only
  have bpos : 0 < b := by linarith
  have bden : 0 < 1-b := by linarith
  have hg : (1/3:ℝ) ≤ (1-b)/b := (le_div_iff₀ bpos).mpr (by linarith)
  refine ⟨Real.rpow_le_rpow_of_exponent_le hh hg, ?_⟩
  rw [← Real.rpow_mul (zero_le_one.trans hh)]
  have exp : (1-b)/b*(1/(1-b)-1) = 1 := by field_simp [bpos.ne', bden.ne']; ring
  rw [exp, Real.rpow_one]

/-- Normalize the three predecessor terms using the first transition scale.
The middle and last terms are controlled separately. -/
theorem off_base_predecessor_tail_shape {C a b ℓ d h x : ℝ}
    (hC : 0 < C) (ha₀ : 7/10 ≤ a) (ha₁ : a ≤ 3/4) (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 3/4)
    (hℓ : 0 < ℓ) (hx : 0 < x) (hh : 1 ≤ h) (hd : h ≤ d) :
    let r := 1/(2*a-1)
    let s := 1/(1-b)
    let y := d*h
    let z := ℓ*y
    let x₀ := h^((1-b)/b)
    (ℓ/d)*(C*y/x+(C*y^a/x)^r+(C*y^(2-2*b)/x)^s) ≤
      (C+C^r+C^s)*(z*(1/d)/x+z*x₀^(r-1)/x^r+z*x₀^(s-1)/x^s) := by
  dsimp only
  let r := 1/(2*a-1)
  let s := 1/(1-b)
  let y := d*h
  let z := ℓ*y
  let x₀ := h^((1-b)/b)
  let F := z*(1/d)/x
  let G := z*x₀^(r-1)/x^r
  let H := z*x₀^(s-1)/x^s
  have hp := zero_lt_one.trans_le hh
  have dp := hp.trans_le hd
  have yp : 0 < y := mul_pos dp hp
  have xp : 0 < x₀ := Real.rpow_pos_of_pos hp _
  have y0 : 0 ≤ y := yp.le
  have nF : 0 ≤ F := by dsimp only [F, z]; positivity
  have nG : 0 ≤ G := by dsimp only [G, z]; positivity
  have nH : 0 ≤ H := by dsimp only [H, z]; positivity
  have r0 : 0 ≤ C^r := Real.rpow_nonneg hC.le _
  have s0 : 0 ≤ C^s := Real.rpow_nonneg hC.le _
  have ⟨start, height⟩ := last_tail_threshold hb₀ hb₁ hh
  change h^(1/3:ℝ) ≤ x₀ at start
  change x₀^(s-1)=h at height
  have second := middle_tail_at_threshold ha₀ ha₁ hℓ hh hd start
  change (ℓ/d)*y^(a*r) ≤ z*x₀^(r-1) at second
  have third : (2-2*b)*s = 2 := by
    have h : 1-b ≠ 0 := (show 0 < 1-b by linarith).ne'
    dsimp only [s]
    field_simp [h]
  have Gterm : (ℓ/d)*(C*y^a/x)^r ≤ C^r*G := calc
    _ = C^r*(((ℓ/d)*y^(a*r))/x^r) := by
      rw [Real.div_rpow (by positivity) hx.le, Real.mul_rpow hC.le (Real.rpow_nonneg y0 _),
        ← Real.rpow_mul y0 a r]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right second (Real.rpow_nonneg hx.le _)) r0
  have Hterm : (ℓ/d)*(C*y^(2-2*b)/x)^s = C^s*H := by
    rw [Real.div_rpow (by positivity) hx.le, Real.mul_rpow hC.le (Real.rpow_nonneg y0 _),
      ← Real.rpow_mul y0, third, Real.rpow_two]
    dsimp only [H, z]
    rw [height]
    dsimp only [y]
    field_simp
  change (ℓ/d)*(C*y/x+(C*y^a/x)^r+(C*y^(2-2*b)/x)^s) ≤ (C+C^r+C^s)*(F+G+H)
  calc
    _ = C*F+(ℓ/d)*(C*y^a/x)^r+(ℓ/d)*(C*y^(2-2*b)/x)^s := by dsimp only [F, z]; ring
    _ ≤ C*F+C^r*G+C^s*H := by rw [Hterm]; exact add_le_add (add_le_add le_rfl Gterm) le_rfl
    _ ≤ _ := by
      have row₁ : C*F ≤ (C+C^r+C^s)*F := mul_le_mul_of_nonneg_right (by linarith) nF
      have row₂ : C^r*G ≤ (C+C^r+C^s)*G := mul_le_mul_of_nonneg_right (by linarith) nG
      have row₃ : C^s*H ≤ (C+C^r+C^s)*H := mul_le_mul_of_nonneg_right (by linarith) nH
      nlinarith only [row₁, row₂, row₃]

/-- The sum of square roots of the mean size powers of the actual buckets.
No separate factor for the number of buckets is needed. -/
theorem lemma34_size_sqrt_sum {C a b t : ℝ} (hC : 1 ≤ C) (ha₀ : 7/10 ≤ a)
    (ha₁ : a < 3/4) (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 3/4) (ht₀ : 1 ≤ t) (ht₁ : t < 2) :
    ∃ A > 0, ∀ {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype V] [Fintype I]
      {paths : I → Finset V} (_ : HalfBridgeFree (PathBefore paths) 4) (L D h : ℕ),
      0 < Fintype.card I → 0 < L → 0 < h → h ≤ D →
      Fintype.card V*D ≤ 4*Fintype.card I*L →
      (∀ i, (paths i).card ≤ L) →
      (∀ v, (occurrences paths v).card ≤ D) → InducedSizeBound paths C a b →
      let z : ℝ := (L:ℝ)*((D:ℝ)*h)
      let x₀ := (h:ℝ)^((1-b)/b)
      (∑ j ∈ range (Nat.log 2 D+1), (2:ℝ)^j*
        Real.sqrt (uniformMean fun base => ((degreeBucket paths base h j).card:ℝ)^t)) ≤
        A*z^(t/2)*x₀^(1-t/2) := by
  let r := 1/(2*a-1)
  let s := 1/(1-b)
  let K := 4*(C+C^r+C^s)
  have hc := zero_lt_one.trans_le hC
  have ha : 1/2 < a := by linarith
  have hb : b < 1 := by linarith
  have rlow : 2 < r := (lt_div_iff₀ (by linarith : 0 < 2*a-1)).mpr (by linarith)
  have slow : 3 ≤ s := (le_div_iff₀ (by linarith : 0 < 1-b)).mpr (by linarith)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  obtain ⟨A, hA, dyadic⟩ := dyadic_weighted_sqrt_sum hC hK ht₀ ht₁
    (show 3-t < r by linarith) (show 3-t < s by linarith)
  refine ⟨A, hA, ?_⟩
  intro V I _ _ _ _ paths free L D h hp hl hh hd ratio lengths degree input
  dsimp only
  let ℓ : ℝ := L
  let d : ℝ := D
  let u : ℝ := h
  let y := d*u
  let z := ℓ*y
  let x₀ := u^((1-b)/b)
  let n : ℝ := Fintype.card V
  let p : ℝ := Fintype.card I
  let J := range (Nat.log 2 D+1)
  let S (j : ℕ) (base : I) : ℝ := (degreeBucket paths base h j).card
  let m (j : ℕ) := uniformMean (fun base => (S j base)^t)
  have ul : 1 ≤ u := by change (1:ℝ) ≤ h; exact_mod_cast (show 1 ≤ h from hh)
  have dl : u ≤ d := Nat.cast_le.mpr hd
  have lp : 0 < ℓ := Nat.cast_pos.mpr hl
  have dp : 0 < d := zero_lt_one.trans_le (ul.trans dl)
  have up : 0 < u := zero_lt_one.trans_le ul
  have zp : 0 < z := mul_pos lp (mul_pos dp up)
  have pp : 0 < p := Nat.cast_pos.mpr hp
  have xpos : 1 ≤ x₀ := by
    have g : 0 ≤ (1-b)/b := div_nonneg (by linarith) (by linarith)
    change 1 ≤ u^((1-b)/b)
    conv_lhs => rw [← Real.one_rpow ((1-b)/b)]
    exact Real.rpow_le_rpow zero_le_one ul g
  have caps (j : ℕ) (hj : j ∈ J) : (2:ℝ)^j ≤ d := by
    have hd0 : 0 < D := hh.trans_le hd
    have hn : (2:ℕ)^j ≤ D := (Nat.pow_le_pow_right (by decide)
        (Nat.le_of_lt_succ (mem_range.mp hj))).trans (Nat.pow_log_le_self 2 hd0.ne')
    change (2:ℝ)^j ≤ (D:ℝ)
    exact_mod_cast hn
  have size (j : ℕ) (i : I) : S j i ≤ 2*z/(2:ℝ)^j := by
    apply (le_div_iff₀ (pow_pos (by norm_num) j)).mpr
    have raw := degreeBucket_size_cap paths i h j L D (lengths i) degree
    have hsum : (L*D)*(h+1) ≤ L*D*(2*h) := Nat.mul_le_mul_left _ (by omega)
    have final : (degreeBucket paths i h j).card*2^j ≤ 2*(L*(D*h)) :=
      (raw.trans hsum).trans_eq (by ring)
    dsimp only [S, z, ℓ, y, d, u]
    exact_mod_cast final
  have nratio : n/p ≤ 4*(ℓ/d) := by
    rw [← mul_div_assoc, le_div_iff₀ dp, div_mul_eq_mul_div, div_le_iff₀ pp]
    dsimp only [n, d, ℓ, p]
    exact_mod_cast ratio.trans_eq (by ring)
  refine dyadic J zp (ul.trans dl) xpos caps m ?_ ?_
  · intro j _
    exact uniformMean_power_le_cap hp (zero_le_one.trans ht₀) (fun _ => Nat.cast_nonneg _) (size j)
  · intro j _ big
    dsimp only
    let x := (2:ℝ)^j
    let E := C*y/x+(C*y^a/x)^r+(C*y^(2-2*b)/x)^s
    let F := z*(1/d)/x+z*x₀^(r-1)/x^r+z*x₀^(s-1)/x^s
    have xPos : 0 < x := pow_pos (by norm_num) j
    have yPos : 0 < y := mul_pos dp up
    have Epos : 0 ≤ E := by dsimp only [E]; positivity
    have average : uniformMean (S j) ≤ n*E/p :=
      lemma34_mean_bucket_size free h j D hp hc big ha hb degree input
    have meanShape : uniformMean (S j) ≤ K*F := calc
      _ ≤ n*E/p := average
      _ = (n/p)*E := by ring
      _ ≤ (4*(ℓ/d))*E := mul_le_mul_of_nonneg_right nratio Epos
      _ = 4*((ℓ/d)*E) := by ring
      _ ≤ 4*((C+C^r+C^s)*F) := mul_le_mul_of_nonneg_left
        (off_base_predecessor_tail_shape hc ha₀ ha₁.le hb₀ hb₁ lp xPos ul dl) (by norm_num)
      _ = _ := by dsimp only [K]; ring
    have pow := uniformMean_power_bound ht₀ (fun i => Nat.cast_nonneg (degreeBucket paths i h j).card) (size j)
    have coef : 0 ≤ (2*z/x)^(t-1) := Real.rpow_nonneg (div_nonneg (mul_nonneg (by norm_num) zp.le) xPos.le) _
    exact pow.trans ((mul_le_mul_of_nonneg_left meanShape coef).trans_eq (by ring))

private theorem squared_weight {k A z x t : ℝ} (hk : 0 ≤ k) (hz : 0 ≤ z) (hx : 0 ≤ x) :
    (Real.sqrt k*(A*z^(t/2)*x^(1-t/2)))^2 = k*A^2*z^t*x^(2-t) := by
  have expZ : (z^(t/2))^2 = z^t := by
    rw [← Real.rpow_two, ← Real.rpow_mul hz, div_mul_cancel₀ t (by norm_num)]
  have expX : (x^(1-t/2))^2 = x^(2-t) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hx]
    congr 1
    ring
  rw [mul_pow, Real.sq_sqrt hk, mul_pow, mul_pow, expZ, expX]
  ring

/-- Translate the three square-root moments into the three terms of Lemma 34. -/
theorem lemma34_weighted_powers {ℓ d h a b : ℝ} (hl : 1 ≤ ℓ) (hd : 0 < d) (hh : 1 ≤ h)
    (hb₀ : 1/2 < b) (hb₁ : b ≤ 1) :
    let z := ℓ*(d*h)
    let x₀ := h^((1-b)/b)
    let γ := (3-4*a)/(2-2*a)
    let D := ℓ^2*d*h^(1/b)
    let E := ℓ^(3/2:ℝ)*d^(3/2+γ)*h^((2*b+1)/(2*b))
    let F := ℓ^(1/b)*d^2*h^((4*b-2*b^2-1)/b^2)
    ((ℓ+d)*z*x₀ ≤ D+F) ∧
      d^γ*z^(3/2:ℝ)*x₀^(1/2:ℝ) = E ∧
      d^((2*b-1)/b)*z^(1/b)*x₀^(2-1/b) = F := by
  dsimp only
  let z := ℓ*(d*h)
  let g := (1-b)/b
  let x₀ := h^g
  let γ := (3-4*a)/(2-2*a)
  let w := (4*b-2*b^2-1)/b^2
  let D := ℓ^2*d*h^(1/b)
  let E := ℓ^(3/2:ℝ)*d^(3/2+γ)*h^((2*b+1)/(2*b))
  let F := ℓ^(1/b)*d^2*h^w
  have hℓ := zero_lt_one.trans_le hl
  have hp := zero_lt_one.trans_le hh
  have hb : 0 < b := by linarith
  have w_eq : (1/b)+g*(2-1/b) = w := by
    dsimp only [g, w]
    field_simp
    ring
  have first_eq : 1+g = 1/b := by
    dsimp only [g]
    field_simp
    ring
  have second_eq : (3/2:ℝ)+g*(1/2) = (2*b+1)/(2*b) := by
    dsimp only [g]
    field_simp
    ring
  have secondD : (2*b-1)/b+1/b = 2 := by field_simp; ring
  have eL : 1 ≤ 1/b := (le_div_iff₀ hb).mpr (by linarith)
  have ew : 1/b ≤ w := by
    have g0 : 0 ≤ g := div_nonneg (by linarith) hb.le
    have e0 : 0 ≤ 2-1/b := by
      apply sub_nonneg.mpr
      exact (div_le_iff₀ hb).mpr (by linarith)
    rw [← w_eq]
    linarith only [mul_nonneg g0 e0]
  have absorb : ℓ*d^2*h^(1/b) ≤ F := by
    have hℓ' : ℓ ≤ ℓ^(1/b) := by
      conv_lhs => rw [← Real.rpow_one ℓ]
      exact Real.rpow_le_rpow_of_exponent_le hl eL
    have hh' := Real.rpow_le_rpow_of_exponent_le hh ew
    exact mul_le_mul (mul_le_mul_of_nonneg_right hℓ' (sq_nonneg d)) hh'
      (Real.rpow_nonneg hp.le _) (mul_nonneg (Real.rpow_nonneg hℓ.le _) (sq_nonneg d))
  have hprod : h*x₀ = h^(1/b) := calc
    _ = h^(1:ℝ)*h^g := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hp, first_eq]
  change (ℓ+d)*z*x₀ ≤ D+F ∧ d^γ*z^(3/2:ℝ)*x₀^(1/2:ℝ) = E ∧
    d^((2*b-1)/b)*z^(1/b)*x₀^(2-1/b) = F
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = ℓ^2*d*(h*x₀)+ℓ*d^2*(h*x₀) := by dsimp only [z]; ring
      _ = D+ℓ*d^2*h^(1/b) := by rw [hprod]
      _ ≤ _ := add_le_add le_rfl absorb
  · dsimp only [z,x₀,E]
    rw [Real.mul_rpow hℓ.le (mul_nonneg hd.le hp.le), Real.mul_rpow hd.le hp.le,
      ← Real.rpow_mul hp.le]
    calc
      _ = ℓ^(3/2:ℝ)*(d^(3/2:ℝ)*d^γ)*(h^(3/2:ℝ)*h^(g*(1/2))) := by ring
      _ = _ := by rw [← Real.rpow_add hd, ← Real.rpow_add hp, second_eq]
  · dsimp only [z,x₀,F]
    rw [Real.mul_rpow hℓ.le (mul_nonneg hd.le hp.le), Real.mul_rpow hd.le hp.le,
      ← Real.rpow_mul hp.le]
    calc
      _ = ℓ^(1/b)*(d^((2*b-1)/b)*d^(1/b))*(h^(1/b)*h^(g*(2-1/b))) := by ring
      _ = _ := by rw [← Real.rpow_add hd, ← Real.rpow_add hp, secondD, w_eq, Real.rpow_two]


set_option maxHeartbeats 600000 in
/-- The off-base tuple estimate of Lemma 34 at the uniform length and degree
caps. Bounds on the ratio of ambient sizes supply the mean predecessor tails. -/
theorem lemma34_off_base_cap_expectation {C a b : ℝ} (hC : 1 ≤ C) (ha₀ : 7/10 ≤ a)
    (ha₁ : a < 3/4) (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 3/4) :
    ∃ A > 0, ∀ {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype V] [Fintype I]
      {paths : I → Finset V} (_ : HalfBridgeFree (PathBefore paths) 4) (L D h : ℕ),
      0 < Fintype.card I → 0 < h → h ≤ L → h ≤ D →
      Fintype.card V*D ≤ 4*Fintype.card I*L →
      (∀ i, (paths i).card ≤ L) →
      (∀ v, (occurrences paths v).card ≤ D) → InducedSizeBound paths C a b →
      let ℓ : ℝ := L
      let d : ℝ := D
      let u : ℝ := h
      uniformMean (fun base => ((offBaseBranchTuples paths base h).card:ℝ)) ≤
        A*(ℓ^2*d*u^(1/b) +
          ℓ^(3/2:ℝ)*d^(3/2+(3-4*a)/(2-2*a))*u^((2*b+1)/(2*b)) +
          ℓ^(1/b)*d^2*u^((4*b-2*b^2-1)/b^2)) := by
  have Cpos := zero_lt_one.trans_le hC
  have bpos : 0 < b := by linarith
  have hb : 1/2 < b := by linarith
  have ib₀ : 1 ≤ 1/b := (le_div_iff₀ bpos).mpr (by linarith)
  have ib₁ : 1/b < 2 := (div_lt_iff₀ bpos).mpr (by linarith)
  obtain ⟨A₁, hA₁, root₁⟩ := lemma34_size_sqrt_sum hC ha₀ ha₁ hb₀ hb₁
    (show (1:ℝ) ≤ 1 by norm_num) (by norm_num)
  obtain ⟨A₂, hA₂, root₂⟩ := lemma34_size_sqrt_sum hC ha₀ ha₁ hb₀ hb₁
    (show (1:ℝ) ≤ 3/2 by norm_num) (by norm_num)
  obtain ⟨A₃, hA₃, root₃⟩ := lemma34_size_sqrt_sum hC ha₀ ha₁ hb₀ hb₁ ib₀ ib₁
  let c₂ := (1/(3-4*a)+1)*C^(1/(2-2*a))
  let c₃ := (1/(2*b-1)+1)*C^(1/b)
  let k₁ := 2*C*A₁^2
  let k₂ := c₂*A₂^2
  let k₃ := c₃*A₃^2
  let K := 1+k₁+k₂+k₃
  have d₂ : 0 < 3-4*a := by linarith
  have d₃ : 0 < 2*b-1 := by linarith
  have hc₂ : 0 ≤ c₂ := by dsimp only [c₂]; positivity
  have hc₃ : 0 ≤ c₃ := by dsimp only [c₃]; positivity
  have hk₁ : 0 ≤ k₁ := by dsimp only [k₁]; positivity
  have hk₂ : 0 ≤ k₂ := mul_nonneg hc₂ (sq_nonneg _)
  have hk₃ : 0 ≤ k₃ := mul_nonneg hc₃ (sq_nonneg _)
  have hK : 0 < K := by dsimp only [K]; linarith only [hk₁,hk₂,hk₃]
  refine ⟨12*K, by positivity, ?_⟩
  intro V I _ _ _ _ paths free L D h hp hh hL hD ratio lengths degree prior
  dsimp only
  let ℓ : ℝ := L
  let d : ℝ := D
  let u : ℝ := h
  let Q := uniformMean (fun base => ((offBaseBranchTuples paths base h).card:ℝ))
  let z := ℓ*(d*u)
  let x₀ := u^((1-b)/b)
  let γ := (3-4*a)/(2-2*a)
  let e := (2*b-1)/b
  let weight₁ := 2*C*(ℓ+d)
  let weight₂ := c₂*d^γ
  let weight₃ := c₃*d^e
  let J := range (Nat.log 2 D+1)
  let P (j : ℕ) (base : I) := ((degreeBucket paths base h j).card:ℝ)
  let M (t : ℝ) (j : ℕ) := uniformMean (fun base => (P j base)^t)
  let W (t : ℝ) := ∑ j ∈ J, (2:ℝ)^j*Real.sqrt (M t j)
  have L0 := hh.trans_le hL
  have D0 := hh.trans_le hD
  have ℓp : 0 < ℓ := Nat.cast_pos.mpr L0
  have dp : 0 < d := Nat.cast_pos.mpr D0
  have up : 0 < u := Nat.cast_pos.mpr hh
  have zp : 0 < z := mul_pos ℓp (mul_pos dp up)
  have xp : 0 < x₀ := Real.rpow_pos_of_pos up _
  have l₁ : 0 ≤ weight₁ := by dsimp only [weight₁]; positivity
  have l₂ : 0 ≤ weight₂ := mul_nonneg hc₂ (Real.rpow_nonneg dp.le _)
  have l₃ : 0 ≤ weight₃ := mul_nonneg hc₃ (Real.rpow_nonneg dp.le _)
  have m0 (t : ℝ) (j : ℕ) : 0 ≤ M t j :=
    div_nonneg (sum_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
  let R (j : ℕ) := uniformMean (fun base => ∑ i, ((paths i ∩ degreeBucket paths base h j).card:ℝ)^2)
  have per (j : ℕ) : Real.sqrt (R j) ≤
      Real.sqrt weight₁*Real.sqrt (M 1 j) +
      Real.sqrt weight₂*Real.sqrt (M (3/2) j) + Real.sqrt weight₃*Real.sqrt (M (1/b) j) := by
    have bound : R j ≤ weight₁*M 1 j+weight₂*M (3/2) j+weight₃*M (1/b) j := by
      have w := lemma34_mean_bucket_moment free h j L D L0 D0 Cpos (by linarith) ha₁ hb
        (by linarith) lengths degree prior
      simpa only [R, weight₁, weight₂, weight₃, c₂, c₃, γ, e, M, P, d, ℓ, Real.rpow_one] using w
    calc
      _ ≤ Real.sqrt (weight₁*M 1 j+weight₂*M (3/2) j+weight₃*M (1/b) j) := Real.sqrt_le_sqrt bound
      _ ≤ Real.sqrt (weight₁*M 1 j)+Real.sqrt (weight₂*M (3/2) j)+Real.sqrt (weight₃*M (1/b) j) := by
        have c₁ := mul_nonneg l₁ (m0 1 j)
        have c₂ := mul_nonneg l₂ (m0 (3/2) j)
        have c₃ := mul_nonneg l₃ (m0 (1/b) j)
        exact (sqrt_add_le_nonneg (add_nonneg c₁ c₂) c₃).trans
          (add_le_add (sqrt_add_le_nonneg c₁ c₂) le_rfl)
      _ = _ := by rw [Real.sqrt_mul l₁, Real.sqrt_mul l₂, Real.sqrt_mul l₃]
  have step : (∑ j ∈ J, (2:ℝ)^j*Real.sqrt (R j)) ≤
      Real.sqrt weight₁*W 1+Real.sqrt weight₂*W (3/2)+Real.sqrt weight₃*W (1/b) := calc
    _ ≤ ∑ j ∈ J, (2:ℝ)^j*(Real.sqrt weight₁*Real.sqrt (M 1 j) +
        Real.sqrt weight₂*Real.sqrt (M (3/2) j)+Real.sqrt weight₃*Real.sqrt (M (1/b) j)) :=
      sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (per j) (pow_nonneg (by norm_num) j))
    _ = ∑ j ∈ J, (Real.sqrt weight₁*((2:ℝ)^j*Real.sqrt (M 1 j)) +
        Real.sqrt weight₂*((2:ℝ)^j*Real.sqrt (M (3/2) j)) +
        Real.sqrt weight₃*((2:ℝ)^j*Real.sqrt (M (1/b) j))) := by
      apply sum_congr rfl
      intro j _
      ring
    _ = _ := by simp only [W, sum_add_distrib, ← mul_sum]
  let U₁ := Real.sqrt weight₁*(A₁*z^(1/2:ℝ)*x₀^(1-1/2:ℝ))
  let U₂ := Real.sqrt weight₂*(A₂*z^((3/2:ℝ)/2)*x₀^(1-(3/2:ℝ)/2))
  let U₃ := Real.sqrt weight₃*(A₃*z^((1/b)/2)*x₀^(1-(1/b)/2))
  have g₁ : W 1 ≤ A₁*z^(1/2:ℝ)*x₀^(1-1/2:ℝ) :=
    root₁ free L D h hp L0 hh hD ratio lengths degree prior
  have g₂ : W (3/2) ≤ A₂*z^((3/2:ℝ)/2)*x₀^(1-(3/2:ℝ)/2) :=
    root₂ free L D h hp L0 hh hD ratio lengths degree prior
  have g₃ : W (1/b) ≤ A₃*z^((1/b)/2)*x₀^(1-(1/b)/2) :=
    root₃ free L D h hp L0 hh hD ratio lengths degree prior
  have root : Real.sqrt Q ≤ 2*(U₁+U₂+U₃) := calc
    _ ≤ 2*∑ j ∈ J, (2:ℝ)^j*Real.sqrt (R j) := lemma34_minkowski_mean free h D hp degree
    _ ≤ 2*(Real.sqrt weight₁*W 1+Real.sqrt weight₂*W (3/2)+Real.sqrt weight₃*W (1/b)) :=
      mul_le_mul_of_nonneg_left step (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left g₁ (Real.sqrt_nonneg _))
        (mul_le_mul_of_nonneg_left g₂ (Real.sqrt_nonneg _)))
      (mul_le_mul_of_nonneg_left g₃ (Real.sqrt_nonneg _))) (by norm_num)
  have q0 : 0 ≤ Q := div_nonneg (sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have nonneg₁ : 0 ≤ U₁ := by dsimp only [U₁]; positivity
  have nonneg₂ : 0 ≤ U₂ := by dsimp only [U₂]; positivity
  have nonneg₃ : 0 ≤ U₃ := by dsimp only [U₃]; positivity
  have qBound : Q ≤ 12*(U₁^2+U₂^2+U₃^2) := calc
    _ = (Real.sqrt Q)^2 := (Real.sq_sqrt q0).symm
    _ ≤ (2*(U₁+U₂+U₃))^2 := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr root
    _ ≤ _ := by nlinarith only [sq_nonneg (U₁-U₂), sq_nonneg (U₂-U₃), sq_nonneg (U₃-U₁)]
  let F₁ := ℓ^2*d*u^(1/b)
  let F₂ := ℓ^(3/2:ℝ)*d^(3/2+γ)*u^((2*b+1)/(2*b))
  let F₃ := ℓ^(1/b)*d^2*u^((4*b-2*b^2-1)/b^2)
  have f₁ : 0 ≤ F₁ := by dsimp only [F₁]; positivity
  have f₂ : 0 ≤ F₂ := by dsimp only [F₂]; positivity
  have f₃ : 0 ≤ F₃ := by dsimp only [F₃]; positivity
  have ℓ1 : 1 ≤ ℓ := by change (1:ℝ) ≤ L; exact_mod_cast (show 1 ≤ L from L0)
  have u1 : 1 ≤ u := by change (1:ℝ) ≤ h; exact_mod_cast (show 1 ≤ h from hh)
  obtain ⟨p₁,p₂,p₃⟩ := lemma34_weighted_powers (a := a) ℓ1 dp u1 hb (by linarith)
  have U1Bound : U₁^2 ≤ k₁*(F₁+F₃) := calc
    _ = weight₁*A₁^2*z^(1:ℝ)*x₀^(2-1:ℝ) := squared_weight l₁ zp.le xp.le
    _ = k₁*((ℓ+d)*z*x₀) := by norm_num [Real.rpow_one]; dsimp only [k₁, weight₁]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left p₁ hk₁
  have U2Bound : U₂^2 = k₂*F₂ := calc
    _ = weight₂*A₂^2*z^(3/2:ℝ)*x₀^(2-3/2:ℝ) := squared_weight l₂ zp.le xp.le
    _ = k₂*(d^γ*z^(3/2:ℝ)*x₀^(1/2:ℝ)) := by norm_num; dsimp only [k₂, weight₂]; ring
    _ = _ := by rw [p₂]
  have U3Bound : U₃^2 = k₃*F₃ := calc
    _ = weight₃*A₃^2*z^(1/b)*x₀^(2-1/b) := squared_weight l₃ zp.le xp.le
    _ = k₃*(d^e*z^(1/b)*x₀^(2-1/b)) := by dsimp only [k₃, weight₃]; ring
    _ = _ := by rw [p₃]
  have powers : U₁^2+U₂^2+U₃^2 ≤ K*(F₁+F₂+F₃) := by
    rw [U2Bound, U3Bound]
    calc
      _ ≤ k₁*(F₁+F₃)+k₂*F₂+k₃*F₃ := add_le_add (add_le_add U1Bound le_rfl) le_rfl
      _ = k₁*F₁+k₂*F₂+(k₁+k₃)*F₃ := by ring
      _ ≤ K*F₁+K*F₂+K*F₃ := add_le_add
        (add_le_add (mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) f₁)
          (mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) f₂))
        (mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) f₃)
      _ = _ := by ring
  exact qBound.trans ((mul_le_mul_of_nonneg_left powers (by norm_num)).trans_eq (by ring))

private theorem cap_rpow_le {x y r : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hr : 0 ≤ r) (hr' : r ≤ 2)
    (cap : x ≤ 4*y) : x^r ≤ 16*y^r := calc
  _ ≤ (4*y)^r := Real.rpow_le_rpow hx cap hr
  _ = (4:ℝ)^r*y^r := Real.mul_rpow (by norm_num) hy
  _ ≤ _ := by
    have h : (4:ℝ)^r ≤ 16 :=
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hr').trans_eq (by norm_num [Real.rpow_two])
    exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hy _)

set_option maxHeartbeats 500000 in
/-- The normalized off-base expectation of Lemma 34 on the actual acyclic
sample. Both deterministic caps are within four times the original averages. -/
theorem lemma34_off_base_expectation {C a b : ℝ} (hC : 1 ≤ C) (ha₀ : 7/10 ≤ a)
    (ha₁ : a < 3/4) (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 3/4) :
    ∃ A > 0, ∀ {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype V] [Fintype I]
      {paths : I → Finset V} (_ : HalfBridgeFree (PathBefore paths) 4) (L D h : ℕ),
      0 < Fintype.card V → 0 < Fintype.card I → 0 < h → h ≤ L → h ≤ D →
      (∀ i, (paths i).card ≤ L) →
      (∀ v, (occurrences paths v).card ≤ D) → InducedSizeBound paths C a b →
      let n := Fintype.card V
      let p := Fintype.card I
      let M := ∑ i, (paths i).card
      0 < M → L*p ≤ 4*M → D*n ≤ 4*M →
      let ℓ : ℝ := (M:ℝ)/p
      let d : ℝ := (M:ℝ)/n
      let u : ℝ := h
      uniformMean (fun base => ((offBaseBranchTuples paths base h).card:ℝ)) ≤
        A*(ℓ^2*d*u^(1/b) +
          ℓ^(3/2:ℝ)*d^(3/2+(3-4*a)/(2-2*a))*u^((2*b+1)/(2*b)) +
          ℓ^(1/b)*d^2*u^((4*b-2*b^2-1)/b^2)) := by
  obtain ⟨K, hK, bound⟩ := lemma34_off_base_cap_expectation hC ha₀ ha₁ hb₀ hb₁
  refine ⟨256*K, by positivity, ?_⟩
  intro V I _ _ _ _ paths free L D h hn hp hh hL hD length degree input
  dsimp only
  let n := Fintype.card V
  let p := Fintype.card I
  let M := ∑ i, (paths i).card
  intro hm Lcap Dcap
  let ℓ : ℝ := (M:ℝ)/p
  let d : ℝ := (M:ℝ)/n
  let u : ℝ := h
  let γ := (3-4*a)/(2-2*a)
  let r := 3/2+γ
  let s := (2*b+1)/(2*b)
  let w := (4*b-2*b^2-1)/b^2
  have ratio : n*D ≤ 4*p*L := calc
    _ ≤ 4*M := (Nat.mul_comm n D).le.trans Dcap
    _ ≤ 4*(p*L) := Nat.mul_le_mul_left _ (by
      calc
        M ≤ ∑ _ : I, L := sum_le_sum (fun i _ => length i)
        _ = _ := by simp [p])
    _ = _ := by ring
  have ppos : (0:ℝ) < p := Nat.cast_pos.mpr hp
  have npos : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have mpos : (0:ℝ) < M := Nat.cast_pos.mpr hm
  have ℓp : 0 < ℓ := div_pos mpos ppos
  have dp : 0 < d := div_pos mpos npos
  have Lcap' : (L:ℝ) ≤ 4*ℓ := by
    change (L:ℝ) ≤ 4*((M:ℝ)/p)
    rw [← mul_div_assoc, le_div_iff₀ ppos]
    exact_mod_cast Lcap
  have Dcap' : (D:ℝ) ≤ 4*d := by
    change (D:ℝ) ≤ 4*((M:ℝ)/n)
    rw [← mul_div_assoc, le_div_iff₀ npos]
    exact_mod_cast Dcap
  have gden : 0 < 2-2*a := by linarith
  have g0 : 0 ≤ γ := div_nonneg (by linarith) gden.le
  have g1 : γ ≤ 1/2 := (div_le_iff₀ gden).mpr (by linarith)
  have r0 : 0 ≤ r := by dsimp only [r]; linarith
  have r1 : r ≤ 2 := by dsimp only [r]; linarith
  have bp : 0 < b := by linarith
  have ib0 := (one_div_pos.mpr bp).le
  have ib1 : 1/b ≤ 2 := (div_le_iff₀ bp).mpr (by linarith)
  have lift {a b t : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 2) (hb : 0 ≤ b) (hb' : b ≤ 2) :
      (L:ℝ)^a*(D:ℝ)^b*u^t ≤ 256*(ℓ^a*d^b*u^t) :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul (cap_rpow_le (Nat.cast_nonneg L) ℓp.le ha ha' Lcap')
        (cap_rpow_le (Nat.cast_nonneg D) dp.le hb hb' Dcap')
        (Real.rpow_nonneg (Nat.cast_nonneg D) _)
        (mul_nonneg (by norm_num) (Real.rpow_nonneg ℓp.le _)))
      (Real.rpow_nonneg (Nat.cast_nonneg h) _)).trans_eq (by ring)
  have h₁ : (L:ℝ)^2*(D:ℝ)*u^(1/b) ≤ 256*(ℓ^2*d*u^(1/b)) := by
    simpa only [Real.rpow_two, Real.rpow_one] using
      lift (a := 2) (b := 1) (t := 1/b) (by norm_num) le_rfl (by norm_num) (by norm_num)
  have h₂ : (L:ℝ)^(3/2:ℝ)*(D:ℝ)^r*u^s ≤ 256*(ℓ^(3/2:ℝ)*d^r*u^s) :=
    lift (by norm_num) (by norm_num) r0 r1
  have h₃ : (L:ℝ)^(1/b)*(D:ℝ)^2*u^w ≤ 256*(ℓ^(1/b)*d^2*u^w) := by
    simpa only [Real.rpow_two] using lift (a := 1/b) (b := 2) (t := w) ib0 ib1 (by norm_num) le_rfl
  have stage := bound free L D h hp hh hL hD ratio length degree input
  exact stage.trans ((mul_le_mul_of_nonneg_left (add_le_add (add_le_add h₁ h₂) h₃) hK.le).trans_eq (by ring))



/-- The complete upper count of Lemma 36 in the acyclic regime. The two
coefficients keep the linear on-base contribution available for absorption. -/
theorem lemma36_acyclic_expectation {C a b : ℝ} (hC : 1 ≤ C) (ha₀ : 7/10 ≤ a)
    (ha₁ : a < 3/4) (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 3/4) :
    ∃ A > 0, ∃ B > 0, ∀ {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype V] [Fintype I]
      {paths : I → Finset V} (_ : HalfBridgeFree (PathBefore paths) 4) (L D h : ℕ),
      0 < Fintype.card V → 0 < Fintype.card I → 0 < h → h ≤ L → h ≤ D →
      (∀ i, (paths i).card ≤ L) →
      (∀ v, (occurrences paths v).card ≤ D) → InducedSizeBound paths C a b →
      let n := Fintype.card V
      let p := Fintype.card I
      let M := ∑ i, (paths i).card
      0 < M → L*p ≤ 4*M → D*n ≤ 4*M →
      let ℓ : ℝ := (M:ℝ)/p
      let d : ℝ := (M:ℝ)/n
      let u : ℝ := h
      uniformMean (fun base => ((branchTuples paths base h).card:ℝ)) ≤
        A*(ℓ^2*d*u^(1/b) +
          ℓ^(3/2:ℝ)*d^(3/2+(3-4*a)/(2-2*a))*u^((2*b+1)/(2*b)) +
          ℓ^(1/b)*d^2*u^((4*b-2*b^2-1)/b^2)) + B*(ℓ^2*d^2+ℓ^(3/2:ℝ)*d^2*u^(5/4:ℝ)) := by
  obtain ⟨A, hA, off⟩ := lemma34_off_base_expectation hC ha₀ ha₁ hb₀ hb₁
  obtain ⟨B, hB, on⟩ := lemma35_on_base_expectation hC
    (show 2/3 ≤ a by linarith) ha₁.le hb₀ hb₁
  refine ⟨A,hA,B,hB,?_⟩
  intro V I _ _ _ _ paths free L D h hn hp hh hL hD lengths degree input
  dsimp only
  intro hM Lcap Dcap
  let offMean := uniformMean (fun base => ((offBaseBranchTuples paths base h).card:ℝ))
  let onMean := uniformMean (fun base => ((onBaseBranchTuples paths base h).card:ℝ))
  have eq : uniformMean (fun base => ((branchTuples paths base h).card:ℝ)) = offMean+onMean := by
    dsimp only [offMean,onMean,uniformMean]
    simp_rw [branchTuples_partition, Nat.cast_add, sum_add_distrib, add_div]
    ring
  rw [eq]
  exact add_le_add
    (off free L D h hn hp hh hL hD lengths degree input hM Lcap Dcap)
    (on free L D h hn hp hh hL hD lengths degree input hM Lcap Dcap)

end OnlineReachabilityPreservers
