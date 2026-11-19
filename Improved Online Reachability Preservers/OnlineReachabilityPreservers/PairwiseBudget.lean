import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OnlineReachabilityPreservers.PairwiseInitial
import OnlineReachabilityPreservers.IndexSensitive

/-! Integer quotas for the all-pairs instantiations of Theorems 15 and 16. -/

namespace OnlineReachabilityPreservers

open Finset

private noncomputable def quotaProfile (n A B a b q : ℝ) : ℝ :=
  max n (max (A*q^a) (B*q^b))

private noncomputable def sharpQuota (a b e n q : ℝ) : ℝ :=
  quotaProfile n (n^(a+e)) (n^(2-2*b+e)) (2-2*a) b q

private noncomputable def initialQuota (n q : ℝ) : ℝ :=
  quotaProfile n (n^(2/3:ℝ)) 0 (2/3) 1 q

private noncomputable def pairwiseQuota (a b e K n q : ℝ) : ℝ :=
  min (K*sharpQuota a b e n q) (16*initialQuota n q)

/-- A bound for forward growth using both the sharp and the initial pairwise rates. -/
noncomputable def pairwiseBudget (a b e K : ℝ) (n q : ℕ) : ℕ :=
  ⌈pairwiseQuota a b e K n q⌉₊

/-- Start the dyadic schedule at a positive integer between √n and 2√n. -/
def pairwiseBase (n : ℕ) : ℕ := Nat.sqrt n + 1

private theorem pairwiseBase_bounds {n : ℕ} (hn : 0 < n) :
    Real.sqrt (n:ℝ) ≤ pairwiseBase n ∧ (pairwiseBase n:ℝ) ≤ 2*Real.sqrt (n:ℝ) := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ (n:ℝ))
  have h0 := Real.sqrt_nonneg (n:ℝ)
  have upper : (n:ℝ) ≤ (pairwiseBase n:ℝ)^2 := by
    exact_mod_cast (Nat.lt_succ_sqrt' n).le
  have lower : (Nat.sqrt n:ℝ)^2 ≤ (n:ℝ) := by
    exact_mod_cast Nat.sqrt_le' n
  have hl : (Nat.sqrt n:ℝ) ≤ Real.sqrt (n:ℝ) := by
    apply (sq_le_sq₀ (by positivity) h0).mp
    rwa [hs]
  have h1 : (1:ℝ) ≤ Real.sqrt (n:ℝ) := by
    have h : (1:ℝ) ≤ n := by exact_mod_cast hn
    simpa using Real.sqrt_le_sqrt h
  refine ⟨(sq_le_sq₀ h0 (by positivity)).mp (by rwa [hs]), ?_⟩
  push_cast [pairwiseBase]
  linarith only [hl,h1]

private theorem pairwiseQuota_ge {a b e K n q : ℝ} (hK : 1 ≤ K) (hn : 0 ≤ n) :
    n ≤ pairwiseQuota a b e K n q := by
  apply le_min
  · have m : n ≤ sharpQuota a b e n q := le_max_left _ _
    linarith only [mul_le_mul_of_nonneg_right hK hn, mul_le_mul_of_nonneg_left m
      (zero_le_one.trans hK)]
  · have m : n ≤ initialQuota n q := le_max_left _ _
    linarith

private theorem quotaProfile_mono {n A B a b x y : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (hxy : x ≤ y) :
    quotaProfile n A B a b x ≤ quotaProfile n A B a b y := by
  unfold quotaProfile
  exact max_le_max le_rfl (max_le_max
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxy ha) hA)
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxy hb) hB))

private theorem quotaProfile_dilate_le {n A B a b q : ℝ}
    (hn : 0 ≤ n) (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : a ≤ 1) (hb : b ≤ 1) (hq : 0 ≤ q) :
    quotaProfile n A B a b (2*q) ≤ 2*quotaProfile n A B a b q := by
  have power (c r : ℝ) (hc : 0 ≤ c) (hr : r ≤ 1) :
      c*(2*q)^r ≤ 2*(c*q^r) := by
    rw [Real.mul_rpow (by norm_num : 0 ≤ (2:ℝ)) hq]
    have hh : (2:ℝ)^r ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) hr
    calc
      _ = (2:ℝ)^r*(c*q^r) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hh (mul_nonneg hc (Real.rpow_nonneg hq _))
  unfold quotaProfile
  rw [mul_max_of_nonneg _ _ (by norm_num : 0 ≤ (2:ℝ)),
    mul_max_of_nonneg _ _ (by norm_num : 0 ≤ (2:ℝ))]
  exact max_le_max (by linarith) (max_le_max (power A a hA ha) (power B b hB hb))

private theorem quotaProfile_dilate_ge {n A B a b q : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 1/2 ≤ a) (hb : 1/2 ≤ b) (hq : 0 ≤ q)
    (hd : n ≤ max (A*q^a) (B*q^b)) :
    (4/3)*quotaProfile n A B a b q ≤ quotaProfile n A B a b (2*q) := by
  have rt : (4/3:ℝ) ≤ Real.sqrt 2 := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg 2)).mp
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  have power (c r : ℝ) (hc : 0 ≤ c) (hr : 1/2 ≤ r) :
      (4/3)*(c*q^r) ≤ c*(2*q)^r := by
    have hh : (4/3:ℝ) ≤ (2:ℝ)^r := by
      rw [Real.sqrt_eq_rpow] at rt
      exact rt.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hr)
    rw [Real.mul_rpow (by norm_num : 0 ≤ (2:ℝ)) hq, mul_left_comm c]
    exact mul_le_mul_of_nonneg_right hh (mul_nonneg hc (Real.rpow_nonneg hq _))
  unfold quotaProfile
  rw [max_eq_right hd, mul_max_of_nonneg _ _ (by norm_num : 0 ≤ (4/3:ℝ))]
  exact (max_le_max (power A a hA ha) (power B b hB hb)).trans (le_max_right _ _)

private theorem sharpQuota_dominate {a e n q : ℝ}
    (hn : 1 ≤ n) (ha : a ≤ 1) (he : 0 ≤ e) (hqn : Real.sqrt n ≤ q) :
    n ≤ n^(a+e)*q^(2-2*a) := by
  have hn0 := zero_lt_one.trans_le hn
  have m := Real.rpow_le_rpow (Real.sqrt_nonneg n) hqn (by linarith : 0 ≤ 2-2*a)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le,
    show (1/2:ℝ)*(2-2*a) = 1-a by ring] at m
  calc
    n = n^a*n^(1-a) := by
      rw [← Real.rpow_add hn0, show a+(1-a)=1 by ring, Real.rpow_one]
    _ ≤ _ := mul_le_mul (Real.rpow_le_rpow_of_exponent_le hn (by linarith)) m
      (Real.rpow_nonneg hn0.le _) (Real.rpow_nonneg hn0.le _)

private theorem initialQuota_dominate {n q : ℝ} (hn : 1 ≤ n) (hqn : Real.sqrt n ≤ q) :
    n ≤ n^(2/3:ℝ)*q^(2/3:ℝ) := by
  have h := sharpQuota_dominate (a := (2/3:ℝ)) (e := 0) hn (by norm_num) le_rfl hqn
  norm_num at h ⊢
  exact h

private theorem pairwiseQuota_dilate_ge {a b e K n q : ℝ}
    (hn : 1 ≤ n) (ha : a ≤ 3/4) (hb : 1/2 ≤ b) (he : 0 ≤ e) (hK : 1 ≤ K)
    (hqn : Real.sqrt n ≤ q) :
    (4/3)*pairwiseQuota a b e K n q ≤ pairwiseQuota a b e K n (2*q) := by
  have n0 := zero_le_one.trans hn
  have q0 := (Real.sqrt_nonneg n).trans hqn
  have sharp : (4/3)*sharpQuota a b e n q ≤ sharpQuota a b e n (2*q) :=
    quotaProfile_dilate_ge (Real.rpow_nonneg n0 _) (Real.rpow_nonneg n0 _)
      (by linarith) hb q0 (le_max_of_le_left (sharpQuota_dominate hn (by linarith) he hqn))
  have init : (4/3)*initialQuota n q ≤ initialQuota n (2*q) :=
    quotaProfile_dilate_ge (Real.rpow_nonneg n0 _) le_rfl
      (by norm_num) (by norm_num) q0 (le_max_of_le_left (initialQuota_dominate hn hqn))
  unfold pairwiseQuota
  rw [mul_min_of_nonneg _ _ (by norm_num : 0 ≤ (4/3:ℝ)), mul_left_comm (4/3:ℝ) K,
    mul_left_comm (4/3:ℝ) 16]
  exact min_le_min (mul_le_mul_of_nonneg_left sharp (zero_le_one.trans hK))
    (mul_le_mul_of_nonneg_left init (by norm_num))

private theorem pairwiseQuota_mono {a b e K n : ℝ} (hn : 0 ≤ n)
    (ha : a ≤ 1) (hb : 0 ≤ b) (hK : 0 ≤ K) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    pairwiseQuota a b e K n x ≤ pairwiseQuota a b e K n y := by
  unfold pairwiseQuota sharpQuota initialQuota
  exact min_le_min
    (mul_le_mul_of_nonneg_left (quotaProfile_mono (Real.rpow_nonneg hn _)
      (Real.rpow_nonneg hn _) (by linarith) hb hx hxy) hK)
    (mul_le_mul_of_nonneg_left (quotaProfile_mono (Real.rpow_nonneg hn _)
      le_rfl (by norm_num) (by norm_num) hx hxy) (by norm_num))

private theorem pairwiseQuota_dilate_le {a b e K n q : ℝ}
    (hn : 0 ≤ n) (ha : 1/2 ≤ a) (hb : b ≤ 1) (hK : 0 ≤ K) (hq : 0 ≤ q) :
    pairwiseQuota a b e K n (2*q) ≤ 2*pairwiseQuota a b e K n q := by
  unfold pairwiseQuota sharpQuota initialQuota
  rw [mul_min_of_nonneg _ _ (by norm_num : 0 ≤ (2:ℝ)), mul_left_comm (2:ℝ) K,
    mul_left_comm (2:ℝ) 16]
  exact min_le_min (mul_le_mul_of_nonneg_left (quotaProfile_dilate_le hn
    (Real.rpow_nonneg hn _) (Real.rpow_nonneg hn _) (by linarith) hb hq) hK)
    (mul_le_mul_of_nonneg_left (quotaProfile_dilate_le hn (Real.rpow_nonneg hn _)
      le_rfl (by norm_num) le_rfl hq) (by norm_num))


private theorem pairwiseBudget_lower {a b e K : ℝ} {n q : ℕ} (hK : 1 ≤ K) :
    n ≤ pairwiseBudget a b e K n q := by
  apply Nat.cast_le (α := ℝ) |>.mp
  exact (pairwiseQuota_ge hK (by positivity)).trans (Nat.le_ceil _)

private theorem pairwiseQuota_small {a b e K n q : ℝ}
    (hn : 1 ≤ n) (hq : 0 ≤ q) (hqn : q ≤ 2*Real.sqrt n) :
    pairwiseQuota a b e K n q ≤ 32*n := by
  have hn0 := zero_lt_one.trans_le hn
  have atRoot : initialQuota n (Real.sqrt n) = n := by
    have hpow : n^(2/3:ℝ)*(Real.sqrt n)^(2/3:ℝ) = n := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le, ← Real.rpow_add hn0,
        show (2/3:ℝ)+(1/2)*(2/3)=1 by norm_num, Real.rpow_one]
    simp [initialQuota, quotaProfile, hpow, hn0.le]
  have leRoot : initialQuota n q ≤ initialQuota n (2*Real.sqrt n) :=
    quotaProfile_mono (Real.rpow_nonneg hn0.le _) le_rfl (by norm_num) (by norm_num) hq hqn
  have twoRoot : initialQuota n (2*Real.sqrt n) ≤ 2*n := by
    calc
      _ ≤ 2*initialQuota n (Real.sqrt n) := quotaProfile_dilate_le hn0.le
        (Real.rpow_nonneg hn0.le _) le_rfl (by norm_num) (show (1:ℝ) ≤ 1 from le_rfl)
        (Real.sqrt_nonneg _)
      _ = _ := by rw [atRoot]
  exact (min_le_right _ _).trans (by linarith only [leRoot,twoRoot])

/-- The actual quotas for Algorithm 5 satisfy the summability requirement of Theorem 16. -/
theorem pairwiseBudget_dyadic_sum {a b e K : ℝ} {n : ℕ} (hn : 0 < n)
    (ha : a ≤ 3/4) (hb : 1/2 ≤ b) (he : 0 ≤ e) (hK : 1 ≤ K) (k : ℕ) :
    (∑ j ∈ range (k+1), pairwiseBudget a b e K n (dyadicQuota (pairwiseBase n) j)) ≤
      8 * pairwiseBudget a b e K n (dyadicQuota (pairwiseBase n) k) := by
  let R (j : ℕ) := pairwiseQuota a b e K n (dyadicQuota (pairwiseBase n) j)
  have n1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have lower (i : ℕ) : 1 ≤ R i :=
    n1.trans (pairwiseQuota_ge hK (zero_le_one.trans n1))
  have growth (i : ℕ) : (4/3)*R i ≤ R (i+1) := by
    have hq : Real.sqrt (n:ℝ) ≤ (dyadicQuota (pairwiseBase n) i:ℝ) := by
      apply (pairwiseBase_bounds hn).1.trans
      exact_mod_cast (show pairwiseBase n ≤ dyadicQuota (pairwiseBase n) i by
        unfold dyadicQuota
        exact Nat.le_mul_of_pos_right _ (by positivity))
    dsimp only [R]
    rw [dyadicQuota_succ, Nat.cast_mul, Nat.cast_ofNat]
    exact pairwiseQuota_dilate_ge n1 ha hb he hK hq
  have sum (i : ℕ) : (∑ j ∈ range (i+1), R j) ≤ 4*R i := by
    induction i with
    | zero =>
      simpa only [zero_add, range_one, sum_singleton] using
        (show R 0 ≤ 4*R 0 by linarith only [lower 0])
    | succ i ih =>
      rw [sum_range_succ]
      linarith only [ih,growth i]
  have rounding (i : ℕ) : (⌈R i⌉₊:ℝ) ≤ 2*R i := by
    linarith only [Nat.ceil_lt_add_one (zero_le_one.trans (lower i)), lower i]
  apply Nat.cast_le (α := ℝ) |>.mp
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat]
  change (∑ j ∈ range (k+1), (⌈R j⌉₊:ℝ)) ≤ 8*(⌈R k⌉₊:ℝ)
  calc
    _ ≤ ∑ j ∈ range (k+1), 2*R j := sum_le_sum (fun i _ => rounding i)
    _ = 2*(∑ j ∈ range (k+1), R j) := (mul_sum ..).symm
    _ ≤ 8*(⌈R k⌉₊:ℝ) := by linarith only [sum k, Nat.le_ceil (R k)]

/-- The last quota is comparable to the budget at the actual demand count. -/
theorem pairwiseBudget_final_quota {a b e K : ℝ} {n p : ℕ} (hn : 0 < n) (hp : 0 < p)
    (ha₀ : 1/2 ≤ a) (ha₁ : a ≤ 3/4) (hb₀ : 1/2 ≤ b) (hb₁ : b ≤ 1) (hK : 1 ≤ K) :
    pairwiseBudget a b e K n (dyadicQuota (pairwiseBase n) (indexLevel (pairwiseBase n) (p-1))) ≤
      32 * pairwiseBudget a b e K n p := by
  let base := pairwiseBase n
  let q := dyadicQuota base (indexLevel base (p-1))
  have basePos : 0 < base := by simp [base,pairwiseBase]
  have bound := finalQuota_le basePos hp
  have n1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have n0 := zero_le_one.trans n1
  by_cases small : 2*p ≤ base
  · have qle : q ≤ base := by simpa only [max_eq_left small] using bound
    have realQ : (q:ℝ) ≤ 2*Real.sqrt (n:ℝ) :=
      (Nat.cast_le.mpr qle).trans (pairwiseBase_bounds hn).2
    have h := pairwiseQuota_small (a := a) (b := b) (e := e) (K := K) n1
      (show 0 ≤ (q:ℝ) by positivity) realQ
    have hceil : pairwiseBudget a b e K n q ≤ 32*n := by
      apply Nat.ceil_le.mpr
      exact_mod_cast h
    exact hceil.trans (Nat.mul_le_mul_left _ (pairwiseBudget_lower hK))
  · have qle : q ≤ 2*p := by simpa only [max_eq_right (le_of_not_ge small)] using bound
    have h := pairwiseQuota_mono (a := a) (b := b) (e := e) n0
      (show a ≤ 1 by linarith only [ha₁]) (show 0 ≤ b by linarith only [hb₀])
      (zero_le_one.trans hK) (show 0 ≤ (q:ℝ) by positivity)
      (show (q:ℝ) ≤ 2*(p:ℝ) by exact_mod_cast qle)
    have hh := pairwiseQuota_dilate_le (e := e) n0 ha₀ hb₁ (zero_le_one.trans hK)
      (show 0 ≤ (p:ℝ) by positivity)
    have hceil : pairwiseBudget a b e K n q ≤ 2*pairwiseBudget a b e K n p := by
      apply Nat.ceil_le.mpr
      push_cast
      exact h.trans (hh.trans (mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by norm_num)))
    exact hceil.trans (Nat.mul_le_mul_right _ (by norm_num))


/-- The two monomials and linear term used for both pairwise rates. -/
noncomputable def pairwiseRate (a b e n p : ℝ) : ℝ :=
  n+n^(a+e)*p^(2-2*a)+n^(2-2*b+e)*p^b

theorem pairwiseRate_nonneg {a b e n p : ℝ} (hn : 0 ≤ n) (hp : 0 ≤ p) :
    0 ≤ pairwiseRate a b e n p := by
  unfold pairwiseRate
  positivity

theorem pairwiseRate_mono {a b e n p q : ℝ} (hn : 0 ≤ n) (ha : a ≤ 1) (hb : 0 ≤ b)
    (hp : 0 ≤ p) (hpq : p ≤ q) : pairwiseRate a b e n p ≤ pairwiseRate a b e n q := by
  unfold pairwiseRate
  have h₁ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hp hpq (show 0 ≤ 2-2*a by linarith))
    (Real.rpow_nonneg hn (a+e))
  have h₂ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hp hpq hb)
    (Real.rpow_nonneg hn (2-2*b+e))
  linarith only [h₁,h₂]

theorem pairwiseBudget_le_rate {a b e K : ℝ} {n q : ℕ} (hn : 0 < n) (hK : 1 ≤ K) :
    (pairwiseBudget a b e K n q:ℝ) ≤ (K+1)*pairwiseRate a b e n q := by
  let R := pairwiseRate a b e (n:ℝ) (q:ℝ)
  have n1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have n0 := zero_le_one.trans n1
  have t₁ : 0 ≤ (n:ℝ)^(a+e)*(q:ℝ)^(2-2*a) := by positivity
  have t₂ : 0 ≤ (n:ℝ)^(2-2*b+e)*(q:ℝ)^b := by positivity
  have R1 : 1 ≤ R := by dsimp [R,pairwiseRate]; linarith only [n1,t₁,t₂]
  have mx : sharpQuota a b e n q ≤ R := by
    apply max_le
    · dsimp [R,pairwiseRate]
      linarith only [t₁,t₂]
    · apply max_le <;> dsimp [R,pairwiseRate] <;> linarith only [n0,t₁,t₂]
  let B := pairwiseQuota a b e K n q
  have B0 : 0 ≤ B := n0.trans (pairwiseQuota_ge hK n0)
  have BR : B ≤ K*R := (min_le_left _ _).trans
    (mul_le_mul_of_nonneg_left mx (zero_le_one.trans hK))
  change (⌈B⌉₊:ℝ) ≤ (K+1)*R
  linarith only [Nat.ceil_lt_add_one B0, BR,R1]

universe u
variable {V : Type u} [LinearOrder V] [Fintype V]

private theorem forwardRun_initial_quota {G : Arcs V} (dag : IsDAG G) (D : List (V × V)) :
    ((forwardRun G D).card:ℝ) ≤ 16*initialQuota (Fintype.card V) D.length := by
  let n := Fintype.card V
  let m := (forwardRun G D).card
  let p := D.length
  change (m:ℝ) ≤ 16*initialQuota (n:ℝ) p
  have h := forwardRun_pairwise_initial dag D
  change m ≤ 16*n ∨ m^3 ≤ 2048*(n*p)^2 at h
  rcases h with h | h
  · have hh : (m:ℝ) ≤ 16*(n:ℝ) := by exact_mod_cast h
    exact hh.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
  · let x := ((n:ℝ)*(p:ℝ))^(2/3:ℝ)
    have x0 : 0 ≤ x := by dsimp only [x]; positivity
    have cube : x^3 = ((n:ℝ)*(p:ℝ))^2 := by
      dsimp only [x]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show (2/3:ℝ)*((3:ℕ):ℝ)=2 by norm_num, Real.rpow_two]
    have hm : (m:ℝ)^3 ≤ 2048*((n:ℝ)*(p:ℝ))^2 := by exact_mod_cast h
    have mm : (m:ℝ) ≤ 16*x := by
      apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ (m:ℝ))
        (show 0 ≤ 16*x by positivity) (by decide : (3:ℕ) ≠ 0)).mp
      rw [mul_pow, cube]
      norm_num
      exact hm.trans (mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg ((n:ℝ)*(p:ℝ))))
    apply mm.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    dsimp only [x,initialQuota,quotaProfile]
    rw [Real.mul_rpow (by positivity) (by positivity)]
    exact le_max_of_le_right (le_max_left _ _)

/-- The sharp and initial bounds together certify an analytical ceiling for any quota. -/
theorem forwardRun_pairwise_budget {G : Arcs V} (dag : IsDAG G) {a b e K : ℝ}
    {q : ℕ} (D : List (V × V)) (hl : D.length ≤ q) (hK : 0 ≤ K)
    (sharp : ((forwardRun G D).card:ℝ) ≤ K*pairwiseRate a b e (Fintype.card V) q) :
    (forwardRun G D).card ≤ pairwiseBudget a b e (3*K) (Fintype.card V) q := by
  let n := Fintype.card V
  let B := pairwiseQuota a b e (3*K) (n:ℝ) q
  have mono : initialQuota (n:ℝ) D.length ≤ initialQuota (n:ℝ) q :=
    quotaProfile_mono (Real.rpow_nonneg (by positivity) _) le_rfl (by norm_num) (by norm_num)
      (by positivity) (Nat.cast_le.mpr hl)
  have sml : pairwiseRate a b e (n:ℝ) q ≤ 3*sharpQuota a b e (n:ℝ) q := by
    unfold pairwiseRate sharpQuota quotaProfile
    have h₁ := le_max_left (n:ℝ)
      (max ((n:ℝ)^(a+e)*(q:ℝ)^(2-2*a)) ((n:ℝ)^(2-2*b+e)*(q:ℝ)^b))
    have h₂ := le_max_of_le_right (a := (n:ℝ)^(a+e)*(q:ℝ)^(2-2*a)) (b := (n:ℝ))
      (le_max_left _ ((n:ℝ)^(2-2*b+e)*(q:ℝ)^b))
    have h₃ := le_max_of_le_right (a := (n:ℝ)^(2-2*b+e)*(q:ℝ)^b) (b := (n:ℝ))
      (le_max_right ((n:ℝ)^(a+e)*(q:ℝ)^(2-2*a)) _)
    linarith only [h₁,h₂,h₃]
  have half₁ : ((forwardRun G D).card:ℝ) ≤ (3*K)*sharpQuota a b e (n:ℝ) q := by
    calc
      _ ≤ K*pairwiseRate a b e (n:ℝ) q := sharp
      _ ≤ K*(3*sharpQuota a b e (n:ℝ) q) := mul_le_mul_of_nonneg_left sml hK
      _ = _ := by ring
  have half₂ := (forwardRun_initial_quota dag D).trans
    (mul_le_mul_of_nonneg_left mono (by norm_num : 0 ≤ (16:ℝ)))
  apply Nat.cast_le (α := ℝ) |>.mp
  exact (le_min half₁ half₂ : ((forwardRun G D).card:ℝ) ≤ B).trans (Nat.le_ceil B)

end OnlineReachabilityPreservers
