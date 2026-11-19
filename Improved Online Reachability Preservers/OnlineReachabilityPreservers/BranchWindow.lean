import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The finite branching window and incidence scaling shared by both proofs. -/

namespace OnlineReachabilityPreservers

/-- Choose a positive integer window that retains the desired lower multiplier. -/
theorem rounded_branch_window {n p M C : ℕ} (hn : 0 < n) (hp : 0 < p) (hM : 0 < M)
    (hC : 2048 ≤ C) (cube : M^3 ≤ 2048*(n*p)^2) :
    let h : ℕ := (C*n^2*p^2)/M^3+1
    let ℓ : ℝ := (M:ℝ)/p
    let d : ℝ := (M:ℝ)/n
    let t : ℝ := (C:ℝ)*p/(ℓ*d^2)
    (h:ℝ)+1 ≤ 3*t ∧ C*n^2*p^2 ≤ (h+1)*M^3 := by
  dsimp only
  let ℓ : ℝ := (M:ℝ)/p
  let d : ℝ := (M:ℝ)/n
  let t := (C:ℝ)*p/(ℓ*d^2)
  let R := C*n^2*p^2
  let h := R/M^3+1
  have npos : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have ppos : (0:ℝ) < p := Nat.cast_pos.mpr hp
  have mpos : (0:ℝ) < M := Nat.cast_pos.mpr hM
  have model : t = (R:ℝ)/(M:ℝ)^3 := by
    dsimp only [t, ℓ, d, R]
    push_cast
    field_simp [npos.ne', ppos.ne', mpos.ne']
  have lower : 1 ≤ t := by
    rw [model, le_div_iff₀ (pow_pos mpos 3), one_mul]
    have hle : M^3 ≤ R := cube.trans
      ((Nat.mul_le_mul_right _ hC).trans_eq (by dsimp only [R]; ring))
    exact_mod_cast hle
  have floor : ((R/M^3:ℕ):ℝ) ≤ t := by
    rw [model, le_div_iff₀ (pow_pos mpos 3)]
    exact_mod_cast Nat.div_mul_le_self R (M^3)
  change (h:ℝ)+1 ≤ 3*t ∧ R ≤ (h+1)*M^3
  constructor
  · dsimp only [h]
    push_cast
    linarith only [lower, floor]
  · calc
      _ ≤ M^3*h := (Nat.lt_mul_div_succ R (Nat.pow_pos hM)).le
      _ = h*M^3 := Nat.mul_comm _ _
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_succ h)

/-- Normalize the retained-window count to the uniform mean. -/
theorem branch_window_mean_lower {n p M C h Q : ℕ} (hn : 0 < n) (hp : 0 < p)
    (height : C*n^2*p^2 ≤ (h+1)*M^3)
    (count : (h+1)*M^7 ≤ (40*2048^2)*n^4*p^3*Q) :
    let ℓ : ℝ := (M:ℝ)/p
    let d : ℝ := (M:ℝ)/n
    (C:ℝ)*(ℓ^2*d^2) ≤ (40*2048^2)*((Q:ℝ)/p) := by
  dsimp only
  have npos : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have ppos : (0:ℝ) < p := Nat.cast_pos.mpr hp
  have hN : C*M^4 ≤ (40*2048^2)*n^2*p*Q := by
    apply Nat.le_of_mul_le_mul_right (c := n^2*p^2) _ (by positivity)
    calc
      _ = (C*n^2*p^2)*M^4 := by ring
      _ ≤ ((h+1)*M^3)*M^4 := Nat.mul_le_mul_right _ height
      _ = (h+1)*M^7 := by ring
      _ ≤ _ := count.trans_eq (by ring)
  have hR : (C:ℝ)*(M:ℝ)^4 ≤ (40*2048^2)*(n:ℝ)^2*p*Q := by exact_mod_cast hN
  apply le_of_mul_le_mul_right (a := (n:ℝ)^2*(p:ℝ)^2) _
    (mul_pos (sq_pos_of_pos npos) (sq_pos_of_pos ppos))
  convert hR using 1
  · field_simp [npos.ne', ppos.ne']
  · field_simp [ppos.ne']

private theorem mass_quartic_le {M n p K : ℝ} {u v : ℕ}
    (hM : 0 < M) (hn : 0 < n) (hp : 0 < p) (hK : 0 ≤ K)
    (comp : M^4 ≤ K*n^u*p^v) :
    M ≤ K^(1/4:ℝ)*n^((u:ℝ)/4)*p^((v:ℝ)/4) := by
  have h := Real.rpow_le_rpow (pow_nonneg hM.le 4) comp (by norm_num : (0:ℝ) ≤ 1/4)
  rw [← Real.rpow_natCast_mul hM.le 4, Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow hK (pow_nonneg hn.le _),
    ← Real.rpow_natCast_mul hn.le u, ← Real.rpow_natCast_mul hp.le v] at h
  norm_num [mul_one_div] at h
  exact h

/-- The case in which the model window is too long for the average path. -/
theorem mass_large_length_window {M n p C : ℝ} (hM : 0 < M) (hn : 0 < n)
    (hp : 0 < p) (hC : 0 < C)
    (outside : let ℓ := M/p; let d := M/n; ℓ ≤ 3*(C*p/(ℓ*d^2))) :
    M ≤ (3*C)^(1/4 : ℝ)*n^(1/2 : ℝ)*p^(3/4 : ℝ) := by
  let ℓ := M/p
  let d := M/n
  have h := mul_le_mul_of_nonneg_right outside (by positivity : 0 ≤ ℓ*d^2)
  change ℓ*(ℓ*d^2) ≤ (3*(C*p/(ℓ*d^2)))*(ℓ*d^2) at h
  have pos : 0 < ℓ*d^2 := by dsimp only [ℓ,d]; positivity
  have eq : (3*(C*p/(ℓ*d^2)))*(ℓ*d^2)=3*C*p := by
    rw [mul_assoc, div_mul_cancel₀ _ pos.ne', mul_assoc]
  rw [eq, show ℓ*(ℓ*d^2)=ℓ^2*d^2 by ring] at h
  have m : M^4 ≤ (3*C)*n^2*p^3 := by
    have h' := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ n^2*p^2)
    convert h' using 1
    · dsimp only [ℓ,d]
      field_simp
    · ring
  have bound := mass_quartic_le hM hn hp (by positivity) m
  norm_num at bound
  exact bound

/-- The case in which the model window exceeds the average degree. -/
theorem mass_large_degree_window {M n p C : ℝ} (hM : 0 < M) (hn : 0 < n)
    (hp : 0 < p) (hC : 0 < C)
    (outside : let ℓ := M/p; let d := M/n; d ≤ 3*(C*p/(ℓ*d^2))) :
    M ≤ (3*C)^(1/4 : ℝ)*n^(3/4 : ℝ)*p^(1/2 : ℝ) := by
  let ℓ := M/p
  let d := M/n
  have h := mul_le_mul_of_nonneg_right outside (by positivity : 0 ≤ ℓ*d^2)
  change d*(ℓ*d^2) ≤ (3*(C*p/(ℓ*d^2)))*(ℓ*d^2) at h
  have pos : 0 < ℓ*d^2 := by dsimp only [ℓ,d]; positivity
  have eq : (3*(C*p/(ℓ*d^2)))*(ℓ*d^2)=3*C*p := by
    rw [mul_assoc, div_mul_cancel₀ _ pos.ne', mul_assoc]
  rw [eq, show d*(ℓ*d^2)=ℓ*d^3 by ring] at h
  have m : M^4 ≤ (3*C)*n^3*p^2 := by
    have h' := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ n^3*p)
    convert h' using 1
    · dsimp only [ℓ,d]
      field_simp
    · ring
  have bound := mass_quartic_le hM hn hp (by positivity) m
  norm_num at bound
  exact bound

/-- Compare the square-root rate and a leading incidence power. -/
theorem square_root_rate_le {n k a : ℝ} (hn : 0 < n) (hk : 0 ≤ k)
    (ha : a ≤ 3/4) :
    n^(3/4 : ℝ)*k^(1/2 : ℝ) ≤ max n (n^a*k^(2-2*a)) := by
  by_cases cut : k ≤ Real.sqrt n
  · have h := Real.rpow_le_rpow hk cut (by norm_num : (0 : ℝ) ≤ 1/2)
    apply le_max_of_le_left
    calc
      _ ≤ n^(3/4 : ℝ)*(Real.sqrt n)^(1/2 : ℝ) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = n := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le, ← Real.rpow_add hn]
        norm_num
  · have hsq : n ≤ k^2 := by
      rw [← Real.sq_sqrt hn.le]
      exact (sq_le_sq₀ (Real.sqrt_nonneg _) hk).mpr (le_of_lt (lt_of_not_ge cut))
    let e : ℝ := 3/4-a
    have he₀ : 0 ≤ e := sub_nonneg.mpr ha
    have he := Real.rpow_le_rpow hn.le hsq he₀
    rw [← Real.rpow_natCast_mul hk 2] at he
    push_cast at he
    apply le_max_of_le_right
    calc
      _ = (n^a*k^(1/2 : ℝ)) * n^e := by
        rw [mul_comm (n^a*k^(1/2 : ℝ)) (n^e), ← mul_assoc, ← Real.rpow_add hn]
        have : e+a = 3/4 := by dsimp [e]; ring
        rw [this]
      _ ≤ (n^a*k^(1/2 : ℝ))*k^(2*e) := mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by
        have hkp : 0 < k := (Real.sqrt_pos.2 hn).trans (lt_of_not_ge cut)
        have he' : (1/2 : ℝ)+2*e = 2-2*a := by dsimp [e]; ring
        rw [mul_assoc, ← Real.rpow_add hkp, he']


/-- Convert a witness count, its second moment and the close-pair count into
the common lower bound on the sampled branching tuples. -/
theorem scaled_branching_count {n p M h a R S Q : ℕ}
    (hn : 0 < n) (hp : 0 < p) (hM : 0 < M)
    (chain : M^4 ≤ 2048 * n^2 * p * R)
    (moment : R^2 ≤ p^2 * S)
    (close : (h+1)*S ≤ a*(R+2*Q))
    (window : a*p ≤ 10*M)
    (large : 40960*n^2*p^2 ≤ (h+1)*M^3) :
    (h+1)*M^7 ≤ (40*2048^2)*n^4*p^3*Q := by
  have enough : 2*a*p^2 ≤ (h+1)*R := by
    apply Nat.le_of_mul_le_mul_right (c := 2048*n^2*p) _ (by positivity)
    have h1 := Nat.mul_le_mul_right (4096*n^2*p^2) window
    have h2 := Nat.mul_le_mul_right M large
    have h3 := Nat.mul_le_mul_left (h + 1) chain
    change (40960*n^2*p^2) * M ≤ ((h + 1)*M^3) * M at h2
    nlinarith only [h1, h2, h3]
  have linear : 2*a*R ≤ (h + 1)*S := by
    apply Nat.le_of_mul_le_mul_right (c := p^2) _ (Nat.pow_pos hp)
    have h1 := Nat.mul_le_mul_right R enough
    have h2 := Nat.mul_le_mul_left (h + 1) moment
    nlinarith only [h1, h2]
  have absorbed : (h+1)*S ≤ 4*a*Q := by nlinarith only [close, linear]
  have square : M^8 ≤ 2048^2*n^4*p^4*S := calc
    M^8 = (M^4)^2 := by ring
    _ ≤ (2048*n^2*p*R)^2 := Nat.pow_le_pow_left chain 2
    _ = (2048^2*n^4*p^2)*R^2 := by ring
    _ ≤ (2048^2*n^4*p^2)*(p^2*S) := Nat.mul_le_mul_left _ moment
    _ = _ := by ring
  apply Nat.le_of_mul_le_mul_right (c := M*p) _ (Nat.mul_pos hM hp)
  calc
    _ = ((h+1)*p)*M^8 := by ring
    _ ≤ ((h+1)*p)*(2048^2*n^4*p^4*S) := Nat.mul_le_mul_left _ square
    _ = (2048^2*n^4*p^5)*((h+1)*S) := by ring
    _ ≤ (2048^2*n^4*p^5)*(4*a*Q) := Nat.mul_le_mul_left _ absorbed
    _ = (4*2048^2*n^4*p^4*Q)*(a*p) := by ring
    _ ≤ (4*2048^2*n^4*p^4*Q)*(10*M) := Nat.mul_le_mul_left _ window
    _ = _ := by ring


end OnlineReachabilityPreservers
