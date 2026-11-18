import OnlineReachabilityPreservers.BootstrapArithmetic
import OnlineReachabilityPreservers.ExponentLimits

/-! The three branching terms and the lower-order logarithm in the offline update. -/

namespace OnlineReachabilityPreservers

private theorem log_factor {n : ℝ} (hn : 1 ≤ n) :
    (2+Real.log n)^(2/11 : ℝ) ≤ 252*n^(1/250 : ℝ) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hlog := Real.log_nonneg hn
  have hnonneg : 0 ≤ 2+Real.log n := by linarith
  have hx : (1 : ℝ) ≤ 2+Real.log n := by linarith
  have hpow : (2+Real.log n)^(2/11 : ℝ) ≤ 2+Real.log n := by
    conv_rhs => rw [← Real.rpow_one (2+Real.log n)]
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have ex : Real.exp (Real.log n * (1/250 : ℝ)) = n^(1/250 : ℝ) :=
    (Real.rpow_def_of_pos hn0 _).symm
  have h := Real.add_one_le_exp (Real.log n * (1/250 : ℝ))
  rw [ex] at h
  have one_n : 1 ≤ n^(1/250 : ℝ) := by
    conv_lhs => rw [← Real.one_rpow (1/250 : ℝ)]
    exact Real.rpow_le_rpow zero_le_one hn (by norm_num)
  exact hpow.trans (by linarith only [h, one_n])

/-- The logarithmic term from the second term of the Lemma 42 comparison
is dominated by the two offline rate terms over the iteration's range. -/
theorem lemma42_log_term_le {n p β : ℝ} (hn : 1 ≤ n) (hp : 0 < p)
    (lo : 7/11 ≤ β) (hi : β ≤ 177/250) :
    (2+Real.log n)^(2/11 : ℝ) * n^(7/11 : ℝ) * p^(7/11 : ℝ) ≤
      252*(n^(3/4 : ℝ)*p^(1/2 : ℝ) + n^(2-2*β)*p^β) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have sub : n^(1/250 : ℝ)*n^(7/11 : ℝ)*p^(7/11 : ℝ) ≤
      n^(3/4 : ℝ)*p^(1/2 : ℝ) + n^(2-2*β)*p^β := by
    rw [← Real.rpow_add hn0]
    let a : ℝ := 1/250+7/11
    change n^a*p^(7/11 : ℝ) ≤ _
    by_cases sparse : p ≤ n^(4/5 : ℝ)
    · apply le_trans _ (le_add_of_nonneg_right (by positivity))
      have h := Real.rpow_le_rpow hp.le sparse (show (0 : ℝ) ≤ 3/22 by norm_num)
      rw [← Real.rpow_mul hn0.le] at h
      have exp : a+(4/5)*(3/22) ≤ 3/4 := by dsimp [a]; norm_num
      calc
        _ = n^a*p^(3/22 : ℝ)*p^(1/2 : ℝ) := by
          rw [mul_assoc, ← Real.rpow_add hp, show (3/22 : ℝ)+1/2 = 7/11 by norm_num]
        _ ≤ n^a*n^((4/5)*(3/22) : ℝ)*p^(1/2 : ℝ) := by gcongr
        _ ≤ _ := by
          rw [← Real.rpow_add hn0]
          exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hn exp) (by positivity)
    · apply le_trans _ (le_add_of_nonneg_left (by positivity))
      have h := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hn0 (4/5))
        (le_of_lt (lt_of_not_ge sparse)) (show 7/11-β ≤ 0 by linarith)
      rw [← Real.rpow_mul hn0.le] at h
      have exp : a+(4/5)*(7/11-β) ≤ 2-2*β := by dsimp [a]; linarith
      calc
        _ = n^a*p^(7/11-β)*p^β := by
          rw [mul_assoc, ← Real.rpow_add hp, sub_add_cancel]
        _ ≤ n^a*n^((4/5)*(7/11-β))*p^β := by gcongr
        _ ≤ _ := by
          rw [← Real.rpow_add hn0]
          exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hn exp) (by positivity)
  calc
    _ ≤ (252*n^(1/250 : ℝ))*n^(7/11 : ℝ)*p^(7/11 : ℝ) := by gcongr; exact log_factor hn
    _ = 252*(n^(1/250 : ℝ)*n^(7/11 : ℝ)*p^(7/11 : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left sub (by norm_num)

private theorem lemma42_first_term {M n p C K : ℝ}
    (hM : 0 < M) (hn : 0 < n) (hp : 0 < p) (hC : 0 < C) (hK : 0 ≤ K)
    (comp : let ℓ := M/p; let d := M/n
      ℓ^2*d^2 ≤ K*ℓ^2*d*(C*p/(ℓ*d^2))) :
    M ≤ (K*C)^(1/4 : ℝ)*n^(3/4 : ℝ)*p^(1/2 : ℝ) := by
  have h := incidence_monomial_bound (u := 2) (v := 1) (w := 1) hM hn hp hC hK
    (by norm_num) (by simpa only [Real.rpow_two, Real.rpow_one] using comp)
  norm_num [Real.rpow_one] at h
  exact h

private theorem lemma42_second_term {M n p C K : ℝ}
    (hM : 0 < M) (hn : 1 ≤ n) (hp : 0 < p) (hC : 0 < C) (hK : 0 ≤ K)
    (comp : let ℓ := M/p; let d := M/n
      ℓ^2*d^2 ≤ K*(2+Real.log n)*ℓ^(3/2 : ℝ)*d^(3/2 : ℝ)*(C*p/(ℓ*d^2))^(3/2 : ℝ)) :
    M ≤ (K*C^(3/2 : ℝ))^(2/11 : ℝ)*
      ((2+Real.log n)^(2/11 : ℝ)*n^(7/11 : ℝ)*p^(7/11 : ℝ)) := by
  have hlog : 0 ≤ 2+Real.log n := by linarith [Real.log_nonneg hn]
  have h := incidence_monomial_bound (u := 3/2) (v := 3/2) (w := 3/2)
    hM (zero_lt_one.trans_le hn) hp hC (mul_nonneg hK hlog) (by norm_num) comp
  have ht : 1/(4-(3/2 : ℝ)-3/2+3*(3/2)) = 2/11 := by norm_num
  have he : (2-(3/2 : ℝ)+2*(3/2))/(4-3/2-3/2+3*(3/2)) = 7/11 := by norm_num
  rw [ht, he, show K*(2+Real.log n)*C^(3/2 : ℝ) = (K*C^(3/2 : ℝ))*(2+Real.log n) by ring,
    Real.mul_rpow (by positivity) hlog] at h
  exact h.trans_eq (by ring)

/-- The three terms of the offline comparison imply the two updated rate terms. -/
theorem lemma42_comparison {C K b : ℝ} (hC : 0 < C) (hK : 0 < K)
    (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 71/100) :
    ∃ A > 0, ∀ {M n p : ℝ}, 0 < M → 1 ≤ n → 0 < p →
      (let ℓ := M/p; let d := M/n; let t := C*p/(ℓ*d^2)
       ℓ^2*d^2 ≤ K*(ℓ^2*d*t +
         (2+Real.log n)*ℓ^(3/2 : ℝ)*d^(3/2 : ℝ)*t^(3/2 : ℝ) +
         ℓ^(1/b)*d^2*t^(1/b))) →
      let β := offlineExponentStep b
      M ≤ A*(n^(3/4 : ℝ)*p^(1/2 : ℝ) + n^(2-2*β)*p^β) := by
  let β := offlineExponentStep b
  let k := 3*K
  let a₁ := (k*C)^(1/4 : ℝ)
  let a₂ := 252*(k*C^(3/2 : ℝ))^(2/11 : ℝ)
  let a₃ := (k*C^(1/b))^(b/(2*b+2))
  have hk : 0 < k := by dsimp [k]; positivity
  have ha₁ : 0 ≤ a₁ := by dsimp [a₁]; positivity
  have ha₂ : 0 ≤ a₂ := by dsimp [a₂]; positivity
  have ha₃ : 0 ≤ a₃ := by dsimp [a₃]; positivity
  have hb : 0 < b := by linarith
  have hden : 0 < 2*b+2 := by positivity
  have hlow : 7/11 ≤ β := by
    change (7/11 : ℝ) ≤ (2*b+1)/(2*b+2)
    exact (le_div_iff₀ hden).mpr (by linarith)
  have hhigh : β ≤ 177/250 := by
    change (2*b+1)/(2*b+2) ≤ (177/250 : ℝ)
    exact (div_le_iff₀ hden).mpr (by linarith)
  refine ⟨1+a₁+a₂+a₃, by linarith, ?_⟩
  intro M n p hM hn hp comp
  let ℓ := M/p
  let d := M/n
  let t := C*p/(ℓ*d^2)
  let x := ℓ^2*d*t
  let y := (2+Real.log n)*ℓ^(3/2 : ℝ)*d^(3/2 : ℝ)*t^(3/2 : ℝ)
  let z := ℓ^(1/b)*d^2*t^(1/b)
  let F := n^(3/4 : ℝ)*p^(1/2 : ℝ)
  let G := n^(2-2*β)*p^β
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have bound : ℓ^2*d^2 ≤ k*max x (max y z) := by
    have sum : x+y+z ≤ 3*max x (max y z) := by
      linarith only [le_max_left x (max y z),
        (le_max_left y z).trans (le_max_right x (max y z)),
        (le_max_right y z).trans (le_max_right x (max y z))]
    exact comp.trans ((mul_le_mul_of_nonneg_left sum hK.le).trans_eq (by dsimp [k]; ring))
  change M ≤ (1+a₁+a₂+a₃)*(F+G)
  by_cases hx : max y z ≤ x
  · rw [max_eq_left hx] at bound
    have h := lemma42_first_term hM (zero_lt_one.trans_le hn) hp hC hk.le
      (by simpa only [x, mul_assoc] using bound)
    have h' : M ≤ a₁*F := h.trans_eq (by dsimp [a₁, F]; ring)
    exact h'.trans ((mul_le_mul_of_nonneg_left (by linarith : F ≤ F+G) ha₁).trans
      (mul_le_mul_of_nonneg_right (by linarith) (add_nonneg hF hG)))
  rw [max_eq_right (le_of_not_ge hx)] at bound
  by_cases hy : z ≤ y
  · rw [max_eq_left hy] at bound
    have h := lemma42_second_term hM hn hp hC hk.le
      (by simpa only [y, mul_assoc] using bound)
    have h' := mul_le_mul_of_nonneg_left (lemma42_log_term_le hn hp hlow hhigh)
      (show 0 ≤ (k*C^(3/2 : ℝ))^(2/11 : ℝ) by positivity)
    have hm : M ≤ a₂*(F+G) := h.trans (h'.trans_eq (by dsimp [a₂, F, G]; ring))
    exact hm.trans
      (mul_le_mul_of_nonneg_right (by linarith) (add_nonneg hF hG))
  rw [max_eq_right (le_of_not_ge hy)] at bound
  have h := lemma42_third_term hM (zero_lt_one.trans_le hn) hp hC hk.le hb
    (by simpa only [z, mul_assoc] using bound)
  have exp : 2-2*β = 1/(b+1) := lemma42_vertex_exponent hb
  have h' : M ≤ a₃*G := h.trans_eq (by dsimp only [a₃, G]; rw [exp]; unfold β offlineExponentStep; ring)
  exact h'.trans ((mul_le_mul_of_nonneg_left (by linarith : G ≤ F+G) ha₃).trans
    (mul_le_mul_of_nonneg_right (by linarith) (add_nonneg hF hG)))

end OnlineReachabilityPreservers
