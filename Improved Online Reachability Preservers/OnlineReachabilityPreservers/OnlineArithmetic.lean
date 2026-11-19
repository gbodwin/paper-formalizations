import OnlineReachabilityPreservers.BootstrapArithmetic
import OnlineReachabilityPreservers.ExponentLimits

/-! The four-term comparison in Appendix A. -/

namespace OnlineReachabilityPreservers

/-- The two online powers together with the degenerate linear regimes. -/
noncomputable def onlineRate (a b n p : ℝ) : ℝ :=
  max n (max (n^a*p^(2-2*a)) (max (n^(2-2*b)*p^b) p))

private theorem lemma37_second_term {M n p C K a b : ℝ}
    (hM : 0 < M) (hn : 0 < n) (hp : 0 < p) (hC : 0 < C) (hK : 0 ≤ K)
    (ha₀ : 29/40 ≤ a) (ha₁ : a < 3/4) (hb : 0 < b)
    (comp : let ℓ := M/p; let d := M/n
      ℓ^2*d^2 ≤ K*ℓ^(3/2:ℝ)*d^(3/2+(3-4*a)/(2-2*a))*
        (C*p/(ℓ*d^2))^((2*b+1)/(2*b))) :
    let s := 1/b
    let γ := (3-4*a)/(2-2*a)
    let D := 4-γ+(3/2)*s
    M ≤ (K*C^(1+s/2))^(1/D)*n^((5/2+s-γ)/D)*p^((5/2+s)/D) := by
  dsimp only
  let s := 1/b
  let γ := (3-4*a)/(2-2*a)
  let D := 4-γ+(3/2)*s
  have hg : γ ≤ 2/11 := (div_le_iff₀ (by linarith : 0 < 2-2*a)).mpr (by linarith)
  have hs : 0 < s := one_div_pos.mpr hb
  have hD : 0 < D := by dsimp only [D]; linarith
  let w := 1+s/2
  have ew : (2*b+1)/(2*b) = w := by dsimp only [w,s]; field_simp
  have eD : 4-(3/2:ℝ)-(3/2+γ)+3*w = D := by dsimp only [w,D]; ring
  have en : 2-(3/2+γ)+2*w = 5/2+s-γ := by dsimp only [w]; ring
  have ep : 2-(3/2:ℝ)+2*w = 5/2+s := by dsimp only [w]; ring
  have premise : let ℓ := M/p; let d := M/n
      ℓ^2*d^2 ≤ K*ℓ^(3/2:ℝ)*d^(3/2+γ)*(C*p/(ℓ*d^2))^w := by rw [← ew]; exact comp
  have calcBound := incidence_monomial_bound hM hn hp hC hK (eD.symm ▸ hD) premise
  rw [eD, en, ep] at calcBound
  exact calcBound

private theorem lemma37_fourth_term {M n p C K : ℝ}
    (hM : 0 < M) (hn : 0 < n) (hp : 0 < p) (hC : 0 < C) (hK : 0 ≤ K)
    (comp : let ℓ := M/p; let d := M/n
      ℓ^2*d^2 ≤ K*ℓ^(3/2:ℝ)*d^2*(C*p/(ℓ*d^2))^(5/4:ℝ)) :
    M ≤ (K*C^(5/4:ℝ))^(4/17:ℝ)*n^(10/17:ℝ)*p^(12/17:ℝ) := by
  have actual := incidence_monomial_bound (u := 3/2) (v := 2) (w := 5/4) hM hn hp hC hK
    (by norm_num) (by simpa only [Real.rpow_two] using comp)
  have e : 1/(4-(3/2:ℝ)-2+3*(5/4)) = 4/17 := by norm_num
  have f : (2-(2:ℝ)+2*(5/4))/(4-3/2-2+3*(5/4)) = 10/17 := by norm_num
  have g : (2-(3/2:ℝ)+2*(5/4))/(4-3/2-2+3*(5/4)) = 12/17 := by norm_num
  simpa only [e,f,g] using actual

/-- The mixed term decreases with its pair exponent for p≤n².
For p≥n² the linear pair term bounds it when the exponent is at most one. -/
theorem mixed_term_le {b c n p : ℝ} (hbc : b ≤ c) (hc : c ≤ 1)
    (hn : 0 < n) (hp : 0 < p) :
    n^(2-2*c)*p^c ≤ max (n^(2-2*b)*p^b) p := by
  by_cases small : p ≤ n^2
  · apply le_max_of_le_left
    let e := c-b
    have h := Real.rpow_le_rpow hp.le small (sub_nonneg.mpr hbc)
    rw [← Real.rpow_natCast_mul hn.le 2] at h
    push_cast at h
    calc
      _ = (n^(2-2*c)*p^b)*p^e := by
        rw [mul_assoc, ← Real.rpow_add hp]
        congr 2
        dsimp [e]
        ring
      _ ≤ (n^(2-2*c)*p^b)*n^(2*e) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by
        rw [show (n^(2-2*c)*p^b)*n^(2*e) = (n^(2-2*c)*n^(2*e))*p^b by ring,
          ← Real.rpow_add hn]
        congr 2
        dsimp [e]
        ring
  · apply le_max_of_le_right
    have bound := Real.rpow_le_rpow (sq_nonneg n) (le_of_not_ge small) (sub_nonneg.mpr hc)
    rw [← Real.rpow_natCast_mul hn.le 2] at bound
    push_cast at bound
    have h : n^(2-2*c) ≤ p^(1-c) := by convert bound using 2; ring
    calc
      _ ≤ p^(1-c)*p^c := mul_le_mul_of_nonneg_right h (by positivity)
      _ = _ := by rw [← Real.rpow_add hp, sub_add_cancel, Real.rpow_one]

private theorem lemma37_second_powers {n p a b β : ℝ} (hn : 1 ≤ n) (hp : 0 < p)
    (ha₀ : 29/40 ≤ a) (ha₁ : a < 3/4) (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 701/1000)
    (hβ₀ : 2/3 ≤ β) (hβ₁ : β ≤ 701/1000) :
    let s := 1/b
    let γ := (3-4*a)/(2-2*a)
    let D := 4-γ+(3/2)*s
    let A := (2+b)/(3+b)
    n^((5/2+s-γ)/D)*p^((5/2+s)/D) ≤
      max (n^A*p^(2-2*A)) (n^(2-2*β)*p^β) := by
  dsimp only
  let s := 1/b
  let γ := (3-4*a)/(2-2*a)
  let D := 4-γ+(3/2)*s
  let A := (2+b)/(3+b)
  let N := (5/2+s-γ)/D
  let P := (5/2+s)/D
  have bpos : 0 < b := by linarith
  have smin : 1 ≤ s := (le_div_iff₀ bpos).mpr (by linarith)
  have smax : s ≤ 3/2 := (div_le_iff₀ bpos).mpr (by linarith)
  have denA : 0 < 2-2*a := by linarith
  have hγ : 0 ≤ γ := div_nonneg (by linarith) denA.le
  have gmax : γ ≤ 2/11 := (div_le_iff₀ denA).mpr (by linarith)
  have Dpos : 0 < D := by dsimp only [D]; linarith
  have Alo : 8/11 ≤ A := (le_div_iff₀ (by linarith : 0 < 3+b)).mpr (by linarith)
  have Ahi : A ≤ 73/100 := (div_le_iff₀ (by linarith : 0 < 3+b)).mpr (by linarith)
  have Plo : 63/100 ≤ P := (le_div_iff₀ Dpos).mpr (by dsimp only [D]; linarith)
  have Phi : P ≤ 2/3 := (div_le_iff₀ Dpos).mpr (by dsimp only [D]; linarith)
  have S : N+(4/5)*P ≤ 1157/1000 := by
    dsimp only [N,P]
    rw [← mul_div_assoc, ← add_div]
    apply (div_le_iff₀ Dpos).mpr
    dsimp only [D]
    linarith
  have hnp := zero_lt_one.trans_le hn
  change n^N*p^P ≤ _
  by_cases small : p ≤ n^(4/5:ℝ)
  · apply le_max_of_le_left
    let u := P-(2-2*A)
    have h := Real.rpow_le_rpow hp.le small (show 0 ≤ u by dsimp [u]; linarith)
    rw [← Real.rpow_mul hnp.le] at h
    calc
      _ = n^N*p^u*p^(2-2*A) := by rw [mul_assoc, ← Real.rpow_add hp]; congr 2; dsimp [u]; ring
      _ ≤ n^N*n^((4/5)*u)*p^(2-2*A) := by gcongr
      _ ≤ _ := by
        rw [← Real.rpow_add hnp]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hn (by dsimp only [u]; linarith)) (by positivity)
  · apply le_max_of_le_right
    let u := P-β
    have h := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hnp (4/5))
      (le_of_not_ge small) (show u ≤ 0 by dsimp [u]; linarith)
    rw [← Real.rpow_mul hnp.le] at h
    calc
      _ = n^N*p^u*p^β := by rw [mul_assoc, ← Real.rpow_add hp]; congr 2; dsimp [u]; ring
      _ ≤ n^N*n^((4/5)*u)*p^β := by gcongr
      _ ≤ _ := by
        rw [← Real.rpow_add hnp]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hn (by dsimp only [u]; linarith)) (by positivity)


/-- Compare the four nonlinear terms of Lemma 37 with the updated incidence rate. -/
theorem lemma37_comparison {C K a b : ℝ} (hC : 0 < C) (hK : 0 < K)
    (ha₀ : 29/40 ≤ a) (ha₁ : a < 3/4) (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 701/1000)
    (hβ₀ : 2/3 ≤ onlineExponentStep b) (hβ₁ : onlineExponentStep b ≤ 701/1000) :
    ∃ A > 0, ∀ {M n p : ℝ}, 0 < M → 1 ≤ n → 0 < p →
      (let ℓ := M/p; let d := M/n; let t := C*p/(ℓ*d^2)
       ℓ^2*d^2 ≤ K*(ℓ^2*d*t^(1/b) +
         ℓ^(3/2:ℝ)*d^(3/2+(3-4*a)/(2-2*a))*t^((2*b+1)/(2*b)) +
         ℓ^(1/b)*d^2*t^((4*b-2*b^2-1)/b^2) + ℓ^(3/2:ℝ)*d^2*t^(5/4:ℝ))) →
      M ≤ A*onlineRate ((2+b)/(3+b)) (onlineExponentStep b) n p := by
  let k := 4*K
  have hk : 0 < k := by dsimp only [k]; positivity
  let s := 1/b
  let γ := (3-4*a)/(2-2*a)
  let den₂ := 4-γ+(3/2)*s
  let den₃ := 11*b-4*b^2-3
  let w := (4*b-2*b^2-1)/b^2
  let α := (2+b)/(3+b)
  let β := onlineExponentStep b
  let c₁ := (k*C^(1/b))^(b/(3+b))
  let c₂ := (k*C^(1+s/2))^(1/den₂)
  let c₃ := (k*C^w)^(b^2/den₃)
  let c₄ := (k*C^(5/4:ℝ))^(4/17:ℝ)
  let A := 1+c₁+c₂+c₃+c₄
  have h₁ : 0 ≤ c₁ := by dsimp only [c₁]; positivity
  have h₂ : 0 ≤ c₂ := by dsimp only [c₂]; positivity
  have h₃ : 0 ≤ c₃ := by dsimp only [c₃]; positivity
  have h₄ : 0 ≤ c₄ := by dsimp only [c₄]; positivity
  have hA : 0 < A := by dsimp only [A]; linarith only [h₁,h₂,h₃,h₄]
  have hb : 0 < b := by linarith
  have hb' : b ≤ 3/4 := by linarith
  have d₃pos : 0 < den₃ := by
    have hsq := (sq_le_sq₀ hb.le (by norm_num : (0:ℝ) ≤ 3/4)).mpr hb'
    dsimp only [den₃]
    nlinarith only [hsq,hb₀]
  have hfirst : 2/(3+b)=2-2*α := by
    have hd : (3+b:ℝ) ≠ 0 := by positivity
    dsimp only [α]
    field_simp [hd]
    ring
  have hthird : (8*b-4*b^2-2)/den₃ = 2-2*β := by
    change (8*b-4*b^2-2)/den₃ = 2-2*((7*b-2*b^2-2)/den₃)
    field_simp [d₃pos.ne']
    dsimp only [den₃]
    ring
  refine ⟨A,hA,?_⟩
  intro M n p hM hn hp compare
  let ℓ := M/p
  let d := M/n
  let t := C*p/(ℓ*d^2)
  let X := ℓ^2*d*t^(1/b)
  let Y := ℓ^(3/2:ℝ)*d^(3/2+γ)*t^((2*b+1)/(2*b))
  let Z := ℓ^(1/b)*d^2*t^w
  let W := ℓ^(3/2:ℝ)*d^2*t^(5/4:ℝ)
  let F := onlineRate α β n p
  have F0 : 0 ≤ F := zero_le_one.trans (hn.trans (le_max_left _ _))
  have hnp := zero_lt_one.trans_le hn
  have hmax : ℓ^2*d^2 ≤ k*max X (max Y (max Z W)) := calc
    _ ≤ K*(X+Y+Z+W) := compare
    _ ≤ K*(4*max X (max Y (max Z W))) := by
      apply mul_le_mul_of_nonneg_left _ hK.le
      linarith only [le_max_left X (max Y (max Z W)),
        (le_max_left Y (max Z W)).trans (le_max_right X (max Y (max Z W))),
        (le_max_left Z W).trans ((le_max_right Y (max Z W)).trans (le_max_right X (max Y (max Z W)))),
        (le_max_right Z W).trans ((le_max_right Y (max Z W)).trans (le_max_right X (max Y (max Z W))))]
    _ = _ := by dsimp only [k]; ring
  have leading : n^α*p^(2-2*α) ≤ F := (le_max_left _ _).trans (le_max_right _ _)
  have mixed : n^(2-2*β)*p^β ≤ F :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have pairs : p ≤ F := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have finish {c z : ℝ} (hm : M ≤ c*z) (hz : z ≤ F) (hc : 0 ≤ c) (upper : c ≤ A) :
      M ≤ A*F := hm.trans ((mul_le_mul_of_nonneg_left hz hc).trans (mul_le_mul_of_nonneg_right upper F0))
  change M ≤ A*F
  by_cases x : max Y (max Z W) ≤ X
  · rw [max_eq_left x] at hmax
    have mass := lemma37_first_term hM hnp hp hC hk.le hb (by simpa only [X,mul_assoc] using hmax)
    rw [hfirst] at mass
    exact finish (mass.trans_eq (by dsimp only [c₁,α]; ring)) leading h₁ (by dsimp only [A]; linarith)
  rw [max_eq_right (le_of_not_ge x)] at hmax
  by_cases y : max Z W ≤ Y
  · rw [max_eq_left y] at hmax
    have mass := lemma37_second_term hM hnp hp hC hk.le ha₀ ha₁ hb (by simpa only [Y,mul_assoc] using hmax)
    have norm : n^((5/2+s-γ)/den₂)*p^((5/2+s)/den₂) ≤ F :=
      (lemma37_second_powers hn hp ha₀ ha₁ hb₀ hb₁ hβ₀ hβ₁).trans (max_le leading mixed)
    exact finish (mass.trans_eq (by dsimp only [c₂,s,γ,den₂]; ring)) norm h₂ (by dsimp only [A]; linarith)
  rw [max_eq_right (le_of_not_ge y)] at hmax
  by_cases z : W ≤ Z
  · rw [max_eq_left z] at hmax
    have mass := lemma37_third_term hM hnp hp hC hk.le hb₀ hb' (by simpa only [Z,mul_assoc] using hmax)
    change M ≤ c₃*n^((8*b-4*b^2-2)/den₃)*p^β at mass
    rw [hthird] at mass
    exact finish (mass.trans_eq (by ring)) mixed h₃ (by dsimp only [A]; linarith)
  rw [max_eq_right (le_of_not_ge z)] at hmax
  have mass := lemma37_fourth_term hM hnp hp hC hk.le (by simpa only [W,mul_assoc] using hmax)
  have power : n^(10/17:ℝ)*p^(12/17:ℝ) ≤ F := by
    have e : (2:ℝ)-2*(12/17) = 10/17 := by norm_num
    rw [← e]
    exact (mixed_term_le (hβ₁.trans (by norm_num)) (by norm_num) hnp hp).trans (max_le mixed pairs)
  exact finish (mass.trans_eq (by dsimp only [c₄]; ring)) power h₄ (by dsimp only [A]; linarith)


/-- Substitute the rounded window, retaining the coefficient of the linear
contribution for absorption against the lower count. -/
theorem lemma37_substitute_window {A B a b : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 3/4) :
    ∃ K > 0, ∀ {ℓ d h t : ℝ}, 0 < ℓ → 0 < d → 0 ≤ h → 0 < t → h ≤ 3*t →
      A*(ℓ^2*d*h^(1/b) +
        ℓ^(3/2:ℝ)*d^(3/2+(3-4*a)/(2-2*a))*h^((2*b+1)/(2*b)) +
        ℓ^(1/b)*d^2*h^((4*b-2*b^2-1)/b^2)) + B*(ℓ^2*d^2+ℓ^(3/2:ℝ)*d^2*h^(5/4:ℝ)) ≤
      B*(ℓ^2*d^2) + K*(ℓ^2*d*t^(1/b) +
        ℓ^(3/2:ℝ)*d^(3/2+(3-4*a)/(2-2*a))*t^((2*b+1)/(2*b)) +
        ℓ^(1/b)*d^2*t^((4*b-2*b^2-1)/b^2) + ℓ^(3/2:ℝ)*d^2*t^(5/4:ℝ)) := by
  let r := 1/b
  let s := (2*b+1)/(2*b)
  let w := (4*b-2*b^2-1)/b^2
  let c₁ := A*(3:ℝ)^r
  let c₂ := A*(3:ℝ)^s
  let c₃ := A*(3:ℝ)^w
  let c₄ := B*(3:ℝ)^(5/4:ℝ)
  let K := 1+c₁+c₂+c₃+c₄
  have c1 : 0 ≤ c₁ := by dsimp only [c₁]; positivity
  have c2 : 0 ≤ c₂ := by dsimp only [c₂]; positivity
  have c3 : 0 ≤ c₃ := by dsimp only [c₃]; positivity
  have c4 : 0 ≤ c₄ := by dsimp only [c₄]; positivity
  have Kp : 0 < K := by dsimp only [K]; linarith
  have k₁ : c₁ ≤ K := by dsimp only [K]; linarith
  have k₂ : c₂ ≤ K := by dsimp only [K]; linarith
  have k₃ : c₃ ≤ K := by dsimp only [K]; linarith
  have k₄ : c₄ ≤ K := by dsimp only [K]; linarith
  have hb : 0 < b := by linarith
  have hr : 0 ≤ r := (one_div_pos.mpr hb).le
  have hs : 0 ≤ s := by dsimp only [s]; positivity
  have hw : 0 ≤ w := by
    have pos : 0 ≤ (1-b)*(2*b-1) := mul_nonneg (by linarith) (by linarith)
    have h : (4*b-2*b^2-1) = b+(1-b)*(2*b-1) := by ring
    unfold w
    rw [h]
    exact div_nonneg (add_nonneg hb.le pos) (sq_nonneg _)
  refine ⟨K,Kp,?_⟩
  intro ℓ d h t hℓ hd hh ht hcap
  let f₁ := ℓ^2*d
  let f₂ := ℓ^(3/2:ℝ)*d^(3/2+(3-4*a)/(2-2*a))
  let f₃ := ℓ^(1/b)*d^2
  let f₄ := ℓ^(3/2:ℝ)*d^2
  have f1 : 0 ≤ f₁ := by dsimp only [f₁]; positivity
  have f2 : 0 ≤ f₂ := by dsimp only [f₂]; positivity
  have f3 : 0 ≤ f₃ := by dsimp only [f₃]; positivity
  have f4 : 0 ≤ f₄ := by dsimp only [f₄]; positivity
  have shift {f x c : ℝ} (hf : 0 ≤ f) (hx : 0 ≤ x) (hc : 0 ≤ c)
      (hK : c*(3:ℝ)^x ≤ K) : c*(f*h^x) ≤ K*(f*t^x) := calc
    _ ≤ c*(f*(3*t)^x) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hh hcap hx) hf) hc
    _ = (c*(3:ℝ)^x)*(f*t^x) := by rw [Real.mul_rpow (by norm_num) ht.le]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hK (mul_nonneg hf (Real.rpow_nonneg ht.le _))
  change A*(f₁*h^r+f₂*h^s+f₃*h^w)+B*(ℓ^2*d^2+f₄*h^(5/4:ℝ)) ≤
    B*(ℓ^2*d^2)+K*(f₁*t^r+f₂*t^s+f₃*t^w+f₄*t^(5/4:ℝ))
  nlinarith only [shift f1 hr hA.le k₁, shift f2 hs hA.le k₂, shift f3 hw hA.le k₃,
    shift f4 (by norm_num : (0:ℝ) ≤ 5/4) hB.le k₄]

end OnlineReachabilityPreservers
