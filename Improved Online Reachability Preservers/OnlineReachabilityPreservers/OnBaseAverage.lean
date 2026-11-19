import OnlineReachabilityPreservers.DyadicSums
import OnlineReachabilityPreservers.OnBaseCounting

/-! The dyadic expectation bound for on-base tuples in Appendix A. -/

namespace OnlineReachabilityPreservers

open Finset

/-- The two arms in the on-base estimate sum geometrically on opposite sides
of the square root of the window height. -/
theorem lemma35_dyadic_arithmetic :
    ∃ K > 0, ∀ (s : Finset ℕ) {ℓ d h : ℝ}, 0 < ℓ → 1 ≤ d → 1 ≤ h →
      (∀ j ∈ s, (2:ℝ)^j ≤ d) →
      (∑ j ∈ s, (ℓ^2*d*(2:ℝ)^j +
        min (ℓ^(3/2:ℝ)*d^(3/2:ℝ)*h*((2:ℝ)^j)^(1/2:ℝ) +
            ℓ^(3/2:ℝ)*d^2*h^(3/2:ℝ)*((2:ℝ)^j)^(-(1/2):ℝ))
          (ℓ^(3/2:ℝ)*d^2*h*((2:ℝ)^j)^(1/2:ℝ)))) ≤
        K*(ℓ^2*d^2+ℓ^(3/2:ℝ)*d^2*h^(5/4:ℝ)) := by
  let A := (2:ℝ)^(1/2:ℝ)/((2:ℝ)^(1/2:ℝ)-1)
  let B := 1/(1-(2:ℝ)^(-(1/2):ℝ))
  have q : (1:ℝ) < 2^(1/2:ℝ) := by
    conv_lhs => rw [← Real.rpow_zero (2:ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  have q' : (2:ℝ)^(-(1/2):ℝ) < 1 := by
    conv_rhs => rw [← Real.rpow_zero (2:ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  have hA : 0 ≤ A := div_nonneg (zero_le_one.trans q.le) (sub_nonneg.mpr q.le)
  have hB : 0 ≤ B := (one_div_pos.mpr (sub_pos.mpr q')).le
  refine ⟨2+2*A+B, by linarith only [hA,hB], ?_⟩
  intro s ℓ d h hℓ hd hh cap
  have dpos := zero_lt_one.trans_le hd
  have hpos := zero_lt_one.trans_le hh
  let X := h^(1/2:ℝ)
  have hX : 0 < X := Real.rpow_pos_of_pos hpos _
  let small := s.filter fun j => (2:ℝ)^j ≤ X
  let large := s.filter fun j => ¬(2:ℝ)^j ≤ X
  let L (j : ℕ) := ℓ^2*d*(2:ℝ)^j
  let U := ℓ^(3/2:ℝ)*d^(3/2:ℝ)*h
  let V := ℓ^(3/2:ℝ)*d^2*h^(3/2:ℝ)
  let W := ℓ^(3/2:ℝ)*d^2*h
  let T (j : ℕ) := min (U*((2:ℝ)^j)^(1/2:ℝ)+V*((2:ℝ)^j)^(-(1/2):ℝ))
    (W*((2:ℝ)^j)^(1/2:ℝ))
  let F := ℓ^2*d^2
  let G := ℓ^(3/2:ℝ)*d^2*h^(5/4:ℝ)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have coefU : 0 ≤ U := by dsimp [U]; positivity
  have coefV : 0 ≤ V := by dsimp [V]; positivity
  have coefW : 0 ≤ W := by dsimp [W]; positivity
  have baseSum : (∑ j ∈ s, (2:ℝ)^j) ≤ 2*d := by
    have h := dyadic_sum_below s (show (0:ℝ) < 1 by norm_num) dpos cap
    norm_num [Real.rpow_one] at h
    exact h
  have linear : (∑ j ∈ s, L j) ≤ 2*F := by
    simp only [L, ← mul_sum]
    exact (mul_le_mul_of_nonneg_left baseSum (by positivity)).trans_eq (by dsimp [F]; ring)
  have short : (∑ j ∈ small, T j) ≤ A*G := calc
    _ ≤ ∑ j ∈ small, W*((2:ℝ)^j)^(1/2:ℝ) := sum_le_sum fun _ _ => min_le_right _ _
    _ = W*∑ j ∈ small, ((2:ℝ)^j)^(1/2:ℝ) := (mul_sum _ _ _).symm
    _ ≤ W*(A*X^(1/2:ℝ)) := mul_le_mul_of_nonneg_left
      (dyadic_sum_below small (by norm_num) hX (fun j hj => (mem_filter.mp hj).2)) coefW
    _ = _ := by
      dsimp only [W, X, G]
      rw [← Real.rpow_mul hpos.le, show (1/2:ℝ)*(1/2) = 1/4 by norm_num]
      calc
        _ = A*(ℓ^(3/2:ℝ)*d^2*(h^(1:ℝ)*h^(1/4:ℝ))) := by rw [Real.rpow_one]; ring
        _ = _ := by rw [← Real.rpow_add hpos]; norm_num
  have longPositive : (∑ j ∈ large, ((2:ℝ)^j)^(1/2:ℝ)) ≤ A*d^(1/2:ℝ) :=
    dyadic_sum_below large (by norm_num) dpos (fun j hj => cap j (mem_filter.mp hj).1)
  have longNegative : (∑ j ∈ large, ((2:ℝ)^j)^(-(1/2):ℝ)) ≤ B*X^(-(1/2):ℝ) :=
    dyadic_sum_above large (by norm_num) hX (fun _ hj => le_of_not_ge (mem_filter.mp hj).2)
  have positive : U*d^(1/2:ℝ) ≤ G := calc
    _ = ℓ^(3/2:ℝ)*(d^(3/2:ℝ)*d^(1/2:ℝ))*h := by dsimp [U]; ring
    _ = ℓ^(3/2:ℝ)*d^2*h := by rw [← Real.rpow_add dpos]; norm_num [Real.rpow_two]
    _ ≤ _ := by
      have hpow : h ≤ h^(5/4:ℝ) := by
        conv_lhs => rw [← Real.rpow_one h]
        exact Real.rpow_le_rpow_of_exponent_le hh (by norm_num)
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have negative : V*X^(-(1/2):ℝ)=G := by
    dsimp only [V, X, G]
    rw [← Real.rpow_mul hpos.le, mul_assoc, mul_assoc, ← Real.rpow_add hpos]
    norm_num
    ring
  have long : (∑ j ∈ large, T j) ≤ (A+B)*G := calc
    _ ≤ ∑ j ∈ large, (U*((2:ℝ)^j)^(1/2:ℝ)+V*((2:ℝ)^j)^(-(1/2):ℝ)) :=
      sum_le_sum fun _ _ => min_le_left _ _
    _ = U*(∑ j ∈ large, ((2:ℝ)^j)^(1/2:ℝ)) + V*(∑ j ∈ large, ((2:ℝ)^j)^(-(1/2):ℝ)) := by
      rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ U*(A*d^(1/2:ℝ))+V*(B*X^(-(1/2):ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left longPositive coefU)
        (mul_le_mul_of_nonneg_left longNegative coefV)
    _ = A*(U*d^(1/2:ℝ))+B*(V*X^(-(1/2):ℝ)) := by ring
    _ ≤ _ := by
      rw [negative, add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left positive hA) le_rfl
  have partition : (∑ j ∈ s, T j) = (∑ j ∈ small, T j)+(∑ j ∈ large, T j) := by
    classical
    exact (sum_filter_add_sum_filter_not s (fun j => (2:ℝ)^j ≤ X) T).symm
  change (∑ j ∈ s, (L j+T j)) ≤ (2+2*A+B)*(F+G)
  rw [sum_add_distrib, partition]
  nlinarith only [linear, short, long, mul_nonneg hA hF, mul_nonneg hB hF, hG]

private theorem predecessor_middle_power {y x a : ℝ} (hy : 0 < y) (hx : 0 < x)
    (ha₀ : 2/3 ≤ a) (ha₁ : a ≤ 3/4) :
    (y^a/x)^(1/(2*a-1)) ≤ y/x+y^2/x^3 := by
  let r := 1/(2*a-1)
  let Y := y^(1/2:ℝ)
  have Ypos : 0 < Y := Real.rpow_pos_of_pos hy _
  have Ysq : Y^2 = y := by dsimp [Y]; rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hy.le]
  have hd : 0 < 2*a-1 := by linarith
  have rlo : 1 ≤ r := (le_div_iff₀ hd).mpr (by linarith)
  have rhi : r ≤ 3 := (div_le_iff₀ hd).mpr (by linarith)
  have e : a*r = (1/2)+(1/2)*r := by
    have h : (2*a-1)*r = 1 := by
      dsimp only [r]
      rw [← mul_div_assoc, mul_one, div_self hd.ne']
    nlinarith only [h]
  have numerator : y^(a*r) = Y*Y^r := by
    dsimp only [Y]
    rw [← Real.rpow_mul hy.le, ← Real.rpow_add hy, e]
  have term : (y^a/x)^r = Y*(Y/x)^r := by
    rw [Real.div_rpow (Real.rpow_nonneg hy.le _) hx.le, ← Real.rpow_mul hy.le a r,
      numerator, Real.div_rpow Ypos.le hx.le, mul_div_assoc]
  change (y^a/x)^r ≤ _
  rw [term]
  by_cases small : x ≤ Y
  · have base : 1 ≤ Y/x := (one_le_div hx).mpr small
    have hp : (Y/x)^r ≤ (Y/x)^3 := by
      have pow := Real.rpow_natCast (Y/x) 3
      simp only [Nat.cast_ofNat] at pow
      rw [← pow]
      exact Real.rpow_le_rpow_of_exponent_le base rhi
    calc
      _ ≤ Y*(Y/x)^3 := mul_le_mul_of_nonneg_left hp Ypos.le
      _ = y^2/x^3 := by rw [div_pow, ← mul_div_assoc, show Y*Y^3 = (Y^2)^2 by ring, Ysq]
      _ ≤ _ := le_add_of_nonneg_left (by positivity)
  · have base : Y/x ≤ 1 := (div_le_one hx).mpr (le_of_not_ge small)
    have hp := Real.rpow_le_rpow_of_exponent_ge (div_pos Ypos hx) base rlo
    rw [Real.rpow_one] at hp
    calc
      _ ≤ Y*(Y/x) := mul_le_mul_of_nonneg_left hp Ypos.le
      _ = y/x := by rw [← mul_div_assoc, ← pow_two, Ysq]
      _ ≤ _ := le_add_of_nonneg_right (by positivity)

private theorem predecessor_last_power {y x b : ℝ} (hy : 0 < y) (hx : 1 ≤ x)
    (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 3/4) :
    (y^(2-2*b)/x)^(1/(1-b)) ≤ y^2/x^3 := by
  let s := 1/(1-b)
  have hb : 0 < 1-b := by linarith
  have ss : 3 ≤ s := (le_div_iff₀ hb).mpr (by linarith)
  have e : (2-2*b)*s = 2 := by dsimp [s]; field_simp
  have hx' := zero_lt_one.trans_le hx
  have exp : x^3 ≤ x^s := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx (by simpa only [Nat.cast_ofNat] using ss)
  change (y^(2-2*b)/x)^s ≤ _
  rw [Real.div_rpow (Real.rpow_nonneg hy.le _) hx'.le, ← Real.rpow_mul hy.le, e, Real.rpow_two]
  exact div_le_div_of_nonneg_left (sq_nonneg y) (pow_pos hx' _) exp

private theorem predecessor_count_coarse {C a b : ℝ} (hC : 1 ≤ C)
    (ha₀ : 2/3 ≤ a) (ha₁ : a ≤ 3/4) (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 3/4) :
    ∃ K ≥ 1, ∀ {M x d h : ℝ}, 1 ≤ x → 0 < d → 1 ≤ h →
      M ≤ d^2*h/x →
      (C < x → let y := d*h
        M ≤ C*y/x+(C*y^a/x)^(1/(2*a-1))+(C*y^(2-2*b)/x)^(1/(1-b))) →
      let y := d*h
      M ≤ K*min (y/x+y^2/x^3) (d^2*h/x) := by
  let r := 1/(2*a-1)
  let s := 1/(1-b)
  let K := 1+C+C^r+C^s+C^2
  have Cpos := zero_lt_one.trans_le hC
  have rnn : 0 ≤ C^r := Real.rpow_nonneg Cpos.le _
  have snn : 0 ≤ C^s := Real.rpow_nonneg Cpos.le _
  have K1 : 1 ≤ K := by dsimp only [K]; linarith only [rnn, snn, sq_nonneg C, Cpos]
  refine ⟨K, K1, ?_⟩
  intro M x d h hx hd hh det env
  let y := d*h
  have hpos := zero_lt_one.trans_le hh
  have ypos : 0 < y := mul_pos hd hpos
  have xpos := zero_lt_one.trans_le hx
  let G := y/x+y^2/x^3
  let T := d^2*h/x
  have Gnn : 0 ≤ G := by dsimp only [G]; positivity
  have Tnn : 0 ≤ T := by dsimp only [T]; positivity
  have aux : M ≤ K*G := by
    by_cases big : C < x
    · have middle :
          (C*y^a/x)^r ≤ C^r*G := by
        rw [mul_div_assoc, Real.mul_rpow Cpos.le (div_nonneg (Real.rpow_nonneg ypos.le _) xpos.le)]
        exact mul_le_mul_of_nonneg_left (predecessor_middle_power ypos xpos ha₀ ha₁) rnn
      have last : (C*y^(2-2*b)/x)^s ≤ C^s*G := by
        rw [mul_div_assoc, Real.mul_rpow Cpos.le (div_nonneg (Real.rpow_nonneg ypos.le _) xpos.le)]
        have h := (predecessor_last_power ypos hx hb₀ hb₁).trans
          (le_add_of_nonneg_left (show 0 ≤ y/x by positivity))
        exact mul_le_mul_of_nonneg_left h snn
      have first : C*y/x ≤ C*G := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) Cpos.le
      have combined := (env big).trans (add_le_add (add_le_add first middle) last)
      exact combined.trans (by dsimp only [K]; nlinarith only [Gnn, mul_nonneg (sq_nonneg C) Gnn])
    · have xC : x ≤ C := le_of_not_gt big
      have hsq : x^2 ≤ C^2 := (sq_le_sq₀ xpos.le Cpos.le).mpr xC
      have hpow : d^2*h/x ≤ C^2*(y^2/x^3) := calc
        _ = (d^2*h*x^2)/x^3 := by field_simp
        _ ≤ (d^2*h*(C^2*h))/x^3 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left
            (hsq.trans ((mul_one (C^2)).symm.le.trans (mul_le_mul_of_nonneg_left hh (sq_nonneg C))))
            (by positivity)
        _ = _ := by dsimp only [y]; ring
      have kC : C^2 ≤ K := by dsimp only [K]; linarith only [rnn, snn, Cpos]
      exact det.trans (hpow.trans ((mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (show 0 ≤ y/x by positivity)) (sq_nonneg C)).trans
          (mul_le_mul_of_nonneg_right kC Gnn)))
  have det' : M ≤ K*T := det.trans ((one_mul T).symm.le.trans (mul_le_mul_of_nonneg_right K1 Tnn))
  change M ≤ K * min G T
  rw [mul_min_of_nonneg _ _ (zero_le_one.trans K1)]
  exact le_min aux det'

/-- A uniform coarse count for each actual family of bases through an off-base
vertex, including thresholds below the inductive envelope coefficient. -/
theorem lemma35_large_bases_coarse {C a b : ℝ} (hC : 1 ≤ C)
    (ha₀ : 2/3 ≤ a) (ha₁ : a ≤ 3/4) (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 3/4) :
    ∃ K ≥ 1, ∀ {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype I]
      {paths : I → Finset V} (_ : HalfBridgeFree (PathBefore paths) 4)
      (u : V) (D h x : ℕ), 0 < D → 0 < h → 0 < x →
      (∀ v, (occurrences paths v).card ≤ D) → InducedSizeBound paths C a b →
      let y : ℝ := (D:ℝ)*h
      ((largeBranchBases paths u h x).card:ℝ) ≤
        K*min (y/x+y^2/(x:ℝ)^3) ((D:ℝ)^2*h/x) := by
  obtain ⟨K, hK, coarse⟩ := predecessor_count_coarse hC ha₀ ha₁ hb₀ hb₁
  refine ⟨K, hK, ?_⟩
  intro V I _ _ _ paths free u D h x hD hh hx degree input
  let J := largeBranchBases paths u h x
  let S := predecessorSupport paths u h
  let y : ℝ := (D:ℝ)*h
  have x1 : (1:ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x from hx)
  have xpos : (0:ℝ) < x := Nat.cast_pos.mpr hx
  have h1 : (1:ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h from hh)
  have dpos : (0:ℝ) < D := Nat.cast_pos.mpr hD
  have det : (J.card:ℝ) ≤ (D:ℝ)^2*h/x := by
    apply (le_div_iff₀ xpos).mpr
    have h := (lemma32_degree_count paths u h x D degree).trans
      (Nat.mul_le_mul_right D (Nat.mul_le_mul_right h (degree u)))
    exact_mod_cast (h.trans_eq (by ring))
  apply coarse x1 dpos h1 det
  intro big
  have size : (S.card:ℝ) ≤ y := by
    have hs := (predecessorSupport_card paths u h).trans (Nat.mul_le_mul_right h (degree u))
    change (S.card:ℝ) ≤ (D:ℝ)*h
    exact_mod_cast hs
  have actual := lemma32_extremal_count free u h x (zero_lt_one.trans_le hC) big
    (by linarith only [ha₀]) (by linarith only [hb₁]) input
  have rnn : 0 ≤ 1/(2*a-1) := one_div_nonneg.mpr (by linarith only [ha₀])
  have snn : 0 ≤ 1/(1-b) := one_div_nonneg.mpr (by linarith only [hb₁])
  have enn : 0 ≤ 2-2*b := by linarith only [hb₁]
  refine actual.trans ?_
  change C*(S.card:ℝ)/x+(C*(S.card:ℝ)^a/x)^(1/(2*a-1))+
    (C*(S.card:ℝ)^(2-2*b)/x)^(1/(1-b)) ≤
    C*y/x+(C*y^a/x)^(1/(2*a-1))+(C*y^(2-2*b)/x)^(1/(1-b))
  gcongr

private theorem sqrt_sum_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a+b) ≤ Real.sqrt a+Real.sqrt b := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt (add_nonneg ha hb), add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
  linarith only [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

private theorem rpow_square {x : ℝ} (hx : 0 ≤ x) (r : ℝ) : (x^r)^2 = x^(2*r) := by
  rw [← Real.rpow_two, ← Real.rpow_mul hx, mul_comm]

/-- Insert the important-incidence bound into the two arms of the
coarse estimate for the number of base paths. -/
theorem lemma35_bucket_upper {ℓ d h x K P M : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hh : 0 < h) (hx : 0 < x) (hK : 1 ≤ K)
    (coarse : P ≤ K*min (d*h/x+(d*h)^2/x^3) (d^2*h/x))
    (marked : M ≤ 2*ℓ*d+2*d*Real.sqrt (ℓ*h*P)) :
    ℓ*x*M ≤ 2*Real.sqrt K*(ℓ^2*d*x +
      min (ℓ^(3/2:ℝ)*d^(3/2:ℝ)*h*x^(1/2:ℝ) + ℓ^(3/2:ℝ)*d^2*h^(3/2:ℝ)*x^(-(1/2):ℝ))
        (ℓ^(3/2:ℝ)*d^2*h*x^(1/2:ℝ))) := by
  let a := d*h/x
  let b := (d*h)^2/x^3
  let c := d^2*h/x
  let f := ℓ*x*d
  let U := ℓ^(3/2:ℝ)*d^(3/2:ℝ)*h*x^(1/2:ℝ)
  let V := ℓ^(3/2:ℝ)*d^2*h^(3/2:ℝ)*x^(-(1/2):ℝ)
  let W := ℓ^(3/2:ℝ)*d^2*h*x^(1/2:ℝ)
  let S := Real.sqrt K
  have ann : 0 ≤ a := by dsimp [a]; positivity
  have bnn : 0 ≤ b := by dsimp [b]; positivity
  have cnn : 0 ≤ c := by dsimp [c]; positivity
  have fnn : 0 ≤ f := by dsimp [f]; positivity
  have hS : 1 ≤ S := (Real.le_sqrt (by norm_num) (zero_le_one.trans hK)).mpr (by norm_num; exact hK)
  have hsqrt (z : ℝ) (pred : P ≤ K*z) :
      Real.sqrt (ℓ*h*P) ≤ S*Real.sqrt (ℓ*h*z) := calc
    _ ≤ Real.sqrt ((ℓ*h)*(K*z)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left pred (by positivity))
    _ = _ := by rw [show (ℓ*h)*(K*z)=K*(ℓ*h*z) by ring, Real.sqrt_mul (zero_le_one.trans hK)]
  have first : f*Real.sqrt (ℓ*h*a) = U := by
    apply (sq_eq_sq₀ (mul_nonneg fnn (Real.sqrt_nonneg _)) (by dsimp [U]; positivity)).mp
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    dsimp only [f, a, U]
    simp only [mul_pow, rpow_square hℓ.le, rpow_square hd.le, rpow_square hx.le]
    norm_num [Real.rpow_one, Real.rpow_natCast]
    field_simp
  have second : f*Real.sqrt (ℓ*h*b) = V := by
    apply (sq_eq_sq₀ (mul_nonneg fnn (Real.sqrt_nonneg _)) (by dsimp [V]; positivity)).mp
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    dsimp only [f, b, V]
    simp only [mul_pow, rpow_square hℓ.le, rpow_square hh.le, rpow_square hx.le]
    norm_num [Real.rpow_neg_one, Real.rpow_natCast]
    field_simp
  have third : f*Real.sqrt (ℓ*h*c) = W := by
    apply (sq_eq_sq₀ (mul_nonneg fnn (Real.sqrt_nonneg _)) (by dsimp [W]; positivity)).mp
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    dsimp only [f, c, W]
    simp only [mul_pow, rpow_square hℓ.le, rpow_square hx.le]
    norm_num [Real.rpow_one, Real.rpow_natCast]
    field_simp
  have ta : P ≤ K*(a+b) :=
    coarse.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (zero_le_one.trans hK))
  have tc : P ≤ K*c :=
    coarse.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (zero_le_one.trans hK))
  have arm₁ : f*Real.sqrt (ℓ*h*P) ≤ S*(U+V) := calc
    _ ≤ f*(S*Real.sqrt (ℓ*h*(a+b))) := mul_le_mul_of_nonneg_left (hsqrt (a+b) ta) fnn
    _ = (f*S)*Real.sqrt (ℓ*h*a+ℓ*h*b) := by rw [mul_add]; ring
    _ ≤ (f*S)*(Real.sqrt (ℓ*h*a)+Real.sqrt (ℓ*h*b)) :=
      mul_le_mul_of_nonneg_left (sqrt_sum_le (by positivity) (by positivity))
        (mul_nonneg fnn (zero_le_one.trans hS))
    _ = S*(f*Real.sqrt (ℓ*h*a)+f*Real.sqrt (ℓ*h*b)) := by ring
    _ = _ := by rw [first, second]
  have arm₂ : f*Real.sqrt (ℓ*h*P) ≤ S*W := calc
    _ ≤ f*(S*Real.sqrt (ℓ*h*c)) := mul_le_mul_of_nonneg_left (hsqrt c tc) fnn
    _ = S*(f*Real.sqrt (ℓ*h*c)) := by ring
    _ = _ := by rw [third]
  have arms : f*Real.sqrt (ℓ*h*P) ≤ S*min (U+V) W := by
    rw [mul_min_of_nonneg _ _ (zero_le_one.trans hS)]
    exact le_min arm₁ arm₂
  have linear : ℓ^2*d*x ≤ S*(ℓ^2*d*x) :=
    (one_mul _).symm.le.trans (mul_le_mul_of_nonneg_right hS (by positivity))
  change ℓ*x*M ≤ 2*S*(ℓ^2*d*x+min (U+V) W)
  calc
    _ ≤ ℓ*x*(2*ℓ*d+2*d*Real.sqrt (ℓ*h*P)) := mul_le_mul_of_nonneg_left marked (by positivity)
    _ = 2*(ℓ^2*d*x+f*Real.sqrt (ℓ*h*P)) := by dsimp only [f]; ring
    _ ≤ _ := by nlinarith only [linear, arms]



/-- The finite Appendix A on-base estimate. The vertex and path dimensions
are kept separate from the uniform degree and length caps. -/
theorem lemma35_on_base_sum {C a b : ℝ} (hC : 1 ≤ C)
    (ha₀ : 2/3 ≤ a) (ha₁ : a ≤ 3/4) (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 3/4) :
    ∃ A > 0, ∀ {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype V] [Fintype I]
      {paths : I → Finset V} (_ : HalfBridgeFree (PathBefore paths) 4) (L D h : ℕ),
      0 < h → h ≤ L → h ≤ D →
      (∀ i, (paths i).card ≤ L) →
      (∀ v, (occurrences paths v).card ≤ D) → InducedSizeBound paths C a b →
      let ℓ : ℝ := L
      let d : ℝ := D
      let t : ℝ := h
      ℓ*(∑ base, ((onBaseBranchTuples paths base h).card:ℝ)) ≤
        A*(Fintype.card V:ℝ)*d*(ℓ^2*d^2+ℓ^(3/2:ℝ)*d^2*t^(5/4:ℝ)) := by
  obtain ⟨K, hK, coarse⟩ := lemma35_large_bases_coarse hC ha₀ ha₁ hb₀ hb₁
  obtain ⟨G, hG, geometric⟩ := lemma35_dyadic_arithmetic
  have sqp : 0 < Real.sqrt K := Real.sqrt_pos.2 (zero_lt_one.trans_le hK)
  refine ⟨12*Real.sqrt K*G, by positivity, ?_⟩
  intro V I _ _ _ _ paths free L D h hh hL hD lengths degrees input
  dsimp only
  let ℓ : ℝ := L
  let d : ℝ := D
  let t : ℝ := h
  let n : ℝ := Fintype.card V
  let J := range (Nat.log 2 D+1)
  let x (j : ℕ) : ℝ := (2:ℝ)^j
  let M (u : V) (j : ℕ) : ℝ := importantBaseIncidences paths u h (2^j)
  let B (j : ℕ) := ℓ^2*d*x j +
    min (ℓ^(3/2:ℝ)*d^(3/2:ℝ)*t*(x j)^(1/2:ℝ) +
        ℓ^(3/2:ℝ)*d^2*t^(3/2:ℝ)*(x j)^(-(1/2):ℝ))
      (ℓ^(3/2:ℝ)*d^2*t*(x j)^(1/2:ℝ))
  have dl : 0 < D := hh.trans_le hD
  have hℓ : 0 < ℓ := Nat.cast_pos.mpr (hh.trans_le hL)
  have hd : 0 < d := Nat.cast_pos.mpr dl
  have ht : 0 < t := Nat.cast_pos.mpr hh
  have hd1 : 1 ≤ d := by change (1:ℝ) ≤ D; exact_mod_cast (show 1 ≤ D from dl)
  have ht1 : 1 ≤ t := by change (1:ℝ) ≤ h; exact_mod_cast (show 1 ≤ h from hh)
  have upper (j : ℕ) (u : V) : ℓ*x j*M u j ≤ 2*Real.sqrt K*B j := by
    have xp : (0:ℝ) < x j := pow_pos (by norm_num) j
    let P : ℝ := (largeBranchBases paths u h (2^j)).card
    let S : ℝ := (predecessorSupport paths u h).card
    let N : ℝ := (predecessorSupport paths u h ∪ successorSupport paths u).card
    have hS : S ≤ d*t := by
      change ((predecessorSupport paths u h).card:ℝ) ≤ (D:ℝ)*h
      exact_mod_cast (predecessorSupport_card paths u h).trans (Nat.mul_le_mul_right h (degrees u))
    have hN : N ≤ 2*ℓ*d := by
      change ((predecessorSupport paths u h ∪ successorSupport paths u).card:ℝ) ≤ 2*(L:ℝ)*D
      have nCap : (predecessorSupport paths u h ∪ successorSupport paths u).card ≤ 2*L*D := calc
        _ ≤ (predecessorSupport paths u h).card + (successorSupport paths u).card := card_union_le _ _
        _ ≤ D*h+D*L := Nat.add_le_add
          ((predecessorSupport_card paths u h).trans (Nat.mul_le_mul_right h (degrees u)))
          ((successorSupport_card paths u L lengths).trans (Nat.mul_le_mul_right L (degrees u)))
        _ ≤ D*L+D*L := Nat.add_le_add_right (Nat.mul_le_mul_left D hL) _
        _ = _ := by ring
      exact_mod_cast nCap
    have pPos : 0 ≤ P := Nat.cast_nonneg _
    have mark : M u j ≤ 2*ℓ*d+2*d*Real.sqrt (ℓ*t*P) := calc
      _ ≤ N+Real.sqrt (2*N*(P*S)) := lemma35_important_upper free u h (2^j) (Nat.pow_pos (by decide))
      _ ≤ (2*ℓ*d)+Real.sqrt (2*(2*ℓ*d)*(P*(d*t))) := by
        have sGood : 0 ≤ S := Nat.cast_nonneg _
        have nGood : 0 ≤ N := Nat.cast_nonneg _
        exact add_le_add hN (Real.sqrt_le_sqrt (by gcongr))
      _ = _ := by
        rw [show 2*(2*ℓ*d)*(P*(d*t))=(2*d)^2*(ℓ*t*P) by ring,
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    have prior := coarse free u D h (2^j) dl hh (Nat.pow_pos (by decide)) degrees input
    have cBound : P ≤ K*min (d*t/x j+(d*t)^2/(x j)^3) (d^2*t/x j) := by
      simpa only [P, d, t, x, Nat.cast_pow, Nat.cast_ofNat] using prior
    exact lemma35_bucket_upper hℓ hd ht xp hK cBound mark
  have bucket (j : ℕ) :
      ℓ*(2*x j*(d+t+1))*(∑ u, M u j) ≤ (12*Real.sqrt K*n*d)*B j := calc
    _ = 2*(d+t+1)*∑ u, ℓ*x j*M u j := by
      rw [← mul_sum]
      ring
    _ ≤ (6*d)*∑ u, ℓ*x j*M u j := by
      have htD : t ≤ d := Nat.cast_le.mpr hD
      apply mul_le_mul_of_nonneg_right (by linarith only [htD, hd1])
      apply sum_nonneg
      intro u _
      exact mul_nonneg (mul_nonneg hℓ.le (pow_nonneg (by norm_num) _)) (Nat.cast_nonneg _)
    _ ≤ (6*d)*∑ _u : V, 2*Real.sqrt K*B j :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun u _ => upper j u) (by positivity)
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]; dsimp only [n]; ring
  have count : (∑ base, ((onBaseBranchTuples paths base h).card:ℝ)) ≤
      ∑ j ∈ J, 2*x j*(d+t+1)*(∑ u, M u j) := by
    dsimp only [J, x, d, t, M]
    exact_mod_cast lemma35_on_base_dyadic_count free h D degrees
  have cutoff (j : ℕ) (hj : j ∈ J) : (2:ℝ)^j ≤ d := by
    have hs : j ≤ Nat.log 2 D := Nat.le_of_lt_succ (mem_range.mp hj)
    have hpow : (2:ℕ)^j ≤ D :=
      (Nat.pow_le_pow_right (by decide) hs).trans (Nat.pow_log_le_self 2 dl.ne')
    change (2:ℝ)^j ≤ (D:ℝ)
    exact_mod_cast hpow
  have sumGeom : (∑ j ∈ J, B j) ≤ G*(ℓ^2*d^2+ℓ^(3/2:ℝ)*d^2*t^(5/4:ℝ)) :=
    geometric J hℓ hd1 ht1 cutoff
  change ℓ*(∑ base, ((onBaseBranchTuples paths base h).card:ℝ)) ≤
    (12*Real.sqrt K*G)*n*d*(ℓ^2*d^2+ℓ^(3/2:ℝ)*d^2*t^(5/4:ℝ))
  calc
    _ ≤ ℓ*∑ j ∈ J, 2*x j*(d+t+1)*(∑ u, M u j) := mul_le_mul_of_nonneg_left count hℓ.le
    _ ≤ ∑ j ∈ J, (12*Real.sqrt K*n*d)*B j := by
      rw [mul_sum]
      exact sum_le_sum fun j _ => (by simpa only [mul_assoc] using bucket j)
    _ = (12*Real.sqrt K*n*d)*∑ j ∈ J, B j := (mul_sum _ _ _).symm
    _ ≤ _ := (mul_le_mul_of_nonneg_left sumGeom (by dsimp only [n]; positivity)).trans_eq (by ring)

set_option maxHeartbeats 500000 in
/-- Averaging over the base paths gives the two terms of Lemma 35 with no
logarithmic loss. The caps are at most four times the corresponding averages. -/
theorem lemma35_on_base_expectation {C a b : ℝ} (hC : 1 ≤ C)
    (ha₀ : 2/3 ≤ a) (ha₁ : a ≤ 3/4) (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 3/4) :
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
      (∑ base, ((onBaseBranchTuples paths base h).card:ℝ))/(p:ℝ) ≤
        A*(ℓ^2*d^2+ℓ^(3/2:ℝ)*d^2*(h:ℝ)^(5/4:ℝ)) := by
  obtain ⟨K, hK, bound⟩ := lemma35_on_base_sum hC ha₀ ha₁ hb₀ hb₁
  refine ⟨1024*K, by positivity, ?_⟩
  intro V I _ _ _ _ paths free L D h hn hp hh hL hD length degree input
  dsimp only
  let n := Fintype.card V
  let p := Fintype.card I
  let M := ∑ i, (paths i).card
  intro hM capL capD
  let ℓ : ℝ := (M:ℝ)/p
  let d : ℝ := (M:ℝ)/n
  let F := (L:ℝ)^2*(D:ℝ)^2 + (L:ℝ)^(3/2:ℝ)*(D:ℝ)^2*(h:ℝ)^(5/4:ℝ)
  let G := ℓ^2*d^2+ℓ^(3/2:ℝ)*d^2*(h:ℝ)^(5/4:ℝ)
  let Q := ∑ base, ((onBaseBranchTuples paths base h).card:ℝ)
  have ppos : (0:ℝ) < p := Nat.cast_pos.mpr hp
  have npos : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have mpos : (0:ℝ) < M := Nat.cast_pos.mpr hM
  have lpos : 0 < ℓ := div_pos mpos ppos
  have dpos : 0 < d := div_pos mpos npos
  have Lpos : (0:ℝ) < L := Nat.cast_pos.mpr (hh.trans_le hL)
  have Fpos : 0 ≤ F := by dsimp only [F]; positivity
  have individual : M ≤ L*p := calc
    _ ≤ ∑ _ : I, L := sum_le_sum (fun i _ => length i)
    _ = _ := by simp [p, mul_comm]
  have ndlp : (n:ℝ)*D ≤ 4*(L:ℝ)*p := calc
    _ ≤ 4*(M:ℝ) := by exact_mod_cast (Nat.mul_comm n D).le.trans capD
    _ ≤ _ := by
      have hh : (M:ℝ) ≤ (L:ℝ)*p := by exact_mod_cast individual
      exact (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 4)).trans_eq (by ring)
  have Lcap : (L:ℝ) ≤ 4*ℓ := by
    change (L:ℝ) ≤ 4*((M:ℝ)/p)
    rw [← mul_div_assoc, le_div_iff₀ ppos]
    exact_mod_cast capL
  have Dcap : (D:ℝ) ≤ 4*d := by
    change (D:ℝ) ≤ 4*((M:ℝ)/n)
    rw [← mul_div_assoc, le_div_iff₀ npos]
    exact_mod_cast capD
  have size : F ≤ 256*G := by
    have hD2 : (D:ℝ)^2 ≤ (4*d)^2 := pow_le_pow_left₀ (Nat.cast_nonneg D) Dcap 2
    have a₁ : (L:ℝ)^2*(D:ℝ)^2 ≤ 256*(ℓ^2*d^2) :=
      (mul_le_mul (pow_le_pow_left₀ Lpos.le Lcap 2) hD2 (sq_nonneg (D:ℝ))
        (sq_nonneg (4*ℓ))).trans_eq (by ring)
    have lbound : (L:ℝ)^(3/2:ℝ) ≤ 16*ℓ^(3/2:ℝ) := calc
      _ ≤ (4*ℓ)^(3/2:ℝ) := Real.rpow_le_rpow Lpos.le Lcap (by norm_num)
      _ = (4:ℝ)^(3/2:ℝ)*ℓ^(3/2:ℝ) := Real.mul_rpow (by norm_num) lpos.le
      _ ≤ _ := by
        have hp : (4:ℝ)^(3/2:ℝ) ≤ 16 := by
          calc
            _ ≤ (4:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = _ := by norm_num [Real.rpow_two]
        exact mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg lpos.le (3/2))
    have a₂ : (L:ℝ)^(3/2:ℝ)*(D:ℝ)^2*(h:ℝ)^(5/4:ℝ) ≤
        256*(ℓ^(3/2:ℝ)*d^2*(h:ℝ)^(5/4:ℝ)) :=
      (mul_le_mul_of_nonneg_right
        (mul_le_mul lbound hD2 (sq_nonneg (D:ℝ)) (mul_nonneg (by norm_num)
          (Real.rpow_nonneg lpos.le _)))
        (Real.rpow_nonneg (Nat.cast_nonneg h) _)).trans_eq (by ring)
    exact (add_le_add a₁ a₂).trans_eq (by dsimp only [G]; ring)
  have qBound : (L:ℝ)*Q ≤ (4*K)*(L:ℝ)*p*F := calc
    _ ≤ K*(n:ℝ)*D*F := bound free L D h hh hL hD length degree input
    _ = (K*F)*((n:ℝ)*D) := by ring
    _ ≤ (K*F)*(4*(L:ℝ)*p) := mul_le_mul_of_nonneg_left ndlp (mul_nonneg hK.le Fpos)
    _ = _ := by ring
  have mean : Q/(p:ℝ) ≤ (4*K)*F := by
    apply (div_le_iff₀ ppos).mpr
    apply le_of_mul_le_mul_left (a := (L:ℝ)) _ Lpos
    exact qBound.trans_eq (by ring)
  exact mean.trans ((mul_le_mul_of_nonneg_left size (mul_nonneg (by norm_num) hK.le)).trans_eq (by ring))

end OnlineReachabilityPreservers
