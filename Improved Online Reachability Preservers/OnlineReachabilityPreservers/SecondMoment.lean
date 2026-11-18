import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import OnlineReachabilityPreservers.IntersectionOrder

/-! Square sums of the clipped powers in the Appendix A second-moment estimate. -/

namespace OnlineReachabilityPreservers

open Finset Set MeasureTheory intervalIntegral

private theorem rpow_sq_of_nonneg {x : ℝ} (hx : 0 ≤ x) (r : ℝ) :
    (x^r)^2 = x^(2*r) := by
  rw [← Real.rpow_two, ← Real.rpow_mul hx, mul_comm]

theorem clippedPower_square_sum (N : ℕ) {A B r T : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 ≤ r) (hr' : r < 1/2) (hT : 0 < T) :
    (∑ i ∈ range N, (min (A * ((i+1 : ℕ) : ℝ)^(-r))
                          (B * ((i+1 : ℕ) : ℝ)^(-1 : ℝ)))^2) ≤
      A^2 * T^(1-2*r)/(1-2*r) + B^2/T := by
  let f (x : ℝ) := (min (A*x^(-r)) (B*x^(-1 : ℝ)))^2
  let g (x : ℝ) := A^2 * x^(-(2*r))
  let j (x : ℝ) := B^2 * x^(-2 : ℝ)
  have fg {x : ℝ} (hx : 0 ≤ x) : f x ≤ g x := calc
    _ ≤ (A*x^(-r))^2 := (sq_le_sq₀ (le_min (mul_nonneg hA (Real.rpow_nonneg hx _))
      (mul_nonneg hB (Real.rpow_nonneg hx _))) (mul_nonneg hA (Real.rpow_nonneg hx _))).mpr
      (min_le_left _ _)
    _ = _ := by
      unfold g
      rw [mul_pow, rpow_sq_of_nonneg hx, show 2*(-r) = -(2*r) by ring]
  have fj {x : ℝ} (hx : 0 ≤ x) : f x ≤ j x := calc
    _ ≤ (B*x^(-1 : ℝ))^2 := (sq_le_sq₀ (le_min (mul_nonneg hA (Real.rpow_nonneg hx _))
      (mul_nonneg hB (Real.rpow_nonneg hx _))) (mul_nonneg hB (Real.rpow_nonneg hx _))).mpr
      (min_le_right _ _)
    _ = _ := by
      unfold j
      rw [mul_pow, rpow_sq_of_nonneg hx]
      norm_num
  have hfmeas : Measurable f := by unfold f; fun_prop
  have gint (a b : ℝ) : IntervalIntegrable g volume a b :=
    (intervalIntegrable_rpow' (r := -(2*r)) (by linarith)).const_mul _
  have fint {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable f volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    have hig := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp (gint a b)
    apply Integrable.mono' hig hfmeas.aestronglyMeasurable
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact fg (ha.trans hx.1)
  have gformula (U : ℝ) :
      (∫ x in 0..U, g x) = A^2 * U^(1-2*r)/(1-2*r) := by
    unfold g
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
      show -(2*r)+1 = 1-2*r by ring, Real.zero_rpow (by linarith), sub_zero, mul_div_assoc]
  have anti : AntitoneOn f (Set.Ioc 0 (0 + (N : ℝ))) := by
    intro x hx y hy hxy
    have nx := le_min (mul_nonneg hA (Real.rpow_nonneg hx.1.le (-r)))
      (mul_nonneg hB (Real.rpow_nonneg hx.1.le (-1 : ℝ)))
    have ny := le_min (mul_nonneg hA (Real.rpow_nonneg hy.1.le (-r)))
      (mul_nonneg hB (Real.rpow_nonneg hy.1.le (-1 : ℝ)))
    exact (sq_le_sq₀ ny nx).mpr (min_le_min
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx.1 hxy (by linarith)) hA)
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx.1 hxy (by norm_num)) hB))
  have fn : IntervalIntegrable f volume 0 (N : ℝ) := fint le_rfl (by positivity)
  have finite : (∑ i ∈ range N, f (↑(i+1) : ℝ)) ≤ ∫ x in 0..(N : ℝ), f x := by
    simpa only [zero_add] using anti.sum_le_integral_of_integrableOn
      (by simpa only [zero_add] using (intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)).mp fn)
  refine finite.trans ?_
  by_cases hNT : (N : ℝ) ≤ T
  · have hu := integral_mono_on (by positivity : (0:ℝ) ≤ N) fn (gint 0 N) (fun _ hx => fg hx.1)
    rw [gformula] at hu
    refine hu.trans ?_
    have hpw := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ N) hNT (by linarith : 0 ≤ 1-2*r)
    have hratio : A^2 * (N:ℝ)^(1-2*r)/(1-2*r) ≤ A^2 * T^(1-2*r)/(1-2*r) := by
      gcongr
      linarith
    exact hratio.trans (le_add_of_nonneg_right (by positivity))
  · have hTN : T ≤ (N : ℝ) := le_of_lt (lt_of_not_ge hNT)
    have f₁ := fint (a := 0) (b := T) le_rfl hT.le
    have f₂ := fint hT.le hTN
    have first := integral_mono_on hT.le f₁ (gint 0 T) (fun _ hx => fg hx.1)
    rw [gformula] at first
    have zero_out : (0 : ℝ) ∉ Set.uIcc T (N : ℝ) := by simp [uIcc_of_le hTN, hT.not_ge]
    have jint : IntervalIntegrable j volume T (N : ℝ) :=
      (intervalIntegrable_rpow (r := (-2 : ℝ)) (Or.inr zero_out)).const_mul _
    have second := integral_mono_on hTN f₂ jint (fun _ hx => fj (hT.le.trans hx.1))
    have formula : (∫ x in T..(N : ℝ), j x) = B^2 * (T⁻¹ - (N : ℝ)⁻¹) := by
      unfold j
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by norm_num, zero_out⟩)]
      rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one, Real.rpow_neg_one]
      ring
    rw [formula] at second
    calc
      (∫ x in 0..(N : ℝ), f x) = (∫ x in 0..T, f x) + ∫ x in T..(N : ℝ), f x :=
        (integral_add_adjacent_intervals f₁ f₂).symm
      _ ≤ A^2 * T^(1-2*r)/(1-2*r) + B^2 * (T⁻¹ - (N : ℝ)⁻¹) := add_le_add first second
      _ ≤ _ := by
        rw [show B^2 / T = B^2 * T⁻¹ by rw [div_eq_mul_inv]]
        gcongr
        exact sub_le_self _ (by positivity)

/-- Balance the two clipped-power integrals at their crossover. -/
theorem clippedPower_square_sum_balanced (N : ℕ) {A B r : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hr : 0 ≤ r) (hr' : r < 1/2) :
    (∑ i ∈ range N, (min (A * ((i+1 : ℕ) : ℝ)^(-r))
                          (B * ((i+1 : ℕ) : ℝ)^(-1 : ℝ)))^2) ≤
      (1/(1-2*r)+1) * A^(1/(1-r)) * B^((1-2*r)/(1-r)) := by
  let T := (B/A)^(1/(1-r))
  have hr1 : 0 < 1-r := by linarith
  have hT : 0 < T := Real.rpow_pos_of_pos (div_pos hB hA) _
  have bound := clippedPower_square_sum N hA.le hB.le hr hr' hT
  let s := (1-2*r)/(1-r)
  have eA : 2-s = 1/(1-r) := by
    dsimp [s]
    field_simp [hr1.ne']
    ring
  have eB : 2-1/(1-r) = s := by linarith only [eA]
  have tpower : T^(1-2*r) = B^s/A^s := by
    dsimp [T, s]
    rw [← Real.rpow_mul (div_nonneg hB.le hA.le),
      show (1/(1-r))*(1-2*r) = (1-2*r)/(1-r) by ring,
      Real.div_rpow hB.le hA.le]
  have part₁ : A^2 * T^(1-2*r) = A^(1/(1-r))*B^s := by
    rw [tpower, ← mul_div_assoc, mul_comm (A^2), mul_div_assoc, ← Real.rpow_two A,
      ← Real.rpow_sub hA, eA]
    ring
  have part₂ : B^2/T = A^(1/(1-r))*B^s := by
    dsimp [T]
    rw [Real.div_rpow hB.le hA.le, div_div_eq_mul_div, mul_comm (B^2), mul_div_assoc,
      ← Real.rpow_two B, ← Real.rpow_sub hB, eB]
  rw [part₁, part₂] at bound
  convert bound using 1
  ring

private theorem sum_four_clips {x L M u v w z : ℝ} (hx : 0 ≤ x) (hL : x ≤ L) (hM : x ≤ M)
    (bound : x ≤ max u (max v (max w z))) :
    x^2 ≤ (min L u)^2 + (min v M)^2 + (min w M)^2 + (min z M)^2 := by
  rcases le_max_iff.mp bound with hu | rest
  · have h := (sq_le_sq₀ hx (hx.trans (le_min hL hu))).mpr (le_min hL hu)
    linarith only [h, sq_nonneg (min v M), sq_nonneg (min w M), sq_nonneg (min z M)]
  rcases le_max_iff.mp rest with hv | rest
  · have h := (sq_le_sq₀ hx (hx.trans (le_min hv hM))).mpr (le_min hv hM)
    linarith only [h, sq_nonneg (min L u), sq_nonneg (min w M), sq_nonneg (min z M)]
  rcases le_max_iff.mp rest with hw | hz
  · have h := (sq_le_sq₀ hx (hx.trans (le_min hw hM))).mpr (le_min hw hM)
    linarith only [h, sq_nonneg (min L u), sq_nonneg (min v M), sq_nonneg (min z M)]
  · have h := (sq_le_sq₀ hx (hx.trans (le_min hz hM))).mpr (le_min hz hM)
    linarith only [h, sq_nonneg (min L u), sq_nonneg (min v M), sq_nonneg (min w M)]

/-- Second-moment estimate for a ranked sequence with the four pointwise
envelopes used in Appendix A. The first is clipped by length and the others
are clipped by the rank bound from total incidence. -/
theorem square_sum_from_rank_bounds (N : ℕ) (values : ℕ → ℝ) {L M G A B K r s : ℝ}
    (hL : 0 < L) (hM : 0 < M) (hG : 0 < G) (hA : 0 < A) (hB : 0 < B) (hK : 0 < K)
    (hr : 0 ≤ r) (hr' : r < 1/2) (hs : 0 ≤ s) (hs' : s < 1/2)
    (nonneg : ∀ i < N, 0 ≤ values i) (cap : ∀ i < N, values i ≤ L)
    (mass : ∀ i < N, values i ≤ M * ((i+1 : ℕ) : ℝ)^(-1 : ℝ))
    (envelope : ∀ i < N, let x := ((i+1 : ℕ) : ℝ)
      values i ≤ max (G*x^(-1 : ℝ)) (max (A*x^(-r)) (max (B*x^(-s)) K))) :
    (∑ i ∈ range N, (values i)^2) ≤
      2*L*G + (1/(1-2*r)+1)*A^(1/(1-r))*M^((1-2*r)/(1-r)) +
      (1/(1-2*s)+1)*B^(1/(1-s))*M^((1-2*s)/(1-s)) + 2*K*M := by
  let x (i : ℕ) := ((i+1 : ℕ) : ℝ)
  let t₀ (i : ℕ) := min L (G*(x i)^(-1 : ℝ))
  let t₁ (i : ℕ) := min (A*(x i)^(-r)) (M*(x i)^(-1 : ℝ))
  let t₂ (i : ℕ) := min (B*(x i)^(-s)) (M*(x i)^(-1 : ℝ))
  let t₃ (i : ℕ) := min K (M*(x i)^(-1 : ℝ))
  have single : (∑ i ∈ range N, (values i)^2) ≤
      ∑ i ∈ range N, ((t₀ i)^2 + (t₁ i)^2 + (t₂ i)^2 + (t₃ i)^2) := by
    apply sum_le_sum
    intro i hi
    have hin := mem_range.mp hi
    exact sum_four_clips (nonneg i hin) (cap i hin) (mass i hin) (envelope i hin)
  have one : (∑ i ∈ range N, (t₀ i)^2) ≤ 2*L*G := by
    simpa [t₀, x, one_add_one_eq_two] using
      clippedPower_square_sum_balanced N hL hG (r := 0) le_rfl (by norm_num)
  have two : (∑ i ∈ range N, (t₁ i)^2) ≤ (1/(1-2*r)+1)*A^(1/(1-r))*M^((1-2*r)/(1-r)) :=
    clippedPower_square_sum_balanced N hA hM hr hr'
  have three : (∑ i ∈ range N, (t₂ i)^2) ≤ (1/(1-2*s)+1)*B^(1/(1-s))*M^((1-2*s)/(1-s)) :=
    clippedPower_square_sum_balanced N hB hM hs hs'
  have four : (∑ i ∈ range N, (t₃ i)^2) ≤ 2*K*M := by
    simpa [t₃, x, one_add_one_eq_two] using
      clippedPower_square_sum_balanced N hK hM (r := 0) le_rfl (by norm_num)
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib] at single
  exact single.trans (add_le_add (add_le_add (add_le_add one two) three) four)

private theorem rank_power_factor {n d C : ℝ} (hn : 0 < n) (hd : 0 ≤ d) (hC : 0 ≤ C)
    (a s t : ℝ) :
    (C*n^a)^s * (n*d)^t = C^s*n^(a*s+t)*d^t := by
  rw [Real.mul_rpow hC (Real.rpow_nonneg hn.le _), Real.mul_rpow hn.le hd,
    ← Real.rpow_mul hn.le, Real.rpow_add hn]
  ring

/-- The analytic implication of Lemma 31 for sorted path lengths with the
prefix-size envelope supplied by the inductive extremal estimate. -/
theorem lemma31_ranked_moment (N : ℕ) (values : ℕ → ℝ) {n d L C a b : ℝ}
    (hn : 0 < n) (hd : 0 < d) (hL : 0 < L) (hC : 0 < C)
    (ha₀ : 1/2 ≤ a) (ha₁ : a < 3/4) (hb₀ : 1/2 < b) (hb₁ : b ≤ 1)
    (nonneg : ∀ i < N, 0 ≤ values i)
    (decreasing : ∀ i j, i ≤ j → j < N → values j ≤ values i)
    (cap : ∀ i < N, values i ≤ L)
    (total : (∑ i ∈ range N, values i) ≤ n*d)
    (prefixBounds : ∀ k ≤ N, (∑ i ∈ range k, values i) ≤
      C * max n (max (n^a*(k:ℝ)^(2-2*a)) (max (n^(2-2*b)*(k:ℝ)^b) (k:ℝ)))) :
    (∑ i ∈ range N, (values i)^2) ≤
      2*C*n*(L+d) +
      (1/(3-4*a)+1)*C^(1/(2-2*a))*n^(3/2 : ℝ)*d^((3-4*a)/(2-2*a)) +
      (1/(2*b-1)+1)*C^(1/b)*n^(1/b)*d^((2*b-1)/b) := by
  let r := 2*a-1
  let s := 1-b
  have rank_le (i : ℕ) (hi : i < N) :
      values i * ((i+1 : ℕ) : ℝ) ≤ ∑ j ∈ range (i+1), values j := calc
    _ = ∑ _ ∈ range (i+1), values i := by simp [mul_comm]
    _ ≤ _ := sum_le_sum fun j hj => decreasing j i (by have := mem_range.mp hj; omega) hi
  have ranked_total (i : ℕ) (hi : i < N) : values i ≤ n*d * ((i+1 : ℕ) : ℝ)^(-1 : ℝ) := by
    have sub : range (i+1) ⊆ range N := range_mono (by omega)
    have hs := sum_le_sum_of_subset_of_nonneg sub (fun j hj _ => nonneg j (mem_range.mp hj))
    rw [Real.rpow_neg_one, ← div_eq_mul_inv]
    exact (le_div_iff₀ (by positivity)).mpr ((rank_le i hi).trans (hs.trans total))
  have ranked_terms (i : ℕ) (hi : i < N) :
      let x := ((i+1 : ℕ) : ℝ)
      values i ≤ max (C*n*x^(-1 : ℝ))
        (max (C*n^a*x^(-r)) (max (C*n^(2-2*b)*x^(-s)) C)) := by
    let x := ((i+1 : ℕ) : ℝ)
    have hx : 0 < x := by dsimp [x]; positivity
    have pp := (rank_le i hi).trans (prefixBounds (i+1) (by omega))
    have h := (le_div_iff₀ hx).mpr pp
    change values i ≤ C * max n (max (n^a*x^(2-2*a)) (max (n^(2-2*b)*x^b) x)) / x at h
    simp_rw [mul_max_of_nonneg _ _ hC.le, ← max_div_div_right hx.le] at h
    have divide (u : ℝ) : x^u / x = x^(u-1) := by rw [Real.rpow_sub hx, Real.rpow_one]
    have e₀ : C*n/x = C*n*x^(-1 : ℝ) := by rw [Real.rpow_neg_one, div_eq_mul_inv]
    have e₁ : C*(n^a*x^(2-2*a))/x = C*n^a*x^(-r) := by
      rw [← mul_assoc, mul_div_assoc, divide, show 2-2*a-1 = -r by dsimp [r]; ring]
    have e₂ : C*(n^(2-2*b)*x^b)/x = C*n^(2-2*b)*x^(-s) := by
      rw [← mul_assoc, mul_div_assoc, divide, show b-1 = -s by dsimp [s]; ring]
    simpa only [e₀, e₁, e₂, mul_div_cancel_right₀ C hx.ne'] using h
  have basic := square_sum_from_rank_bounds N values hL (mul_pos hn hd) (mul_pos hC hn)
    (mul_pos hC (Real.rpow_pos_of_pos hn _)) (mul_pos hC (Real.rpow_pos_of_pos hn _)) hC
    (show 0 ≤ r by dsimp [r]; linarith) (show r < 1/2 by dsimp [r]; linarith)
    (show 0 ≤ s by dsimp [s]; linarith) (show s < 1/2 by dsimp [s]; linarith)
    nonneg cap ranked_total ranked_terms
  have ar : 1-r = 2-2*a := by dsimp [r]; ring
  have ar2 : 1-2*r = 3-4*a := by dsimp [r]; ring
  have bs : 1-s = b := by dsimp [s]; ring
  have bs2 : 1-2*s = 2*b-1 := by dsimp [s]; ring
  have ha : (2-2*a : ℝ) ≠ 0 := by linarith
  have ae : a*(1/(2-2*a)) + (3-4*a)/(2-2*a) = 3/2 := calc
    _ = (a+(3-4*a))/(2-2*a) := by rw [mul_one_div, ← add_div]
    _ = _ := (div_eq_iff ha).mpr (by ring)
  have be : (2-2*b)*(1/b) + (2*b-1)/b = 1/b := calc
    _ = ((2-2*b)+(2*b-1))/b := by rw [mul_one_div, ← add_div]
    _ = _ := congrArg (· / b) (by ring)
  rw [ar, ar2, bs, bs2] at basic
  refine basic.trans_eq ?_
  calc
    _ = 2*L*(C*n) +
        (1/(3-4*a)+1)*((C*n^a)^(1/(2-2*a))*(n*d)^((3-4*a)/(2-2*a))) +
        (1/(2*b-1)+1)*((C*n^(2-2*b))^(1/b)*(n*d)^((2*b-1)/b)) + 2*C*(n*d) := by ring
    _ = _ := by
      rw [rank_power_factor hn hd.le hC.le, rank_power_factor hn hd.le hC.le, ae, be]
      ring

variable {V I : Type*} [LinearOrder V] [Fintype V] [LinearOrder I] [Fintype I]

omit [LinearOrder V] [Fintype V] in
private theorem descending_rank (paths : I → Finset V) :
    ∃ rank : Fin (Fintype.card I) ≃ I, Antitone (fun i => (paths (rank i)).card) := by
  classical
  let key (i : I) : ℕ ×ₗ I := toLex ((paths i).card, i)
  let keys := (univ : Finset I).image key
  have injective : Function.Injective key := fun _ _ eq => congrArg (fun k => (ofLex k).2) eq
  have cardinality : keys.card = Fintype.card I :=
    (card_image_of_injective _ injective).trans card_univ
  let numbered := keys.orderIsoOfFin cardinality
  let toKey : I ≃ keys := Equiv.ofBijective (fun i => ⟨key i, mem_image_of_mem _ (mem_univ _)⟩) ⟨
    fun _ _ e => injective (congrArg Subtype.val e),
    fun k => by obtain ⟨i, _, hi⟩ := mem_image.mp k.2; exact ⟨i, Subtype.ext hi⟩⟩
  let rank : Fin (Fintype.card I) ≃ I := Fin.revPerm.trans (numbered.toEquiv.trans toKey.symm)
  have rank_key (i : Fin (Fintype.card I)) : key (rank i) = (numbered i.rev).val :=
    congrArg Subtype.val (toKey.apply_symm_apply (numbered i.rev))
  refine ⟨rank, ?_⟩
  intro i j hij
  have key_le : key (rank j) ≤ key (rank i) := by
    rw [rank_key, rank_key]
    exact numbered.monotone (Fin.rev_le_rev.mpr hij)
  exact Prod.Lex.monotone_fst _ _ key_le

omit [LinearOrder V] [Fintype V] in
/-- List the path lengths in decreasing order. Every prefix corresponds to
an actual subfamily, whose indices keep their original path order. -/
theorem ranked_path_lengths (paths : I → Finset V) :
    ∃ values : ℕ → ℝ,
      (∀ i j, i ≤ j → j < Fintype.card I → values j ≤ values i) ∧
      (∀ i < Fintype.card I, ∃ j : I, values i = (paths j).card) ∧
      ∀ k ≤ Fintype.card I, ∃ J : Finset I, J.card = k ∧
        ∀ f : ℝ → ℝ, (∑ i ∈ range k, f (values i)) = ∑ j ∈ J, f ((paths j).card : ℝ) := by
  classical
  obtain ⟨rank, order⟩ := descending_rank paths
  let values (i : ℕ) : ℝ := if h : i < Fintype.card I then ((paths (rank ⟨i, h⟩)).card : ℝ) else 0
  refine ⟨values, ?_, ?_, ?_⟩
  · intro i j h hlt
    have hi : i < Fintype.card I := h.trans_lt hlt
    have hfin : (⟨i, hi⟩ : Fin (Fintype.card I)) ≤ ⟨j, hlt⟩ := h
    simp only [values, dite_eq_left hi, dite_eq_left hlt]
    exact_mod_cast (order hfin)
  · intro i hi
    exact ⟨rank ⟨i, hi⟩, by simp [values, hi]⟩
  · intro k hk
    let J := (univ : Finset (Fin k)).map ((Fin.castLEEmb hk).trans rank.toEmbedding)
    refine ⟨J, by simp [J], fun f => ?_⟩
    dsimp only [J]
    rw [sum_map, ← Fin.sum_univ_eq_sum_range (fun i => f (values i)) k]
    apply sum_congr rfl
    intro i _
    have hi : i.1 < Fintype.card I := i.2.trans_le hk
    simp [values, hi, Function.Embedding.trans_apply, Fin.castLE]

/-- Lemma 31 on ordered paths with a common vertex order. The input bound
is the inductive incidence-size envelope applied to each subfamily. -/
theorem lemma31_acyclic_moment (paths : I → Finset V) (free : HalfBridgeFree (PathBefore paths) 4)
    {d L C a b : ℝ} (hn : 0 < Fintype.card V) (hd : 0 < d) (hL : 0 < L) (hC : 0 < C)
    (ha₀ : 1/2 ≤ a) (ha₁ : a < 3/4) (hb₀ : 1/2 < b) (hb₁ : b ≤ 1)
    (cap : ∀ i, ((paths i).card : ℝ) ≤ L)
    (mass : (∑ i, ((paths i).card : ℝ)) ≤ (Fintype.card V : ℝ)*d)
    (subfamily : ∀ J : Finset I, HalfBridgeFree (PathBefore fun i : J => paths i.val) 4 →
      let n : ℝ := Fintype.card V
      let p : ℝ := J.card
      (∑ i ∈ J, ((paths i).card : ℝ)) ≤ C * max n (max (n^a*p^(2-2*a)) (max (n^(2-2*b)*p^b) p))) :
    let n : ℝ := Fintype.card V
    (∑ i, ((paths i).card : ℝ)^2) ≤
      2*C*n*(L+d) +
      (1/(3-4*a)+1)*C^(1/(2-2*a))*n^(3/2 : ℝ)*d^((3-4*a)/(2-2*a)) +
      (1/(2*b-1)+1)*C^(1/b)*n^(1/b)*d^((2*b-1)/b) := by
  let p := Fintype.card I
  obtain ⟨values, order, listed, prefixes⟩ := ranked_path_lengths paths
  obtain ⟨all, hc, sums⟩ := prefixes p le_rfl
  have heq : all = (Finset.univ : Finset I) := Finset.eq_univ_of_card _ hc
  have total : (∑ i ∈ range p, values i) = ∑ j, ((paths j).card : ℝ) := by
    simpa only [heq, id_eq] using sums id
  have positive : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hn
  have bound := lemma31_ranked_moment p values positive hd hL hC ha₀ ha₁ hb₀ hb₁
    (fun i hi => by obtain ⟨j, eq⟩ := listed i hi; rw [eq]; positivity) order
    (fun i hi => by obtain ⟨j, eq⟩ := listed i hi; rw [eq]; exact cap j) (total.le.trans mass) (by
      intro k hk
      obtain ⟨J, hJ, hsum⟩ := prefixes k hk
      have eq : (∑ i ∈ range k, values i) = ∑ j ∈ J, ((paths j).card : ℝ) := hsum id
      rw [eq]
      simpa only [hJ] using subfamily J (free.restrict_paths J))
  rw [sums (· ^ 2), heq] at bound
  exact bound

end OnlineReachabilityPreservers
