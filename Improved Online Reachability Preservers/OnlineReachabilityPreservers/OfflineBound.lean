import OnlineReachabilityPreservers.BranchWindow
import OnlineReachabilityPreservers.OfflineArithmetic
import OnlineReachabilityPreservers.OfflineMoment
import OnlineReachabilityPreservers.Regularization

/-! The Appendix B incidence update on finite acyclic path systems. -/

namespace OnlineReachabilityPreservers

/-- The rate used at each step of the offline incidence induction. -/
noncomputable def offlineRate (b n p : ℝ) : ℝ :=
  max n (max (n^(3/4 : ℝ)*p^(1/2 : ℝ)) (max (n^(2-2*b)*p^b) p))

theorem offlineRate_mono {b n n' p p' : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 1)
    (hn : 0 ≤ n) (hp : 0 ≤ p) (h1 : n ≤ n') (h2 : p ≤ p') :
    offlineRate b n p ≤ offlineRate b n' p' := by
  have hn' := hn.trans h1
  have hp' := hp.trans h2
  have he : 0 ≤ 2-2*b := by linarith
  unfold offlineRate
  gcongr

private theorem offlineRate_double {b n p : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 1)
    (hn : 0 ≤ n) (hp : 0 ≤ p) :
    offlineRate b (2*n) (2*p) ≤ 4*offlineRate b n p := by
  have shift {f g : ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g) (hfg : f+g ≤ 2) :
      (2*n)^f*(2*p)^g ≤ 4*(n^f*p^g) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hp]
    calc
      _ = ((2 : ℝ)^f*(2 : ℝ)^g)*(n^f*p^g) := by ring
      _ ≤ _ := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) hfg).trans_eq (by norm_num)
  let F := offlineRate b n p
  have hN : n ≤ F := le_max_left _ _
  have hP : p ≤ F := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hF : n^(3/4 : ℝ)*p^(1/2 : ℝ) ≤ F := (le_max_left _ _).trans (le_max_right _ _)
  have hG : n^(2-2*b)*p^b ≤ F :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  unfold offlineRate at ⊢
  change max (2*n) (max _ (max _ (2*p))) ≤ 4*F
  refine max_le (by linarith) (max_le ?_ (max_le ?_ (by linarith)))
  · exact (shift (by norm_num) (by norm_num) (by norm_num)).trans
      (mul_le_mul_of_nonneg_left hF (by norm_num))
  · exact (shift (by linarith) hb (by linarith)).trans (mul_le_mul_of_nonneg_left hG (by norm_num))

private theorem offline_window_term_le {b n p : ℝ} (hb : b ≤ 3/4)
    (hn : 0 < n) (hp : 0 < p) :
    n^(1/2 : ℝ)*p^(3/4 : ℝ) ≤ offlineRate b n p := by
  by_cases h : p ≤ n^2
  · let e : ℝ := 3/4-b
    have he : 0 ≤ e := sub_nonneg.mpr hb
    have hpow := Real.rpow_le_rpow hp.le h he
    rw [← Real.rpow_natCast_mul hn.le 2] at hpow
    have hG : n^(2-2*b)*p^b ≤ offlineRate b n p :=
      (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    refine le_trans ?_ hG
    calc
      _ = n^(1/2 : ℝ)*p^e*p^b := by
        rw [mul_assoc, ← Real.rpow_add hp, sub_add_cancel]
      _ ≤ n^(1/2 : ℝ)*n^(2*e)*p^b := by
        push_cast at hpow
        gcongr
      _ = _ := by
        rw [← Real.rpow_add hn]
        congr 2
        dsimp [e]
        ring
  · have hpow := Real.rpow_le_rpow (pow_nonneg hn.le 2) (le_of_not_ge h)
      (show (0 : ℝ) ≤ 1/4 by norm_num)
    rw [← Real.rpow_natCast_mul hn.le 2] at hpow
    have h' : n^(1/2 : ℝ) ≤ p^(1/4 : ℝ) := by convert hpow using 2; norm_num
    have hP : p ≤ offlineRate b n p :=
      (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    calc
      _ ≤ p^(1/4 : ℝ)*p^(3/4 : ℝ) := mul_le_mul_of_nonneg_right h' (by positivity)
      _ = p := by rw [← Real.rpow_add hp]; norm_num
      _ ≤ _ := hP

/-- Insert the degree, length and window caps into the three moment terms.
The logarithm of the sample size is bounded using its ambient vertex count. -/
theorem offline_sample_scale {C : ℝ} (hC : 1 ≤ C) :
    ∃ K ≥ 1, ∀ {b M n p N L D : ℝ}, 1/2 < b → b ≤ 1 → 0 < M → 1 ≤ n → 0 < p → p ≤ M →
      1 ≤ N → 0 < L → 0 < D →
      let ℓ := M/p; let d := M/n; let t := C*p/(ℓ*d^2)
      L ≤ 4*ℓ → D ≤ 4*d → N ≤ 48*ℓ*d*t →
      N*L + (2+Real.log N)*N^(3/2 : ℝ) + N^(1/b)*D^((2*b-1)/b) ≤
        K*(ℓ^2*d*t + (2+Real.log n)*ℓ^(3/2 : ℝ)*d^(3/2 : ℝ)*t^(3/2 : ℝ) +
          ℓ^(1/b)*d^2*t^(1/b)) := by
  let a := 1+Real.log (48*C)
  let x := a * 48^(3/2 : ℝ)
  let y' : ℝ := 48^2*4
  have cpos : 0 < C := zero_lt_one.trans_le hC
  have hc48 : 1 ≤ 48*C := by linarith
  have logc := Real.log_nonneg hc48
  have ax : 0 ≤ x := by dsimp [x, a]; positivity
  have hy' : 0 ≤ y' := by norm_num [y']
  refine ⟨192+x+y', by linarith, ?_⟩
  intro b M n p N L D hb hb_le hM hn hp hpM hN hL hD
  let e := (2*b-1)/b
  let w := 1/b
  let y := (48 : ℝ)^w*(4 : ℝ)^e
  have bpos : 0 < b := by linarith
  have wpos : 0 < w := one_div_pos.mpr bpos
  have wle : w ≤ 2 := (div_le_iff₀ bpos).mpr (by linarith)
  have enonneg : 0 ≤ e := div_nonneg (by linarith) bpos.le
  have ele : e ≤ 1 := (div_le_iff₀ bpos).mpr (by linarith)
  have ay : y ≤ y' := by
    change (48 : ℝ)^w*(4 : ℝ)^e ≤ 48^2*4
    conv_rhs => rw [← Real.rpow_two (48 : ℝ), ← Real.rpow_one (4 : ℝ)]
    exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by norm_num) wle)
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) ele) (by positivity) (by positivity)
  dsimp only
  let ℓ := M/p
  let d := M/n
  let t := C*p/(ℓ*d^2)
  intro hLc hDc hNc
  change L ≤ 4*ℓ at hLc
  change D ≤ 4*d at hDc
  change N ≤ 48*ℓ*d*t at hNc
  have npos := zero_lt_one.trans_le hn
  have lpos : 0 < ℓ := div_pos hM hp
  have dpos : 0 < d := div_pos hM npos
  have tpos : 0 < t := by dsimp [t]; positivity
  have Npos := zero_lt_one.trans_le hN
  have size : N ≤ (48*C)*n := calc
    _ ≤ _ := hNc
    _ = (48*C)*n*(p/M) := by dsimp [t, ℓ, d]; field_simp
    _ ≤ _ := (mul_le_mul_of_nonneg_left ((div_le_one hM).mpr hpM) (by positivity)).trans_eq (mul_one _)
  have lg := Real.log_le_log Npos size
  rw [Real.log_mul (by positivity : (48*C : ℝ) ≠ 0) npos.ne'] at lg
  have log_bound : 2+Real.log N ≤ a*(2+Real.log n) := by
    dsimp [a]
    nlinarith only [lg, logc, mul_nonneg logc (Real.log_nonneg hn)]
  have first : N*L ≤ 192*(ℓ^2*d*t) := by
    exact (mul_le_mul hNc hLc hL.le (by positivity)).trans_eq (by ring)
  have middle : (2+Real.log N)*N^(3/2 : ℝ) ≤
      x*((2+Real.log n)*ℓ^(3/2 : ℝ)*d^(3/2 : ℝ)*t^(3/2 : ℝ)) := calc
    _ ≤ (a*(2+Real.log n))*(48*ℓ*d*t)^(3/2 : ℝ) := by
      apply mul_le_mul log_bound (Real.rpow_le_rpow Npos.le hNc (by norm_num)) (by positivity)
      exact mul_nonneg (by dsimp [a]; linarith) (by linarith [Real.log_nonneg hn])
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0 ≤ 48*ℓ*d) tpos.le,
        Real.mul_rpow (by positivity : 0 ≤ 48*ℓ) dpos.le, Real.mul_rpow (by norm_num) lpos.le]
      unfold x
      ring
  have deg : w+e = 2 := by dsimp [w, e]; field_simp; ring
  have last : N^w*D^e ≤ y*(ℓ^w*d^2*t^w) := calc
    _ ≤ (48*ℓ*d*t)^w*(4*d)^e := mul_le_mul
      (Real.rpow_le_rpow Npos.le hNc wpos.le) (Real.rpow_le_rpow hD.le hDc enonneg)
      (by positivity) (by positivity)
    _ = y*(ℓ^w*(d^w*d^e)*t^w) := by
      rw [Real.mul_rpow (by positivity : 0 ≤ 48*ℓ*d) tpos.le,
        Real.mul_rpow (by positivity : 0 ≤ 48*ℓ) dpos.le,
        Real.mul_rpow (by norm_num) lpos.le, Real.mul_rpow (by norm_num) dpos.le]
      unfold y
      ring
    _ = _ := by rw [← Real.rpow_add dpos, deg, Real.rpow_two]
  let X := ℓ^2*d*t
  let Y := (2+Real.log n)*ℓ^(3/2 : ℝ)*d^(3/2 : ℝ)*t^(3/2 : ℝ)
  let Z := ℓ^w*d^2*t^w
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by
    have : 0 ≤ 2+Real.log n := by linarith [Real.log_nonneg hn]
    dsimp [Y]
    positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  change N*L+(2+Real.log N)*N^(3/2 : ℝ)+N^w*D^e ≤ (192+x+y')*(X+Y+Z)
  calc
    _ ≤ 192*X+x*Y+y*Z := add_le_add (add_le_add first middle) last
    _ ≤ (192+x+y')*X+(192+x+y')*Y+(192+x+y')*Z := by
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_right (by linarith) hX) (mul_le_mul_of_nonneg_right (by linarith) hY))
        (mul_le_mul_of_nonneg_right (by linarith) hZ)
    _ = _ := by ring


open Finset

universe u v

/-- A uniform incidence bound for finite full-bridge-free systems with a common
vertex order. The quantifier includes induced subsystems and acyclic splits. -/
def OfflineIncidenceBound (b B : ℝ) : Prop :=
  ∀ (V : Type u) (I : Type v) [LinearOrder V] [LinearOrder I] [Fintype V] [Fintype I]
    (paths : I → Finset V), BridgeFree (PathBefore paths) 4 →
    (∑ i, ((paths i).card : ℝ)) ≤ offlineRate b (Fintype.card V) (Fintype.card I) * B

private theorem mean_lower_real {n p M Q : ℕ} (hn : 0 < n) (hp : 0 < p)
    (lower : M^4 ≤ 4096*n^2*p*Q) :
    let ℓ : ℝ := (M:ℝ)/p
    let d : ℝ := (M:ℝ)/n
    ℓ^2*d^2 ≤ 4096*((Q:ℝ)/p) := by
  dsimp only
  have npos : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have ppos : (0:ℝ) < p := Nat.cast_pos.mpr hp
  have hr : (M:ℝ)^4 ≤ 4096*(n:ℝ)^2*p*Q := by exact_mod_cast lower
  apply le_of_mul_le_mul_right (a := (n:ℝ)^2*(p:ℝ)^2) _
    (mul_pos (sq_pos_of_pos npos) (sq_pos_of_pos ppos))
  convert hr using 1
  · field_simp [npos.ne', ppos.ne']
  · field_simp [ppos.ne']

private theorem offline_sample_mean {V : Type u} {I : Type v}
    [LinearOrder V] [LinearOrder I] [Fintype V] [Fintype I]
    {b B N : ℝ} (prior : OfflineIncidenceBound.{u,v} b B)
    (hb : 1/2 < b) (hb_le : b ≤ 1) (hB : 0 < B)
    {paths : I → Finset V} (free : BridgeFree (PathBefore paths) 4)
    (L D h : ℕ) (hp : 0 < Fintype.card I) (hnN : 1 ≤ N)
    (hL : 0 < L) (hD : 0 < D) (hDN : (D:ℝ) ≤ N)
    (lengths : ∀ i, (paths i).card ≤ L) (degrees : ∀ x, (occurrences paths x).card ≤ D)
    (ambient : ∀ base, ((branchSupport paths base h).card : ℝ) ≤ N) :
    let q := (∑ base : I, ((branchTuples paths base h).card : ℝ))/(Fintype.card I:ℝ)
    q ≤ 2*B*N*L + Real.exp 8*(max 1 B)^2*(2+Real.log N)*N^(3/2:ℝ) +
      (2*B+(1/(2*b-1)+1)*B^(1/b))*N^(1/b)*(D:ℝ)^((2*b-1)/b) := by
  dsimp only
  let E := 2*B*N*L + Real.exp 8*(max 1 B)^2*(2+Real.log N)*N^(3/2:ℝ) +
      (2*B+(1/(2*b-1)+1)*B^(1/b))*N^(1/b)*(D:ℝ)^((2*b-1)/b)
  have hLr : (0:ℝ) < L := Nat.cast_pos.mpr hL
  have ppos : (0:ℝ) < Fintype.card I := Nat.cast_pos.mpr hp
  have bpos : 0 ≤ b := by linarith only [hb]
  apply (div_le_iff₀ ppos).mpr
  calc
    _ ≤ ∑ _ : I, E := by
      apply sum_le_sum
      intro base _
      let S := branchSupport paths base h
      exact lemma41_sampled_upper free base h D hnN hD hDN hLr hB hb hb_le (ambient base)
        (fun i => Nat.cast_le.mpr (lengths i)) (fun x _ => degrees x) (by
          intro J inherited
          have bound := prior S J (inducedPaths paths S J) inherited
          simp only [Fintype.card_coe] at bound
          change _ ≤ B*offlineRate b N (J.card : ℝ)
          rw [mul_comm B]
          exact bound.trans (mul_le_mul_of_nonneg_right
            (offlineRate_mono bpos hb_le (Nat.cast_nonneg _) (Nat.cast_nonneg _) (ambient base) le_rfl) hB.le))
    _ = _ := by
      change (∑ _ : I, E) = E*(Fintype.card I:ℝ)
      rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]

private theorem offline_moment_weight_le {B b : ℝ} (hB : 1 ≤ B) (hb : 2/3 ≤ b) :
    2*B + Real.exp 8*(max 1 B)^2 + (2*B+(1/(2*b-1)+1)*B^(1/b)) ≤
      (8+Real.exp 8)*B^2 := by
  have hBp := zero_lt_one.trans_le hB
  have hb' : 0 < b := by linarith
  have hden : 0 < 2*b-1 := by linarith
  have e : 1/b ≤ 2 := (div_le_iff₀ hb').mpr (by linarith)
  have f : 1/(2*b-1)+1 ≤ 4 := by
    have h : 1/(2*b-1) ≤ 3 := (div_le_iff₀ hden).mpr (by linarith)
    linarith
  have Bsq : B ≤ B^2 := by
    rw [pow_two]
    exact (one_mul B).symm.le.trans (mul_le_mul_of_nonneg_right hB hBp.le)
  have Bpow : B^(1/b) ≤ B^2 := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hB e
  have z := mul_le_mul f Bpow (Real.rpow_nonneg hBp.le _) (by norm_num : (0:ℝ) ≤ 4)
  rw [max_eq_right hB]
  linarith only [Bsq, z]

private theorem sqrt_coefficient {B R : ℝ} (hB : 1 ≤ B) (hR : 0 ≤ R) (hle : R^2 ≤ B) :
    R*B^(1/2:ℝ) ≤ B := by
  have hBp := zero_le_one.trans hB
  have hS : 0 ≤ B^(1/2:ℝ) := Real.rpow_nonneg hBp _
  have heq : (B^(1/2:ℝ))^2 = B := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hBp]
  have hr := (sq_le_sq₀ hR hS).mp (hle.trans_eq heq.symm)
  exact (mul_le_mul_of_nonneg_right hr hS).trans_eq (by rw [← pow_two, heq])

set_option maxHeartbeats 900000 in
private theorem offline_regular_step :
    ∃ R ≥ 1, ∀ {b B : ℝ}, 2/3 ≤ b → b ≤ 71/100 → 1 ≤ B →
      OfflineIncidenceBound.{u,v} b B → ∀ {V : Type u} {I : Type v}
      [LinearOrder V] [LinearOrder I] [Fintype V] [Fintype I]
      (paths : I → Finset V) (_ : BridgeFree (PathBefore paths) 4) (L D : ℕ),
      0 < Fintype.card V → 0 < Fintype.card I → 0 < L → 0 < D →
      let M := ∑ i, (paths i).card
      16*Fintype.card V < M → 8*Fintype.card I < M →
      L*Fintype.card I ≤ 4*M → D*Fintype.card V ≤ 4*M →
      (∀ i, (paths i).card ≤ L) → (∀ x, (occurrences paths x).card ≤ D) →
      (M : ℝ) ≤ R*B^(1/2:ℝ)*offlineRate (offlineExponentStep b) (Fintype.card V) (Fintype.card I) := by
  let C : ℝ := 40960
  have hC : 1 ≤ C := by norm_num [C]
  have hCp : 0 < C := zero_lt_one.trans_le hC
  obtain ⟨K, hK, scale⟩ := offline_sample_scale hC
  let K₀ := 4096*((8+Real.exp 8)*K)
  have hK₀ : 1 ≤ K₀ := by
    have he := Real.exp_nonneg 8
    calc
      (1 : ℝ) ≤ 4096*(8*1) := by norm_num
      _ ≤ _ := by dsimp only [K₀]; gcongr; linarith
  let U := (3*C)^(1/4 : ℝ)
  have hU : 0 < U := by dsimp [U]; positivity
  let A₀ := 1+3*K₀*C+253*(3*K₀*C^(3/2:ℝ))
  have hA₀ : 1 ≤ A₀ := by
    have hKp := zero_lt_one.trans_le hK₀
    dsimp only [A₀]
    have h₁ : 0 ≤ 3*K₀*C := by positivity
    have h₂ : 0 ≤ 253*(3*K₀*C^(3/2:ℝ)) := by positivity
    linarith only [h₁, h₂]
  let R := U+2*A₀
  have hR : 1 ≤ R := by dsimp only [R]; linarith only [hU, hA₀]
  refine ⟨R, hR, ?_⟩
  intro b B hb₀ hb₁ hB prior
  have hBp := zero_lt_one.trans_le hB
  let S := B^(1/2:ℝ)
  have hS : 1 ≤ S := by
    unfold S
    conv_lhs => rw [← Real.one_rpow (1/2:ℝ)]
    exact Real.rpow_le_rpow zero_le_one hB (by norm_num)
  let A := offlineComparisonConstant C (K₀*B^2) b
  have hKp := zero_lt_one.trans_le hK₀
  have hA : 0 < A := offlineComparisonConstant_pos hCp (by positivity)
  have coeff : U+2*A ≤ R*S := by
    have hA' : A ≤ A₀*S := offlineComparisonConstant_le hC hK₀ hB hb₀ (by linarith)
    have hU' : U ≤ U*S :=
      (mul_one U).symm.le.trans (mul_le_mul_of_nonneg_left hS hU.le)
    dsimp only [R]
    nlinarith only [hA', hU']
  let β := offlineExponentStep b
  have hb : 1/2 < b := by linarith
  have b_le_one : b ≤ 1 := by linarith
  have beta_high : β ≤ 3/4 := by
    change (2*b+1)/(2*b+2) ≤ (3/4 : ℝ)
    exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  let c₁ := 2*B
  let c₂ := Real.exp 8 * (max 1 B)^2
  let c₃ := 2*B+(1/(2*b-1)+1)*B^(1/b)
  let W := c₁+c₂+c₃
  have hc₁ : 0 < c₁ := by dsimp [c₁]; positivity
  have hc₂ : 0 ≤ c₂ := by dsimp [c₂]; positivity
  have hc₃ : 0 ≤ c₃ := by
    have : 0 < 2*b-1 := by linarith
    dsimp [c₃]
    positivity
  have hW : 0 < W := by dsimp only [W]; linarith
  have Wle : W ≤ (8+Real.exp 8)*B^2 := offline_moment_weight_le hB hb₀
  have Wscaled : 4096*(W*K) ≤ K₀*B^2 := calc
    _ ≤ 4096*(((8+Real.exp 8)*B^2)*K) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right Wle (zero_le_one.trans hK)) (by norm_num)
    _ = _ := by dsimp only [K₀]; ring
  intro V I _ _ _ _ paths free L D hn hp hL hD
  dsimp only
  let n := Fintype.card V
  let p := Fintype.card I
  let M := ∑ i, (paths i).card
  intro hdense hlong hcapL hcapD lengths degrees
  change 16*n < M at hdense
  change 8*p < M at hlong
  change L*p ≤ 4*M at hcapL
  change D*n ≤ 4*M at hcapD
  have hM : 0 < M := by omega
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have npos : (0 : ℝ) < n := by exact_mod_cast hn
  have ppos : (0 : ℝ) < p := by exact_mod_cast hp
  have mpos : (0 : ℝ) < M := by exact_mod_cast hM
  let ℓ : ℝ := (M : ℝ)/p
  let d : ℝ := (M : ℝ)/n
  let t : ℝ := C*p/(ℓ*d^2)
  have lpos : 0 < ℓ := div_pos mpos ppos
  have dpos : 0 < d := div_pos mpos npos
  let h := (40960*n^2*p^2)/M^3+1
  have cube : M^3 ≤ 2048*(n*p)^2 :=
    ((lemma27_acyclic paths free.halfFree).resolve_left (not_le_of_gt hdense)).resolve_left
      (not_le_of_gt hlong)
  obtain ⟨hsum, hlarge⟩ := rounded_branch_window (C := 40960) hn hp hM (by decide) cube
  change (h:ℝ)+1 ≤ 3*t at hsum
  change 40960*n^2*p^2 ≤ (h+1)*M^3 at hlarge
  let F := offlineRate β (n : ℝ) (p : ℝ)
  have hF : 0 ≤ F := npos.le.trans (le_max_left _ _)
  change (M : ℝ) ≤ R*S*F
  refine le_trans ?_ (mul_le_mul_of_nonneg_right coeff hF)
  by_cases window : h*p ≤ M
  swap
  · have houtside : ℓ ≤ 3*t := by
      have h : (M : ℝ) ≤ (h : ℝ)*p := by exact_mod_cast (le_of_not_ge window)
      exact ((div_le_iff₀ ppos).mpr h).trans (by linarith)
    have hsmall := mass_large_length_window mpos npos ppos hCp houtside
    have hU' : U ≤ U+2*A := by linarith only [hA]
    exact (hsmall.trans_eq (mul_assoc _ _ _)).trans
      ((mul_le_mul_of_nonneg_left (offline_window_term_le beta_high npos ppos) hU.le).trans
      (mul_le_mul_of_nonneg_right hU' hF))
  let N : ℝ := (L : ℝ)*D*((h : ℝ)+1)
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have oneL : (1:ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L from hL)
  have oneD : (1:ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D from hD)
  have oneH : (1:ℝ) ≤ (h:ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg h)
  have hnN : 1 ≤ N := by
    have count := mul_le_mul (mul_le_mul oneL oneD zero_le_one hLr.le) oneH
      zero_le_one (mul_nonneg hLr.le hDr.le)
    simpa only [one_mul] using count
  have hDN : (D : ℝ) ≤ N := by
    have count := mul_le_mul (mul_le_mul_of_nonneg_right oneL hDr.le) oneH
      zero_le_one (mul_nonneg hLr.le hDr.le)
    simpa only [one_mul, mul_one] using count
  have capL : (L : ℝ) ≤ 4*ℓ := by
    change (L:ℝ) ≤ 4*((M:ℝ)/p)
    rw [← mul_div_assoc, le_div_iff₀ ppos]
    exact_mod_cast hcapL
  have capD : (D : ℝ) ≤ 4*d := by
    change (D:ℝ) ≤ 4*((M:ℝ)/n)
    rw [← mul_div_assoc, le_div_iff₀ npos]
    exact_mod_cast hcapD
  have sampleSize : N ≤ 48*ℓ*d*t := calc
    _ ≤ (4*ℓ)*(4*d)*(3*t) := mul_le_mul
      (mul_le_mul capL capD hDr.le (mul_nonneg (by norm_num) lpos.le)) hsum
      (zero_le_one.trans oneH)
      (mul_nonneg (mul_nonneg (by norm_num) lpos.le) (mul_nonneg (by norm_num) dpos.le))
    _ = _ := by ring
  let q : ℝ := (∑ base : I, ((branchTuples paths base h).card : ℝ))/p
  have lower : ℓ^2*d^2 ≤ 4096*q := by
    have count := lemma28_mean_lower free.halfFree L h lengths hn hp hdense.le hlong.le hcapL window hlarge
    let Q := ∑ base : I, (branchTuples paths base h).card
    have hmean := mean_lower_real (M := M) (Q := Q) hn hp count
    change ℓ^2*d^2 ≤ 4096*((Q:ℝ)/p) at hmean
    have heq : (Q:ℝ) = ∑ base : I, ((branchTuples paths base h).card:ℝ) :=
      Nat.cast_sum _ _
    rwa [heq] at hmean
  let J₁ := N*(L : ℝ)
  let J₂ := (2+Real.log N)*N^(3/2 : ℝ)
  let J₃ := N^(1/b)*(D : ℝ)^((2*b-1)/b)
  have j₁ : 0 ≤ J₁ := by unfold J₁; positivity
  have j₂ : 0 ≤ J₂ := by
    have : 0 ≤ 2+Real.log N := by linarith [Real.log_nonneg hnN]
    unfold J₂
    positivity
  have j₃ : 0 ≤ J₃ := by unfold J₃; positivity
  have upper : q ≤ W*(J₁+J₂+J₃) := by
    have cards (base : I) : ((branchSupport paths base h).card : ℝ) ≤ N := by
      change ((branchSupport paths base h).card : ℝ) ≤ (L:ℝ)*(D:ℝ)*((h:ℝ)+1)
      exact_mod_cast (branchSupport_card_caps paths base h L D (lengths base) (fun x _ => degrees x))
    have mean := offline_sample_mean prior hb b_le_one hBp free L D h hp hnN hL hD hDN lengths degrees cards
    have c₁W : c₁ ≤ W := by dsimp only [W]; linarith only [hc₂, hc₃]
    have c₂W : c₂ ≤ W := by dsimp only [W]; linarith only [hc₁, hc₃]
    have c₃W : c₃ ≤ W := by dsimp only [W]; linarith only [hc₁, hc₂]
    calc
      _ ≤ c₁*J₁+c₂*J₂+c₃*J₃ := mean.trans_eq (by dsimp only [c₁, c₂, c₃, J₁, J₂, J₃]; ring)
      _ ≤ W*J₁+W*J₂+W*J₃ := add_le_add
        (add_le_add (mul_le_mul_of_nonneg_right c₁W j₁) (mul_le_mul_of_nonneg_right c₂W j₂))
        (mul_le_mul_of_nonneg_right c₃W j₃)
      _ = _ := by ring
  have scaled := scale hb b_le_one mpos hnr ppos (by exact_mod_cast (show p ≤ M by omega)) hnN hLr hDr capL capD sampleSize
  have compare : ℓ^2*d^2 ≤ (4096*(W*K))*(ℓ^2*d*t +
      (2+Real.log n)*ℓ^(3/2 : ℝ)*d^(3/2 : ℝ)*t^(3/2 : ℝ) + ℓ^(1/b)*d^2*t^(1/b)) := calc
    _ ≤ 4096*q := lower
    _ ≤ 4096*(W*(J₁+J₂+J₃)) := mul_le_mul_of_nonneg_left upper (by norm_num)
    _ ≤ _ := (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left scaled hW.le)
      (show (0 : ℝ) ≤ 4096 by norm_num)).trans_eq (by ring)
  have hlog : 0 ≤ 2+Real.log (n:ℝ) := by linarith [Real.log_nonneg hnr]
  have tpos : 0 < t := div_pos (mul_pos hCp ppos) (mul_pos lpos (sq_pos_of_pos dpos))
  have second :
      0 ≤ (2+Real.log n)*ℓ^(3/2 : ℝ)*d^(3/2 : ℝ)*t^(3/2 : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg hlog (Real.rpow_nonneg lpos.le _))
      (Real.rpow_nonneg dpos.le _)) (Real.rpow_nonneg tpos.le _)
  have third : 0 ≤ ℓ^(1/b)*d^2*t^(1/b) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg lpos.le _) (sq_nonneg _))
      (Real.rpow_nonneg tpos.le _)
  have compare' : ℓ^2*d^2 ≤ (K₀*B^2)*(ℓ^2*d*t +
      (2+Real.log n)*ℓ^(3/2 : ℝ)*d^(3/2 : ℝ)*t^(3/2 : ℝ) + ℓ^(1/b)*d^2*t^(1/b)) :=
    compare.trans (mul_le_mul_of_nonneg_right Wscaled
      (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) dpos.le) tpos.le) second) third))
  have mass := lemma42_comparison hCp (mul_pos hKp (sq_pos_of_pos hBp)) hb₀ hb₁
    mpos hnr ppos compare'
  change (M:ℝ) ≤ A*((n:ℝ)^(3/4:ℝ)*(p:ℝ)^(1/2:ℝ)+(n:ℝ)^(2-2*β)*(p:ℝ)^β) at mass
  have term₁ : (n : ℝ)^(3/4 : ℝ)*(p : ℝ)^(1/2 : ℝ) ≤ F :=
    (le_max_left _ _).trans (le_max_right _ _)
  have term₂ : (n : ℝ)^(2-2*β)*(p : ℝ)^β ≤ F :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have final : A*(2*F) ≤ (U+2*A)*F := by nlinarith only [mul_nonneg hU.le hF]
  exact mass.trans ((mul_le_mul_of_nonneg_left (show _ ≤ 2*F by linarith only [term₁, term₂]) hA.le).trans final)


/-- The Appendix B step on all acyclic full-bridge-free systems. Sparse cases
use the linear terms. In the dense case the verified splits supply the caps. -/
theorem lemma42_acyclic_update :
    ∃ R ≥ 1, ∀ {b B : ℝ}, 2/3 ≤ b → b ≤ 71/100 → 1 ≤ B →
      OfflineIncidenceBound.{u,v} b B →
      OfflineIncidenceBound.{u,v} (offlineExponentStep b) (R*B^(1/2:ℝ)) := by
  obtain ⟨R, hR, denseBound⟩ := offline_regular_step
  let K := 32+4*R
  refine ⟨K, by dsimp only [K]; linarith only [hR], ?_⟩
  intro b B hb₀ hb₁ hB prior
  let S := B^(1/2:ℝ)
  have hS : 1 ≤ S := by
    unfold S
    conv_lhs => rw [← Real.one_rpow (1/2:ℝ)]
    exact Real.rpow_le_rpow zero_le_one hB (by norm_num)
  have hRS : 0 ≤ R*S := mul_nonneg (zero_le_one.trans hR) (zero_le_one.trans hS)
  have hsmall : 32 ≤ K*S := by
    have hK : 32 ≤ K := by dsimp only [K]; linarith only [hR]
    exact hK.trans ((mul_one K).symm.le.trans
      (mul_le_mul_of_nonneg_left hS ((by norm_num : (0:ℝ) ≤ 32).trans hK)))
  let β := offlineExponentStep b
  have beta_pos : 0 ≤ β := by
    have : 0 < b := by linarith
    unfold β offlineExponentStep
    positivity
  have beta_le : β ≤ 1 := by
    change (2*b+1)/(2*b+2) ≤ (1 : ℝ)
    exact (div_le_iff₀ (by linarith)).mpr (by linarith)
  intro V I _ _ _ _ paths free
  let n := Fintype.card V
  let p := Fintype.card I
  let M := ∑ i, (paths i).card
  let F := offlineRate β (n:ℝ) (p:ℝ)
  have hNF : (n:ℝ) ≤ F := le_max_left _ _
  have hPF : (p:ℝ) ≤ F :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hF : 0 ≤ F := (Nat.cast_nonneg n).trans hNF
  have castMass : (∑ i, ((paths i).card : ℝ)) = M := by simp only [M, Nat.cast_sum]
  rw [castMass]
  change (M:ℝ) ≤ F*(K*S)
  have linCoeff := mul_le_mul_of_nonneg_right hsmall hF
  by_cases ndense : 32*n < M
  swap
  · have real : (M:ℝ) ≤ 32*n := by exact_mod_cast (le_of_not_gt ndense)
    nlinarith only [real, hNF, linCoeff]
  by_cases nlong : 16*p < M
  swap
  · have real : (M:ℝ) ≤ 16*p := by exact_mod_cast (le_of_not_gt nlong)
    nlinarith only [real, hPF, hF, linCoeff]
  have cap : M ≤ p*n := by
    calc
      _ ≤ ∑ _i : I, n := sum_le_sum (fun i _ => card_le_univ (paths i))
      _ = _ := by simp [p, mul_comm]
  have hn : 0 < n := Nat.pos_of_ne_zero (fun e => by rw [e, mul_zero] at cap; omega)
  have hp : 0 < p := Nat.pos_of_ne_zero (fun e => by rw [e, zero_mul] at cap; omega)
  let D := M/n+1
  let L := M/p+1
  let vertices := splitVertices paths D
  let after := splitPaths vertices L
  let n' := Fintype.card (VertexBlockIndex paths D)
  let p' := Fintype.card (BlockIndex vertices L)
  obtain ⟨ncap, pcap, sameMass, pathCaps, degreeCaps, degreeAvg, lengthAvg⟩ :=
    regularization_average_caps paths hn hp (by omega) (by omega)
  change n' ≤ 2*n at ncap
  change p' ≤ 2*p at pcap
  change (∑ i, (after i).card) = M at sameMass
  have hn' : 0 < n' := hn.trans_le (blockIndex_card_ge (occurrences paths) D)
  have hp' : 0 < p' := hp.trans_le (blockIndex_card_ge vertices L)
  have deg' : 16*n' < ∑ i, (after i).card := by rw [sameMass]; omega
  have len' : 8*p' < ∑ i, (after i).card := by rw [sameMass]; omega
  have capL : L*p' ≤ 4*∑ i, (after i).card := sameMass.symm ▸ lengthAvg
  have capD : D*n' ≤ 4*∑ i, (after i).card := sameMass.symm ▸ degreeAvg
  have stage := denseBound hb₀ hb₁ hB prior after (regularization_free free D L) L D hn' hp'
    (Nat.succ_pos _) (Nat.succ_pos _) deg' len' capL capD pathCaps degreeCaps
  rw [sameMass] at stage
  have size : offlineRate β (n':ℝ) (p':ℝ) ≤ 4*F :=
    (offlineRate_mono beta_pos beta_le (by positivity) (by positivity)
      (by exact_mod_cast ncap) (by exact_mod_cast pcap)).trans
      (offlineRate_double beta_pos beta_le (by positivity) (by positivity))
  exact stage.trans ((mul_le_mul_of_nonneg_left size hRS).trans (by
    dsimp only [K]
    nlinarith only [mul_nonneg (zero_le_one.trans hS) hF]))

set_option maxHeartbeats 500000 in
private theorem offline_incidence_initial : OfflineIncidenceBound.{u,v} (2/3) 16 := by
  intro V I _ _ _ _ paths free
  let n := Fintype.card V
  let p := Fintype.card I
  let M := ∑ i, (paths i).card
  let F := offlineRate (2/3) (n:ℝ) (p:ℝ)
  have hNF : (n:ℝ) ≤ F := le_max_left _ _
  have hPF : (p:ℝ) ≤ F :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have castMass : (∑ i, ((paths i).card : ℝ)) = M := by simp only [M, Nat.cast_sum]
  rw [castMass]
  change (M:ℝ) ≤ F*16
  rcases lemma27_acyclic paths free.halfFree with h | h | h
  · have hr : (M:ℝ) ≤ 16*n := by exact_mod_cast h
    linarith
  · have hr : (M:ℝ) ≤ 8*p := by exact_mod_cast h
    have hF : 0 ≤ F := (Nat.cast_nonneg p).trans hPF
    linarith
  · have hr : (M:ℝ)^3 ≤ 2048*((n:ℝ)*p)^2 := by exact_mod_cast h
    have hroot := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg M : (0:ℝ) ≤ M) 3) hr
        (show (0:ℝ) ≤ 1/3 by norm_num)
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg M) 3,
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2048) (by positivity),
      ← Real.rpow_natCast_mul (by positivity : 0 ≤ (n:ℝ)*p) 2,
      Real.mul_rpow (Nat.cast_nonneg n) (Nat.cast_nonneg p)] at hroot
    norm_num at hroot
    have c : (2048:ℝ)^(1/3:ℝ) ≤ 16 := by
      have t := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 2048)
        (by norm_num : (2048:ℝ) ≤ (16:ℝ)^3) (by norm_num : (0:ℝ) ≤ 1/3)
      rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 16) 3] at t
      norm_num at t
      exact t
    have hG : (n:ℝ)^(2/3:ℝ)*(p:ℝ)^(2/3:ℝ) ≤ F := by
      have ha : (n:ℝ)^(2-2*(2/3:ℝ))*(p:ℝ)^(2/3:ℝ) ≤ F :=
        (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
      norm_num at ha
      exact ha
    calc
      _ ≤ _ := hroot
      _ ≤ 16*((n:ℝ)^(2/3:ℝ)*(p:ℝ)^(2/3:ℝ)) := by grw [c]
      _ ≤ _ := (mul_le_mul_of_nonneg_left hG (by norm_num)).trans_eq (mul_comm _ _)

private theorem offline_limit_lt : 1 / Real.sqrt 2 < (71/100 : ℝ) := by
  have hpos := Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2)
  have eq : (1/Real.sqrt 2)^2=(1/2:ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  apply (sq_lt_sq₀ (by positivity) (by norm_num)).mp
  rw [eq]
  norm_num

/-- A single constant bounds every iterate in Theorem 43 for acyclic systems. -/
theorem theorem43_acyclic_iteration_uniform :
    ∃ B ≥ 1, ∀ k, OfflineIncidenceBound.{u,v} (offlineExponent k) B := by
  obtain ⟨R, hR, step⟩ := lemma42_acyclic_update
  let B := max 16 (R^2)
  have base : 16 ≤ B := le_max_left _ _
  have hB : 1 ≤ B := (by norm_num : (1:ℝ) ≤ 16).trans base
  have coeff := sqrt_coefficient hB (zero_le_one.trans hR) (le_max_right 16 (R^2))
  refine ⟨B, hB, ?_⟩
  intro k
  induction k with
  | zero =>
    intro V I _ _ _ _ paths free
    have h := offline_incidence_initial V I paths free
    exact h.trans (mul_le_mul_of_nonneg_left base ((Nat.cast_nonneg _).trans (le_max_left _ _)))
  | succ k ih =>
    have bounds := theorem43_exponent_limit.2.1 k
    have h := step bounds.1 (bounds.2.trans offline_limit_lt).le hB ih
    have eq : offlineExponent (k+1) = offlineExponentStep (offlineExponent k) :=
      Function.iterate_succ_apply' _ _ _
    rw [eq]
    intro V I _ _ _ _ paths free
    exact (h V I paths free).trans (mul_le_mul_of_nonneg_left coeff
      ((Nat.cast_nonneg _).trans (le_max_left _ _)))

theorem theorem43_acyclic_iteration (k : ℕ) :
    ∃ B > 0, OfflineIncidenceBound.{u,v} (offlineExponent k) B := by
  obtain ⟨B, hB, bound⟩ := theorem43_acyclic_iteration_uniform
  exact ⟨B, zero_lt_one.trans_le hB, bound k⟩


open Filter
open scoped Topology

/-- The limiting Appendix B bound for acyclic full-bridge-free path systems.
The single constant in the iteration permits taking the limit at fixed sizes. -/
theorem theorem43_acyclic_limit :
    ∃ B ≥ 1, OfflineIncidenceBound.{u,v} (1/Real.sqrt 2) B := by
  obtain ⟨B, hB, all⟩ := theorem43_acyclic_iteration_uniform
  refine ⟨B, hB, ?_⟩
  intro V I _ _ _ _ paths free
  let n : ℝ := Fintype.card V
  let p : ℝ := Fintype.card I
  let α := 1/Real.sqrt 2
  let m : ℝ := ∑ i, ((paths i).card:ℝ)
  change m ≤ offlineRate α n p * B
  have zero_le_bound : 0 ≤ offlineRate α n p * B :=
    mul_nonneg ((Nat.cast_nonneg _).trans (le_max_left _ _)) (zero_le_one.trans hB)
  have mass : m ≤ p*n := calc
    _ ≤ ∑ _i : I, n := sum_le_sum fun i _ => Nat.cast_le.mpr (card_le_univ (paths i))
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul, p]
  by_cases hn : 0 < Fintype.card V
  swap
  · have nz : n = 0 := by
      change (Fintype.card V:ℝ)=0
      exact_mod_cast (Nat.eq_zero_of_not_pos hn)
    rw [nz, mul_zero] at mass
    exact mass.trans zero_le_bound
  by_cases hp : 0 < Fintype.card I
  swap
  · have pz : p = 0 := by
      change (Fintype.card I:ℝ)=0
      exact_mod_cast (Nat.eq_zero_of_not_pos hp)
    rw [pz, zero_mul] at mass
    exact mass.trans zero_le_bound
  have hnr : 0 < n := Nat.cast_pos.mpr hn
  have hpr : 0 < p := Nat.cast_pos.mpr hp
  have continuous : Continuous (fun x : ℝ => offlineRate x n p * B) := by
    unfold offlineRate
    simp only [Real.rpow_def_of_pos hnr, Real.rpow_def_of_pos hpr]
    fun_prop
  have limit : Tendsto (fun k => offlineRate (offlineExponent k) n p * B) atTop
      (𝓝 (offlineRate α n p * B)) :=
    continuous.continuousAt.tendsto.comp theorem43_exponent_limit.2.2
  exact ge_of_tendsto' limit (fun k => all k V I paths free)

end OnlineReachabilityPreservers
