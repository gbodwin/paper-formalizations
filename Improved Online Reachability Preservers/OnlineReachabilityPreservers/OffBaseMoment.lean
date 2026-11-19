import OnlineReachabilityPreservers.BranchingDegrees

/-! Expected moments of the actual Appendix A dyadic samples. -/

namespace OnlineReachabilityPreservers

open Finset

/-- The mean of a real-valued statistic under the uniform choice of path. -/
noncomputable def uniformMean {I : Type*} [Fintype I] (f : I → ℝ) : ℝ :=
  (∑ i, f i)/(Fintype.card I:ℝ)

private theorem uniformMean_mono {I : Type*} [Fintype I] {f g : I → ℝ}
    (pointwise : ∀ i, f i ≤ g i) : uniformMean f ≤ uniformMean g :=
  div_le_div_of_nonneg_right (sum_le_sum (fun i _ => pointwise i)) (Nat.cast_nonneg _)

private theorem uniformMean_add {I : Type*} [Fintype I] (f g : I → ℝ) :
    uniformMean (fun i => f i+g i) = uniformMean f+uniformMean g := by
  simp only [uniformMean, sum_add_distrib, add_div]

private theorem uniformMean_mul {I : Type*} [Fintype I] (f : I → ℝ) (C : ℝ) :
    uniformMean (fun i => C*f i) = C*uniformMean f := by
  simp only [uniformMean, ← mul_sum, mul_div_assoc]

private theorem uniformMean_const {I : Type*} [Fintype I] (hp : 0 < Fintype.card I) (C : ℝ) :
    uniformMean (fun _ : I => C) = C := by
  simp only [uniformMean, sum_const, card_univ, nsmul_eq_mul, mul_comm]
  exact mul_div_cancel_right₀ _ (Nat.cast_pos.mpr hp).ne'

/-- Bound higher sample-size moments using the deterministic cap and the mean. -/
theorem uniformMean_power_bound {I : Type*} [Fintype I] {f : I → ℝ} {T r : ℝ}
    (hr : 1 ≤ r) (nonneg : ∀ i, 0 ≤ f i) (cap : ∀ i, f i ≤ T) :
    uniformMean (fun i => (f i)^r) ≤ T^(r-1)*uniformMean f := by
  rw [← uniformMean_mul]
  apply uniformMean_mono
  intro i
  rcases (nonneg i).eq_or_lt with hz | hpos
  · rw [← hz, mul_zero, Real.zero_rpow (by linarith)]
  calc
    _ = (f i)^(r-1)*(f i)^(1:ℝ) := by rw [← Real.rpow_add hpos, sub_add_cancel]
    _ = (f i)^(r-1)*f i := by rw [Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (nonneg i) (cap i) (sub_nonneg.mpr hr)) (nonneg i)

theorem uniformMean_power_le_cap {I : Type*} [Fintype I] {f : I → ℝ} {T r : ℝ}
    (hp : 0 < Fintype.card I) (hr : 0 ≤ r) (nonneg : ∀ i, 0 ≤ f i) (cap : ∀ i, f i ≤ T) :
    uniformMean (fun i => (f i)^r) ≤ T^r :=
  (uniformMean_mono (fun i => Real.rpow_le_rpow (nonneg i) (cap i) hr)).trans_eq
    (uniformMean_const hp _)

variable {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype V] [Fintype I]

/-- The refined Lemma 34 inequality in terms of uniform means over bases. -/
theorem lemma34_minkowski_mean {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (h D : ℕ) (hp : 0 < Fintype.card I) (degree : ∀ v, (occurrences paths v).card ≤ D) :
    Real.sqrt (uniformMean fun base => ((offBaseBranchTuples paths base h).card:ℝ)) ≤
      2*∑ j ∈ range (Nat.log 2 D+1), (2:ℝ)^j *
        Real.sqrt (uniformMean fun base => ∑ i, ((paths i ∩ degreeBucket paths base h j).card:ℝ)^2) := by
  let P : ℝ := Fintype.card I
  have hP : 0 < P := Nat.cast_pos.mpr hp
  let S (j : ℕ) := ∑ base : I, ∑ i, ((paths i ∩ degreeBucket paths base h j).card:ℝ)^2
  let Q := ∑ base : I, ((offBaseBranchTuples paths base h).card:ℝ)
  let J := range (Nat.log 2 D+1)
  have qPos : 0 ≤ Q := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have sPos (j : ℕ) : 0 ≤ S j := sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _))
  have bound : Real.sqrt Q ≤ 2*∑ j ∈ J, (2:ℝ)^j*Real.sqrt (S j) :=
    lemma34_minkowski free h D degree
  have k := div_le_div_of_nonneg_right bound (Real.sqrt_pos.mpr hP).le
  change Real.sqrt (Q/P) ≤ 2*∑ j ∈ J, (2:ℝ)^j*Real.sqrt (S j/P)
  calc
    _ = Real.sqrt Q/Real.sqrt P := Real.sqrt_div qPos _
    _ ≤ _ := k
    _ = _ := by
      rw [mul_div_assoc, sum_div]
      congr 1
      apply sum_congr rfl
      intro j _
      rw [Real.sqrt_div (sPos j), mul_div_assoc]

omit [LinearOrder I] in
/-- Deterministic cap on each actual off-base dyadic bucket. -/
theorem degreeBucket_size_cap (paths : I → Finset V) (base : I) (h j L D : ℕ)
    (length : (paths base).card ≤ L) (degree : ∀ v, (occurrences paths v).card ≤ D) :
    (degreeBucket paths base h j).card * 2^j ≤ L*D*(h+1) := calc
  _ ≤ (largeBranchVertices paths base h (2^j)).card * 2^j :=
    Nat.mul_le_mul_right _ (card_le_card (degreeBucket_subset_large paths base h j))
  _ ≤ ∑ u ∈ paths base, (occurrences paths u).card*(h+1) :=
    lemma33_deterministic paths base h (2^j)
  _ ≤ ∑ _ ∈ paths base, D*(h+1) := sum_le_sum fun u _ => Nat.mul_le_mul_right _ (degree u)
  _ = (paths base).card * D * (h+1) := by simp [mul_assoc]
  _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ length)

/-- The moment estimate for each off-base bucket, averaged over actual bases. -/
theorem lemma34_mean_bucket_moment {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (h j L D : ℕ) (hL : 0 < L) (hD : 0 < D) {C a b : ℝ}
    (hC : 0 < C) (ha₀ : 1/2 ≤ a) (ha₁ : a < 3/4) (hb₀ : 1/2 < b) (hb₁ : b ≤ 1)
    (length : ∀ i, (paths i).card ≤ L)
    (degree : ∀ v, (occurrences paths v).card ≤ D) (input : InducedSizeBound paths C a b) :
    let n (base : I) : ℝ := (degreeBucket paths base h j).card
    let d : ℝ := D
    uniformMean (fun base => ∑ i, ((paths i ∩ degreeBucket paths base h j).card:ℝ)^2) ≤
      (2*C*((L:ℝ)+d))*uniformMean n +
      ((1/(3-4*a)+1)*C^(1/(2-2*a))*d^((3-4*a)/(2-2*a)))*
        uniformMean (fun base => (n base)^(3/2:ℝ)) +
      ((1/(2*b-1)+1)*C^(1/b)*d^((2*b-1)/b))*
        uniformMean (fun base => (n base)^(1/b)) := by
  dsimp only
  let N (base : I) : ℝ := (degreeBucket paths base h j).card
  let d : ℝ := D
  let t₁ := 2*C*((L:ℝ)+d)
  let t₂ := (1/(3-4*a)+1)*C^(1/(2-2*a))*d^((3-4*a)/(2-2*a))
  let t₃ := (1/(2*b-1)+1)*C^(1/b)*d^((2*b-1)/b)
  have hb : 0 < b := by linarith
  change _ ≤ t₁*uniformMean N +
    t₂*uniformMean (fun base => (N base)^(3/2:ℝ)) +
    t₃*uniformMean (fun base => (N base)^(1/b))
  simp only [← uniformMean_mul, ← uniformMean_add]
  apply uniformMean_mono
  intro base
  let S := degreeBucket paths base h j
  change (∑ i, ((paths i ∩ S).card:ℝ)^2) ≤
    t₁*(S.card:ℝ)+t₂*(S.card:ℝ)^(3/2:ℝ)+t₃*(S.card:ℝ)^(1/b)
  by_cases he : S = ∅
  · simp [he, Real.zero_rpow (inv_ne_zero hb.ne')]
  have hs : 0 < S.card := card_pos.mpr (nonempty_iff_ne_empty.mpr he)
  have upper := sampled_vertex_moment free S hs D hD (show (0:ℝ) < L from Nat.cast_pos.mpr hL)
    hC ha₀ ha₁ hb₀ hb₁ (fun i => Nat.cast_le.mpr (length i)) (fun u _ => degree u) input
  exact upper.trans_eq (by dsimp only [t₁,t₂,t₃,d]; ring)

/-- The first moment of each actual bucket is at most the predecessor-tail
envelope from Lemma 33 when the threshold exceeds its coefficient. -/
theorem lemma34_mean_bucket_size {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (h j D : ℕ) (hp : 0 < Fintype.card I) {C a b : ℝ}
    (hC : 0 < C) (hsmall : C < (2:ℝ)^j) (ha : 1/2 < a) (hb : b < 1)
    (degree : ∀ v, (occurrences paths v).card ≤ D) (input : InducedSizeBound paths C a b) :
    let y : ℝ := (D:ℝ)*h
    let x : ℝ := (2:ℝ)^j
    uniformMean (fun base => ((degreeBucket paths base h j).card:ℝ)) ≤
      (Fintype.card V:ℝ)*(C*y/x+(C*y^a/x)^(1/(2*a-1))+
        (C*y^(2-2*b)/x)^(1/(1-b)))/(Fintype.card I:ℝ) := by
  have threshold : C < ((2^j:ℕ):ℝ) := by exact_mod_cast hsmall
  have norm := lemma33_expected_count free D h (2^j) hp hC threshold ha hb degree input
  apply le_trans _ (by simpa only [uniformMean, Nat.cast_pow, Nat.cast_ofNat] using norm)
  apply uniformMean_mono
  intro base
  exact Nat.cast_le.mpr (card_le_card (degreeBucket_subset_large paths base h j))

end OnlineReachabilityPreservers
