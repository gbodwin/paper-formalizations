import OnlineReachabilityPreservers.LocalOffBaseMoment
import OnlineReachabilityPreservers.OffBaseAverage

/-! The off-base expectation in Appendix A with local path orders. -/

namespace OnlineReachabilityPreservers

open Finset

/-- The off-base average bounded using the uniform degree and length caps. -/
theorem lemma34_list_off_base_cap_expectation {C a b : ℝ} (hC : 1 ≤ C) (ha₀ : 7/10 ≤ a)
    (ha₁ : a < 3/4) (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 3/4) :
    ∃ A > 0, ∀ {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype V] [Fintype I]
      {paths : I → List V}, (∀ i, (paths i).Nodup) →
      (∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y) →
      ∀ (L D h : ℕ),
      0 < Fintype.card I → 0 < h → h ≤ L → h ≤ D →
      Fintype.card V*D ≤ 4*Fintype.card I*L →
      (∀ i, (paths i).length ≤ L) →
      (∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ D) → ListInducedSizeBound paths C a b →
      let ℓ : ℝ := L
      let d : ℝ := D
      let u : ℝ := h
      uniformMean (fun base => ((listOffBaseBranchTuples paths base h).card:ℝ)) ≤
        A*(ℓ^2*d*u^(1/b) +
          ℓ^(3/2:ℝ)*d^(3/2+(3-4*a)/(2-2*a))*u^((2*b+1)/(2*b)) +
          ℓ^(1/b)*d^2*u^((4*b-2*b^2-1)/b^2)) := by
  obtain ⟨K, hK, bound⟩ := lemma34_off_base_cap_from_moments hC ha₀ ha₁ hb₀ hb₁
  refine ⟨K, hK, ?_⟩
  intro V I _ _ _ _ paths simple unique L D h hp hh hL hD ratio lengths degree prior
  let P (j : ℕ) (i : I) := (listDegreeBucket paths i h j).card
  let R (j : ℕ) := uniformMean (fun base => ∑ i, (((paths i).toFinset ∩ listDegreeBucket paths base h j).card:ℝ)^2)
  let Q := uniformMean (fun base => ((listOffBaseBranchTuples paths base h).card:ℝ))
  refine bound (Fintype.card V) L D h hp hh hL hD ratio P R Q
    (div_nonneg (sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    (fun j i => listDegreeBucket_size_cap paths i h j L D (by
      rw [List.toFinset_card_of_nodup (simple i)]
      exact lengths i) degree) ?_ ?_ ?_
  · intro j big
    exact lemma34_list_mean_bucket_size simple unique h j D hp (zero_lt_one.trans_le hC) big
      (by linarith) (by linarith) degree prior
  · intro j
    simpa only [R, P, Real.rpow_one] using
      lemma34_list_mean_bucket_moment simple h j L D (hh.trans_le hL) (hh.trans_le hD)
        (zero_lt_one.trans_le hC) (show 1/2 ≤ a by linarith) ha₁ (show 1/2 < b by linarith)
        (show b ≤ 1 by linarith) lengths degree prior
  · exact lemma34_list_minkowski_mean unique h D hp degree

/-- The off-base estimate in terms of the actual incidence averages. -/
theorem lemma34_list_off_base_expectation {C a b : ℝ} (hC : 1 ≤ C) (ha₀ : 7/10 ≤ a)
    (ha₁ : a < 3/4) (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 3/4) :
    ∃ A > 0, ∀ {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype V] [Fintype I]
      {paths : I → List V}, (∀ i, (paths i).Nodup) →
      (∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y) →
      ∀ (L D h : ℕ),
      0 < Fintype.card V → 0 < Fintype.card I → 0 < h → h ≤ L → h ≤ D →
      (∀ i, (paths i).length ≤ L) →
      (∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ D) → ListInducedSizeBound paths C a b →
      let n := Fintype.card V
      let p := Fintype.card I
      let M := ∑ i, (paths i).length
      0 < M → L*p ≤ 4*M → D*n ≤ 4*M →
      let ℓ : ℝ := (M:ℝ)/p
      let d : ℝ := (M:ℝ)/n
      let u : ℝ := h
      uniformMean (fun base => ((listOffBaseBranchTuples paths base h).card:ℝ)) ≤
        A*(ℓ^2*d*u^(1/b) +
          ℓ^(3/2:ℝ)*d^(3/2+(3-4*a)/(2-2*a))*u^((2*b+1)/(2*b)) +
          ℓ^(1/b)*d^2*u^((4*b-2*b^2-1)/b^2)) := by
  obtain ⟨K, hK, bound⟩ := lemma34_list_off_base_cap_expectation hC ha₀ ha₁ hb₀ hb₁
  refine ⟨256*K, by positivity, ?_⟩
  intro V I _ _ _ _ paths simple unique L D h hn hp hh hL hD length degree input
  dsimp only
  let n := Fintype.card V
  let p := Fintype.card I
  let M := ∑ i, (paths i).length
  intro hm Lcap Dcap
  have ratio : n*D ≤ 4*p*L := calc
    _ ≤ 4*M := (Nat.mul_comm n D).le.trans Dcap
    _ ≤ 4*(p*L) := Nat.mul_le_mul_left _ (by
      calc
        M ≤ ∑ _ : I, L := sum_le_sum (fun i _ => length i)
        _ = _ := by simp [p])
    _ = _ := by ring
  exact lemma34_off_base_average_from_caps ha₀ ha₁ hb₀ hK.le hn hp hm Lcap Dcap
    (bound simple unique L D h hp hh hL hD ratio length degree input)

end OnlineReachabilityPreservers
