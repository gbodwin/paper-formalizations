import OnlineReachabilityPreservers.LocalBranchingDegrees
import OnlineReachabilityPreservers.OffBaseMoment

/-! The moments of actual off-base vertex samples in local path orders. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype I]

/-- Restrict every path to a nonempty vertex sample and apply Lemma 31. -/
theorem lemma31_list_sampled_moment {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (S : Finset V) (hS : 0 < S.card) (D : ℕ) (hD : 0 < D) {L C a b : ℝ}
    (hL : 0 < L) (hC : 0 < C) (ha₀ : 1/2 ≤ a) (ha₁ : a < 3/4) (hb₀ : 1/2 < b) (hb₁ : b ≤ 1)
    (cap : ∀ i, ((paths i).length : ℝ) ≤ L)
    (degree : ∀ u ∈ S, (occurrences (fun i => (paths i).toFinset) u).card ≤ D)
    (input : ListInducedSizeBound paths C a b) :
    let n : ℝ := S.card
    let d : ℝ := D
    (∑ i, (((paths i).toFinset ∩ S).card : ℝ)^2) ≤
      2*C*n*(L+d) +
      (1/(3-4*a)+1)*C^(1/(2-2*a))*n^(3/2 : ℝ)*d^((3-4*a)/(2-2*a)) +
      (1/(2*b-1)+1)*C^(1/b)*n^(1/b)*d^((2*b-1)/b) := by
  let marks (i : I) := (paths i).toFinset
  let sample (i : I) := marks i ∩ S
  have lengths (i : I) : ((sample i).card : ℝ) ≤ L := by
    have smaller : (sample i).card ≤ (marks i).card :=
      card_le_card (inter_subset_left : marks i ∩ S ⊆ marks i)
    have whole : (marks i).card = (paths i).length := List.toFinset_card_of_nodup (simple i)
    exact (Nat.cast_le.mpr (smaller.trans_eq whole)).trans (cap i)
  have mass : (∑ i, ((sample i).card:ℝ)) ≤ (S.card:ℝ)*D := by
    have bound := inducedPath_mass_le marks S D degree
    simp only [inducedPath_card] at bound
    exact_mod_cast bound
  apply lemma31_moment_from_subfamily sample (Nat.cast_pos.mpr hS) (Nat.cast_pos.mpr hD)
    hL hC ha₀ ha₁ hb₀ hb₁ lengths mass
  intro J
  have eq : (∑ i : J, ((restrictListPaths paths S J i).length : ℝ)) =
      ∑ i ∈ J, ((sample i).card : ℝ) := by
    rw [← J.sum_coe_sort (fun i => ((sample i).card:ℝ))]
    apply sum_congr rfl
    intro i _
    change ((restrictListPath (paths i.val) S).length : ℝ) = ((sample i.val).card : ℝ)
    rw [restrictListPath_length (simple i.val)]
  rw [← eq]
  exact input S J

variable [Fintype V]

/-- The vertices outside the base with positive branching weight in dyadic bucket `j`. -/
noncomputable def listDegreeBucket (paths : I → List V) (b : I) (h j : ℕ) : Finset V :=
  weightedDegreeBucket (paths b).toFinset (fun v => (listBranchesThrough paths b h v).card) j

omit [LinearOrder I] in
theorem listDegreeBucket_subset_large (paths : I → List V) (b : I) (h j : ℕ) :
    listDegreeBucket paths b h j ⊆ listLargeBranchVertices paths b h (2^j) := by
  intro v hv
  obtain ⟨hb, hp, hl⟩ := mem_filter.mp hv
  have hpow := Nat.pow_log_le_self 2 hp.ne'
  rw [hl] at hpow
  exact mem_filter.mpr ⟨mem_univ _, fun h => (mem_sdiff.mp hb).2 (List.mem_toFinset.mpr h), hpow⟩

theorem lemma34_list_minkowski_mean {paths : I → List V}
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (h D : ℕ) (hp : 0 < Fintype.card I) (degree : ∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ D) :
    Real.sqrt (uniformMean fun base => ((listOffBaseBranchTuples paths base h).card:ℝ)) ≤
      2*∑ j ∈ range (Nat.log 2 D+1), (2:ℝ)^j *
        Real.sqrt (uniformMean fun base => ∑ i, (((paths i).toFinset ∩ listDegreeBucket paths base h j).card:ℝ)^2) := by
  exact lemma34_minkowski_mean_from_weights (fun i => (paths i).toFinset)
    (fun b v => (listBranchesThrough paths b h v).card) (fun b => (listOffBaseBranchTuples paths b h).card)
    D hp (fun _ v outside => (listBranchesThrough_le_degree unique (fun h => outside (List.mem_toFinset.mpr h))).trans (degree v))
    (lemma34_list_weighted_path_bound paths · h)

theorem listDegreeBucket_size_cap (paths : I → List V) (base : I) (h j L D : ℕ)
    (length : (paths base).toFinset.card ≤ L)
    (degree : ∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ D) :
    (listDegreeBucket paths base h j).card * 2^j ≤ L*D*(h+1) := calc
  _ ≤ (listLargeBranchVertices paths base h (2^j)).card * 2^j :=
    Nat.mul_le_mul_right _ (card_le_card (listDegreeBucket_subset_large paths base h j))
  _ ≤ ∑ u ∈ (paths base).toFinset, (occurrences (fun i => (paths i).toFinset) u).card*(h+1) :=
    lemma33_list_deterministic paths base h (2^j)
  _ ≤ ∑ _ ∈ (paths base).toFinset, D*(h+1) := sum_le_sum fun u _ => Nat.mul_le_mul_right _ (degree u)
  _ = (paths base).toFinset.card * D * (h+1) := by simp [mul_assoc]
  _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ length)

theorem lemma34_list_mean_bucket_moment {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (h j L D : ℕ) (hL : 0 < L) (hD : 0 < D) {C a b : ℝ}
    (hC : 0 < C) (ha₀ : 1/2 ≤ a) (ha₁ : a < 3/4) (hb₀ : 1/2 < b) (hb₁ : b ≤ 1)
    (length : ∀ i, (paths i).length ≤ L)
    (degree : ∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ D)
    (input : ListInducedSizeBound paths C a b) :
    let n (base : I) : ℝ := (listDegreeBucket paths base h j).card
    let d : ℝ := D
    uniformMean (fun base => ∑ i, (((paths i).toFinset ∩ listDegreeBucket paths base h j).card:ℝ)^2) ≤
      (2*C*((L:ℝ)+d))*uniformMean n +
      ((1/(3-4*a)+1)*C^(1/(2-2*a))*d^((3-4*a)/(2-2*a)))*
        uniformMean (fun base => (n base)^(3/2:ℝ)) +
      ((1/(2*b-1)+1)*C^(1/b)*d^((2*b-1)/b))*
        uniformMean (fun base => (n base)^(1/b)) := by
  apply lemma34_mean_bucket_moment_from_samples (fun i => (paths i).toFinset)
    (fun base => listDegreeBucket paths base h j) (show 0 < b by linarith)
  intro S hs
  exact lemma31_list_sampled_moment simple S hs D hD (Nat.cast_pos.mpr hL)
    hC ha₀ ha₁ hb₀ hb₁ (fun i => Nat.cast_le.mpr (length i)) (fun v _ => degree v) input

theorem lemma34_list_mean_bucket_size {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (h j D : ℕ) (hp : 0 < Fintype.card I) {C a b : ℝ}
    (hC : 0 < C) (hsmall : C < (2:ℝ)^j) (ha : 1/2 < a) (hb : b < 1)
    (degree : ∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ D)
    (input : ListInducedSizeBound paths C a b) :
    let y : ℝ := (D:ℝ)*h
    let x : ℝ := (2:ℝ)^j
    uniformMean (fun base => ((listDegreeBucket paths base h j).card:ℝ)) ≤
      (Fintype.card V:ℝ)*(C*y/x+(C*y^a/x)^(1/(2*a-1))+
        (C*y^(2-2*b)/x)^(1/(1-b)))/(Fintype.card I:ℝ) := by
  have threshold : C < ((2^j:ℕ):ℝ) := by exact_mod_cast hsmall
  have norm := lemma33_list_expected_count simple unique D h (2^j) hp hC threshold ha hb degree input
  apply le_trans _ (by simpa only [uniformMean, Nat.cast_pow, Nat.cast_ofNat] using norm)
  apply uniformMean_mono
  intro base
  exact Nat.cast_le.mpr (card_le_card (listDegreeBucket_subset_large paths base h j))

end OnlineReachabilityPreservers
