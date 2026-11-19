import OnlineReachabilityPreservers.LocalFullOnBaseCounting
import OnlineReachabilityPreservers.LocalOffBaseAverage
import OnlineReachabilityPreservers.LocalOnBaseAverage

/-! The full branching expectation in Appendix A with local path orders. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

/-- Lemma 35's on-base sum for all the on-base tuples in the sampled subsystem. -/
theorem lemma35_list_full_on_base_sum {C a b : ℝ} (hC : 1 ≤ C)
    (ha₀ : 2/3 ≤ a) (ha₁ : a ≤ 3/4) (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 3/4) :
    ∃ A > 0, ∀ {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype V] [Fintype I]
      {paths : I → List V}, (∀ i, (paths i).Nodup) → HalfBridgeFree (ListBefore paths) 4 →
      (∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y) →
      ∀ (L D h : ℕ), 0 < h → h ≤ L → h ≤ D →
      (∀ i, (paths i).length ≤ L) →
      (∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ D) → ListInducedSizeBound paths C a b →
      let ℓ : ℝ := L
      let d : ℝ := D
      let t : ℝ := h
      ℓ*(∑ base, ((listFullOnBaseBranchTuples paths base h).card:ℝ)) ≤
        A*(Fintype.card V:ℝ)*d*(ℓ^2*d^2+ℓ^(3/2:ℝ)*d^2*t^(5/4:ℝ)) := by
  obtain ⟨K, hK, coarse⟩ := lemma35_list_large_bases_coarse hC ha₀ ha₁ hb₀ hb₁
  obtain ⟨G, hG, combine⟩ := lemma35_on_base_sum_from_buckets
  refine ⟨2*(12*Real.sqrt K*G), by positivity, ?_⟩
  intro V I _ _ _ _ paths simple free unique L D h hh hL hD lengths degrees input
  let M (u : V) (j : ℕ) : ℝ :=
    ((listImportantBaseIncidences paths u h (2^j) : ℝ)+(listBackwardBaseIncidences paths u h (2^j) : ℝ))/2
  let P (u : V) (j : ℕ) : ℝ := (listLargeBranchBases paths u h (2^j)).card
  let Q := ∑ base, ((listFullOnBaseBranchTuples paths base h).card:ℝ)
  have upper := combine L D h hh hL hD hK (Q := Q/2) M P (fun _ _ => by dsimp only [M]; positivity)
  have scaled := upper ?_ ?_ ?_
  · have result := mul_le_mul_of_nonneg_left scaled (by norm_num : (0 : ℝ) ≤ 2)
    convert result using 1 <;> ring
  · intro j u
    let S : ℝ := (listPredecessorSupport paths u h).card
    let N : ℝ := (listPredecessorSupport paths u h ∪ listSuccessorSupport paths u).card
    have len (i : I) : (paths i).toFinset.card ≤ L := by
      rw [List.toFinset_card_of_nodup (simple i)]
      exact lengths i
    have near := (listPredecessorSupport_card paths u h).trans (Nat.mul_le_mul_right h (degrees u))
    have hS : S ≤ (D:ℝ)*h := by
      change ((listPredecessorSupport paths u h).card:ℝ) ≤ (D:ℝ)*h
      exact_mod_cast near
    have hN : N ≤ 2*(L:ℝ)*D := by
      change ((listPredecessorSupport paths u h ∪ listSuccessorSupport paths u).card:ℝ) ≤ 2*(L:ℝ)*D
      have nCap : (listPredecessorSupport paths u h ∪ listSuccessorSupport paths u).card ≤ 2*L*D := calc
        _ ≤ (listPredecessorSupport paths u h).card + (listSuccessorSupport paths u).card :=
          card_union_le _ _
        _ ≤ D*h+D*L := Nat.add_le_add near
          ((listSuccessorSupport_card paths u L len).trans (Nat.mul_le_mul_right L (degrees u)))
        _ ≤ D*L+D*L := Nat.add_le_add_right (Nat.mul_le_mul_left D hL) _
        _ = _ := by ring
      exact_mod_cast nCap
    have upper₁ := lemma35_list_important_upper simple free unique u h (2^j) (Nat.pow_pos (by decide))
    have upper₂ := lemma35_list_backward_upper free unique u h (2^j) (Nat.pow_pos (by decide))
    have mark : M u j ≤ N+Real.sqrt (2*N*(P u j*S)) := by
      dsimp only [M, N, P, S] at *
      linarith only [upper₁, upper₂]
    exact lemma35_important_from_caps (Nat.cast_nonneg L) (Nat.cast_nonneg D) (Nat.cast_nonneg h)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hS hN mark
  · intro j u
    simpa only [P, Nat.cast_pow, Nat.cast_ofNat] using coarse simple u D h (2^j)
      (listLargeBranchBases paths u h (2^j)) (hh.trans_le hD) hh (Nat.pow_pos (by decide))
      (fun _ hi => (mem_filter.mp hi).2.2) degrees input
  · let J := range (Nat.log 2 D+1)
    let B (u : V) (j : ℕ) : ℝ :=
      (listImportantBaseIncidences paths u h (2^j):ℝ)+(listBackwardBaseIncidences paths u h (2^j):ℝ)
    have raw : Q ≤ ∑ j ∈ J, (2*(2:ℝ)^j*((D:ℝ)+h+1))*∑ u, B u j := by
      dsimp only [Q, J, B]
      exact_mod_cast lemma35_list_full_on_base_dyadic_count unique h D degrees
    calc
      _ ≤ (∑ j ∈ J, (2*(2:ℝ)^j*((D:ℝ)+h+1))*∑ u, B u j)/2 :=
        div_le_div_of_nonneg_right raw (by norm_num)
      _ = _ := by
        rw [sum_div]
        apply sum_congr rfl
        intro j _
        rw [mul_div_assoc, sum_div]

/-- Uniformly averaging the full on-base tuples incurs no logarithmic loss. -/
theorem lemma35_list_full_on_base_expectation {C a b : ℝ} (hC : 1 ≤ C)
    (ha₀ : 2/3 ≤ a) (ha₁ : a ≤ 3/4) (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 3/4) :
    ∃ A > 0, ∀ {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype V] [Fintype I]
      {paths : I → List V}, (∀ i, (paths i).Nodup) → HalfBridgeFree (ListBefore paths) 4 →
      (∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y) →
      ∀ (L D h : ℕ), 0 < Fintype.card V → 0 < Fintype.card I → 0 < h → h ≤ L → h ≤ D →
      (∀ i, (paths i).length ≤ L) →
      (∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ D) → ListInducedSizeBound paths C a b →
      let n := Fintype.card V
      let p := Fintype.card I
      let M := ∑ i, (paths i).length
      0 < M → L*p ≤ 4*M → D*n ≤ 4*M →
      let ℓ : ℝ := (M:ℝ)/p
      let d : ℝ := (M:ℝ)/n
      (∑ base, ((listFullOnBaseBranchTuples paths base h).card:ℝ))/(p:ℝ) ≤
        A*(ℓ^2*d^2+ℓ^(3/2:ℝ)*d^2*(h:ℝ)^(5/4:ℝ)) := by
  obtain ⟨K, hK, bound⟩ := lemma35_list_full_on_base_sum hC ha₀ ha₁ hb₀ hb₁
  refine ⟨1024*K, by positivity, ?_⟩
  intro V I _ _ _ _ paths simple free unique L D h hn hp hh hL hD length degree input
  dsimp only
  intro hM capL capD
  apply lemma35_on_base_average_from_sum hK.le hn hp hM (hh.trans_le hL) capL capD
  · calc
      _ ≤ ∑ _ : I, L := sum_le_sum (fun i _ => length i)
      _ = _ := by simp [mul_comm]
  · exact bound simple free unique L D h hh hL hD length degree input

/-- The complete upper count of Lemma 36 in local path orders. The two
coefficients keep the linear on-base contribution available for absorption. -/
theorem lemma36_list_expectation {C a b : ℝ} (hC : 1 ≤ C) (ha₀ : 7/10 ≤ a)
    (ha₁ : a < 3/4) (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 3/4) :
    ∃ A > 0, ∃ B > 0, ∀ {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype V] [Fintype I]
      {paths : I → List V}, (∀ i, (paths i).Nodup) → HalfBridgeFree (ListBefore paths) 4 →
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
      uniformMean (fun base => ((fullListBranchTuples paths base h).card:ℝ)) ≤
        A*(ℓ^2*d*u^(1/b) +
          ℓ^(3/2:ℝ)*d^(3/2+(3-4*a)/(2-2*a))*u^((2*b+1)/(2*b)) +
          ℓ^(1/b)*d^2*u^((4*b-2*b^2-1)/b^2)) + B*(ℓ^2*d^2+ℓ^(3/2:ℝ)*d^2*u^(5/4:ℝ)) := by
  obtain ⟨A, hA, off⟩ := lemma34_list_off_base_expectation hC ha₀ ha₁ hb₀ hb₁
  obtain ⟨B, hB, on⟩ := lemma35_list_full_on_base_expectation hC
    (show 2/3 ≤ a by linarith) ha₁.le hb₀ hb₁
  refine ⟨A,hA,B,hB,?_⟩
  intro V I _ _ _ _ paths simple free unique L D h hn hp hh hL hD lengths degree input
  dsimp only
  intro hM Lcap Dcap
  let offMean := uniformMean (fun base => ((listOffBaseBranchTuples paths base h).card:ℝ))
  let onMean := uniformMean (fun base => ((listFullOnBaseBranchTuples paths base h).card:ℝ))
  have eq : uniformMean (fun base => ((fullListBranchTuples paths base h).card:ℝ)) = offMean+onMean := by
    dsimp only [offMean,onMean,uniformMean]
    simp_rw [fullListBranchTuples_partition, Nat.cast_add, sum_add_distrib, add_div]
    ring
  rw [eq]
  exact add_le_add
    (off simple unique L D h hn hp hh hL hD lengths degree input hM Lcap Dcap)
    (on simple free unique L D h hn hp hh hL hD lengths degree input hM Lcap Dcap)

end OnlineReachabilityPreservers
