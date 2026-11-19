import OnlineReachabilityPreservers.LocalOnBaseCounting
import OnlineReachabilityPreservers.OnBaseAverage

/-! The on-base branching expectation in local path orders. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

/-- The coarse bound in Lemma 35, for any selection of long induced paths
in the predecessor subsystem of Lemma 32. -/
theorem lemma35_list_large_bases_coarse {C a b : ℝ} (hC : 1 ≤ C)
    (ha₀ : 2/3 ≤ a) (ha₁ : a ≤ 3/4) (hb₀ : 2/3 ≤ b) (hb₁ : b ≤ 3/4) :
    ∃ K ≥ 1, ∀ {V I : Type*} [LinearOrder V] [Fintype I] {paths : I → List V},
      (∀ i, (paths i).Nodup) → ∀ (u : V) (D h x : ℕ) (J : Finset I),
      0 < D → 0 < h → 0 < x →
      (∀ i ∈ J, x ≤ ((paths i).toFinset ∩ listPredecessorSupport paths u h).card) →
      (∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ D) → ListInducedSizeBound paths C a b →
      let y : ℝ := (D:ℝ)*h
      (J.card:ℝ) ≤ K*min (y/x+y^2/(x:ℝ)^3) ((D:ℝ)^2*h/x) := by
  obtain ⟨K, hK, coarse⟩ := lemma35_coarse_from_counts hC ha₀ ha₁ hb₀ hb₁
  refine ⟨K, hK, ?_⟩
  intro V I _ _ paths simple u D h x J hD hh hx long degree input
  let S := listPredecessorSupport paths u h
  let y : ℝ := (D:ℝ)*h
  have x1 : (1:ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x from hx)
  have xpos : (0:ℝ) < x := Nat.cast_pos.mpr hx
  have h1 : (1:ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h from hh)
  have dpos : (0:ℝ) < D := Nat.cast_pos.mpr hD
  have det : (J.card:ℝ) ≤ (D:ℝ)^2*h/x := by
    apply (le_div_iff₀ xpos).mpr
    have h := (lemma32_list_degree_count_subfamily paths u h x D J long degree).trans
      (Nat.mul_le_mul_right D (Nat.mul_le_mul_right h (degree u)))
    exact_mod_cast (h.trans_eq (by ring))
  apply coarse x1 dpos h1 det
  intro big
  have size : (S.card:ℝ) ≤ y := by
    have hs := (listPredecessorSupport_card paths u h).trans (Nat.mul_le_mul_right h (degree u))
    change (S.card:ℝ) ≤ (D:ℝ)*h
    exact_mod_cast hs
  have actual := lemma32_list_extremal_count_subfamily simple u h x J long (zero_lt_one.trans_le hC) big
    (by linarith only [ha₀]) (by linarith only [hb₁]) input
  have rnn : 0 ≤ 1/(2*a-1) := one_div_nonneg.mpr (by linarith only [ha₀])
  have snn : 0 ≤ 1/(1-b) := one_div_nonneg.mpr (by linarith only [hb₁])
  have enn : 0 ≤ 2-2*b := by linarith only [hb₁]
  refine actual.trans ?_
  change C*(S.card:ℝ)/x+(C*(S.card:ℝ)^a/x)^(1/(2*a-1))+
    (C*(S.card:ℝ)^(2-2*b)/x)^(1/(1-b)) ≤
    C*y/x+(C*y^a/x)^(1/(2*a-1))+(C*y^(2-2*b)/x)^(1/(1-b))
  gcongr

/-- Lemma 35's on-base sum for the tuple family used by the close-pair lower bound. -/
theorem lemma35_list_on_base_sum {C a b : ℝ} (hC : 1 ≤ C)
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
      ℓ*(∑ base, ((listOnBaseBranchTuples paths base h).card:ℝ)) ≤
        A*(Fintype.card V:ℝ)*d*(ℓ^2*d^2+ℓ^(3/2:ℝ)*d^2*t^(5/4:ℝ)) := by
  obtain ⟨K, hK, coarse⟩ := lemma35_list_large_bases_coarse hC ha₀ ha₁ hb₀ hb₁
  obtain ⟨G, hG, combine⟩ := lemma35_on_base_sum_from_buckets
  refine ⟨12*Real.sqrt K*G, by positivity, ?_⟩
  intro V I _ _ _ _ paths simple free unique L D h hh hL hD lengths degrees input
  let M (u : V) (j : ℕ) : ℝ := listImportantBaseIncidences paths u h (2^j)
  let P (u : V) (j : ℕ) : ℝ := (listLargeBranchBases paths u h (2^j)).card
  refine combine L D h hh hL hD hK M P (fun _ _ => Nat.cast_nonneg _) ?_ ?_ ?_
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
    exact lemma35_important_from_caps (Nat.cast_nonneg L) (Nat.cast_nonneg D) (Nat.cast_nonneg h)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hS hN
      (lemma35_list_important_upper simple free unique u h (2^j) (Nat.pow_pos (by decide)))
  · intro j u
    simpa only [P, Nat.cast_pow, Nat.cast_ofNat] using coarse simple u D h (2^j)
      (listLargeBranchBases paths u h (2^j)) (hh.trans_le hD) hh (Nat.pow_pos (by decide))
      (fun _ hi => (mem_filter.mp hi).2.2) degrees input
  · dsimp only [M]
    exact_mod_cast lemma35_list_on_base_dyadic_count unique h D degrees

/-- Uniformly averaging the actual filtered on-base tuples incurs no logarithmic loss. -/
theorem lemma35_list_on_base_expectation {C a b : ℝ} (hC : 1 ≤ C)
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
      (∑ base, ((listOnBaseBranchTuples paths base h).card:ℝ))/(p:ℝ) ≤
        A*(ℓ^2*d^2+ℓ^(3/2:ℝ)*d^2*(h:ℝ)^(5/4:ℝ)) := by
  obtain ⟨K, hK, bound⟩ := lemma35_list_on_base_sum hC ha₀ ha₁ hb₀ hb₁
  refine ⟨1024*K, by positivity, ?_⟩
  intro V I _ _ _ _ paths simple free unique L D h hn hp hh hL hD length degree input
  dsimp only
  intro hM capL capD
  apply lemma35_on_base_average_from_sum hK.le hn hp hM (hh.trans_le hL) capL capD
  · calc
      _ ≤ ∑ _ : I, L := sum_le_sum (fun i _ => length i)
      _ = _ := by simp [mul_comm]
  · exact bound simple free unique L D h hh hL hD length degree input

end OnlineReachabilityPreservers
