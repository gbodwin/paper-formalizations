import OnlineReachabilityPreservers.LocalInducedPaths
import OnlineReachabilityPreservers.LocalOfflineCounting
import OnlineReachabilityPreservers.OfflineMoment

/-! The sampled upper moment for locally ordered paths in Appendix B. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V I : Type*} [LinearOrder V] [Fintype V] [LinearOrder I] [Fintype I]

local notation "ListBefore" => SourceAudit.BeforeIn

omit [LinearOrder I] [Fintype V] in
theorem listBranchSupport_card_caps (paths : I → List V) (b : I) (h L D : ℕ)
    (cap : (paths b).length ≤ L)
    (degrees : ∀ u ∈ paths b, (occurrences (fun i => (paths i).toFinset) u).card ≤ D) :
    (listBranchSupport paths b h).card ≤ L*D*(h+1) := calc
  _ ≤ ∑ u ∈ (paths b).toFinset, (occurrences (fun i => (paths i).toFinset) u).card*(h+1) :=
    listBranchSupport_card paths b h
  _ ≤ ∑ _ ∈ (paths b).toFinset, D*(h+1) :=
    sum_le_sum fun u hu => Nat.mul_le_mul_right _ (degrees u (List.mem_toFinset.mp hu))
  _ = (paths b).toFinset.card * D * (h+1) := by simp [mul_assoc]
  _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ((List.toFinset_card_le _).trans cap))

/-- Lemma 41 with the shared moment estimate on the actual local subsystem. -/
theorem lemma41_list_sampled_upper {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (ListBefore paths) 4)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (base : I) (h D : ℕ) {n L C b : ℝ} (hn : 1 ≤ n) (hD : 0 < D) (hdn : (D : ℝ) ≤ n)
    (hL : 0 < L) (hC : 0 < C) (hb₀ : 1/2 < b) (hb₁ : b ≤ 1)
    (ambient : ((listBranchSupport paths base h).card : ℝ) ≤ n)
    (cap : ∀ i, ((paths i).length : ℝ) ≤ L)
    (degrees : ∀ u ∈ listBranchSupport paths base h, (occurrences (fun i => (paths i).toFinset) u).card ≤ D)
    (subfamily : ∀ J : Finset I,
      let p : ℝ := J.card
      (∑ i : J, ((restrictListPaths paths (listBranchSupport paths base h) J i).length : ℝ)) ≤
        C * max n (max (n^(3/4 : ℝ)*p^(1/2 : ℝ)) (max (n^(2-2*b)*p^b) p))) :
    ((listOffBaseBranchTuples paths base h).card : ℝ) ≤
      2*C*n*L + Real.exp 8 * (max 1 C)^2 * (2+Real.log n) * n^(3/2 : ℝ) +
      (2*C+(1/(2*b-1)+1)*C^(1/b))*n^(1/b)*(D : ℝ)^((2*b-1)/b) := by
  let S := listBranchSupport paths base h
  let marks (i : I) := (paths i).toFinset
  let restricted := inducedPath marks S
  have inSupport (i : I) : (restricted i).card = (marks i ∩ S).card := inducedPath_card marks S i
  have capacities (i : I) : ((restricted i).card : ℝ) ≤ L := by
    have sub : (restricted i).card ≤ (paths i).length :=
      (inSupport i).le.trans ((card_le_card inter_subset_left).trans (List.toFinset_card_le _))
    exact (Nat.cast_le.mpr sub).trans (cap i)
  have massNat : (∑ i, (restricted i).card) ≤ S.card * D := inducedPath_mass_le marks S D degrees
  have mass : (∑ i, ((restricted i).card : ℝ)) ≤ n*D := calc
    _ ≤ (S.card : ℝ)*D := by exact_mod_cast massNat
    _ ≤ _ := mul_le_mul_of_nonneg_right ambient (by positivity)
  have upper := lemma40_moment_from_subfamily restricted hn
    (show (0 : ℝ) < D by exact_mod_cast hD) hdn hL hC hb₀ hb₁ capacities mass (by
      intro J
      have equality (i : J) : (restricted i.val).card = (restrictListPaths paths S J i).length :=
        (inSupport i.val).trans (restrictListPath_length (simple i.val) S).symm
      rw [← J.sum_coe_sort (fun i => ((restricted i).card : ℝ))]
      simpa only [equality] using subfamily J)
  have pairs : (listOffBaseBranchTuples paths base h).card ≤ ∑ i, (restricted i).card^2 := by
    have bound := lemma41_list_branch_count free unique base h
    change _ ≤ ∑ i, (marks i ∩ S).card^2 at bound
    simpa only [inSupport] using bound
  exact (show ((listOffBaseBranchTuples paths base h).card : ℝ) ≤ ∑ i, ((restricted i).card : ℝ)^2 by
    exact_mod_cast pairs).trans upper

end OnlineReachabilityPreservers
