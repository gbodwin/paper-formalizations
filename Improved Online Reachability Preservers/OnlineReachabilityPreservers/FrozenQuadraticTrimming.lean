import OnlineReachabilityPreservers.LocalFrozenCleaning
import OnlineReachabilityPreservers.ReverseIntersectionCopies
import OnlineReachabilityPreservers.WidthBlockProfiles

/-! Use full blocks to fit a high-mass subsystem within both frozen budgets. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

private theorem average_width_times_budget {M q : ℕ} (positive : 0 < q) (dense : q ≤ M) :
    3 * M ≤ (4 * M / q) * q := by
  have next := Nat.lt_mul_div_succ (4 * M) positive
  rw [Nat.mul_succ, Nat.mul_comm q (4 * M / q)] at next
  omega

private theorem large_cropped_mass {M K R lost : ℕ} (positive : 0 < M) (upper : K ≤ M)
    (enough : 9 * M ≤ 16 * K) (cropped : K ≤ R + lost) (loss : 6 * M * lost ≤ K ^ 2) :
    261 * M ≤ 512 * R := by
  have paid : 6 * M * K ≤ 6 * M * R + K ^ 2 := calc
    _ ≤ 6 * M * (R + lost) := Nat.mul_le_mul_left _ cropped
    _ ≤ _ := by rw [Nat.mul_add]; exact Nat.add_le_add_left loss _
  have paidReal : 6 * (M : ℝ) * K ≤ 6 * (M : ℝ) * R + (K : ℝ) ^ 2 := by
    exact_mod_cast paid
  have lower : 0 ≤ 16 * (K : ℝ) - 9 * M := sub_nonneg.mpr (by exact_mod_cast enough)
  have upperReal : (K : ℝ) ≤ M := by exact_mod_cast upper
  have extent : 0 ≤ 87 * (M : ℝ) - 16 * K := by
    linarith [Nat.cast_nonneg (α := ℝ) M]
  have clipped : 261 * (M : ℝ) * M ≤ 512 * (R : ℝ) * M := by
    nlinarith only [mul_nonneg lower extent, paidReal]
  apply (Nat.mul_le_mul_right_iff positive).mp
  exact_mod_cast clipped

private theorem trim_width_supports {V I : Type*} [LinearOrder V] [Fintype V] [LinearOrder I] [Fintype I]
    (paths : I → Finset V) (fullV : Finset V) (fullI : Finset I) {n p D L M : ℕ}
    (Dpos : 0 < D) (Lpos : 0 < L)
    (vFilled : ∀ v ∈ fullV, (occurrences paths v).card = D) (vRest : (univ \ fullV).card ≤ n)
    (iFilled : ∀ i ∈ fullI, (paths i).card = L) (iRest : (univ \ fullI).card ≤ p)
    (vWidth : 3 * M ≤ D * n) (iWidth : 3 * M ≤ L * p)
    (mPositive : 0 < M) (upper : ∑ i, (paths i).card ≤ M)
    (lower : 9 * M ≤ 16 * (∑ i, (paths i).card)) :
    ∃ A : Finset V, ∃ B : Finset I, A.card ≤ n ∧ B.card ≤ p ∧
      261 * M ≤ 512 * (∑ i ∈ B, (paths i ∩ A).card) := by
  let K := ∑ i, (paths i).card
  have vRoom : K ≤ D * n := (upper.trans (by omega : M ≤ 3 * M)).trans vWidth
  have iRoom : K ≤ L * p := (upper.trans (by omega : M ≤ 3 * M)).trans iWidth
  obtain ⟨A, va, lostV, boundV, exactV⟩ := trim_full_vertex_blocks_quadratic paths fullV Dpos vFilled vRest vRoom
  obtain ⟨B, ib, boundI⟩ := trim_full_weight_blocks_quadratic (fun i => (paths i).card) fullI Lpos iFilled iRest iRoom
  let lostI := ∑ i ∈ univ \ B, (paths i).card
  let R := ∑ i ∈ B, (paths i ∩ A).card
  have originalColumns : (∑ i ∈ (univ : Finset I), (paths i ∩ A).card) + lostV = K := by
    rw [Finset.sum_subtype (univ : Finset I) (fun _ => Iff.rfl) (fun i => (paths i ∩ A).card)]
    have equal (i : (univ : Finset I)) : (rectanglePaths paths A univ i).card = (paths i.val ∩ A).card := by
      rw [← card_image_of_injective _ Subtype.val_injective]
      congr 1
      ext v
      simp only [rectanglePaths, mem_image, mem_filter, mem_attach, true_and, mem_inter]
      constructor
      · rintro ⟨w, onPath, rfl⟩
        exact ⟨onPath, w.property⟩
      · rintro ⟨onPath, allowed⟩
        exact ⟨⟨v, allowed⟩, onPath, rfl⟩
    simpa only [equal] using exactV
  have byRows : (∑ i ∈ (univ : Finset I), (paths i ∩ A).card) ≤ R + lostI := calc
    _ = (∑ i ∈ univ \ B, (paths i ∩ A).card) + R := (sum_sdiff (subset_univ B)).symm
    _ ≤ lostI + R := Nat.add_le_add_right (sum_le_sum fun i _ => card_le_card inter_subset_left) R
    _ = _ := Nat.add_comm _ _
  have both : 6 * M * (lostV + lostI) ≤ K ^ 2 := by
    have timesV : 12 * M * lostV ≤ K ^ 2 := by
      apply le_trans _ boundV
      have scaled := Nat.mul_le_mul_right lostV (Nat.mul_le_mul_left 4 vWidth)
      simpa only [← Nat.mul_assoc] using scaled
    have timesI : 12 * M * lostI ≤ K ^ 2 := by
      apply le_trans _ boundI
      have scaled := Nat.mul_le_mul_right lostI (Nat.mul_le_mul_left 4 iWidth)
      simpa only [← Nat.mul_assoc] using scaled
    have factor : 2 * (6 * M * (lostV + lostI)) ≤ 2 * K ^ 2 := calc
      _ = 12 * M * lostV + 12 * M * lostI := by ring
      _ ≤ K ^ 2 + K ^ 2 := Nat.add_le_add timesV timesI
      _ = _ := by ring
    omega
  exact ⟨A, B, va, ib, large_cropped_mass mPositive upper lower (by omega) both⟩

/-- A subsystem carrying at least nine sixteenths of the original mass
can be split at the original widths and trimmed back to both budgets.
If the splits preserve the chosen bridge exclusion, frozen peeling keeps
at least one 104th of the original mass. -/
theorem regularization_list_frozen_after_quadratic_width_trim {V I : Type*}
    [LinearOrder V] [Fintype V] [LinearOrder I] [Fintype I] {half : Bool} {k n p M : ℕ}
    (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k (listRegularizedPaths paths (4 * M / n) (4 * M / p)))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (vertices : Fintype.card V ≤ n) (rows : Fintype.card I ≤ p)
    (upper : ∑ i, (paths i).length ≤ M) (lower : 9 * M ≤ 16 * (∑ i, (paths i).length)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 104 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean := by
  let D := 4 * M / n
  let L := 4 * M / p
  let pieces := listRegularizedPaths paths D L
  let raw := fun i => (pieces i).toFinset
  obtain ⟨Dpos, _, _⟩ := four_average_width hn dense
  obtain ⟨Lpos, _, _⟩ := four_average_width hp long
  change 0 < D at Dpos
  change 0 < L at Lpos
  have pieceSimple := listRegularizedPaths_simple paths simple D L
  obtain ⟨mass, length, degree⟩ := regularization_list_mass_caps paths simple D L Dpos Lpos
  have setMass : (∑ i, (raw i).card) = ∑ i, (paths i).length :=
    (sum_congr rfl fun i _ => List.toFinset_card_of_nodup (pieceSimple i)).trans mass
  obtain ⟨fullV, fullI, filledV, restV, filledI, restI⟩ :=
    listRegularizedPaths_full_block_profiles paths simple Dpos Lpos
  obtain ⟨A, B, va, ib, kept⟩ := trim_width_supports raw fullV fullI Dpos Lpos filledV
    (by exact restV.le.trans vertices)
    (fun i active => (List.toFinset_card_of_nodup (pieceSimple i)).trans (filledI i active))
    (by exact restI.le.trans rows)
    (average_width_times_budget hn dense) (average_width_times_budget hp long) (hn.trans_le dense)
    (setMass.trans_le upper) (by rw [setMass]; exact lower)
  let crop := restrictListPaths pieces A B
  have cropSimple (i : B) : (crop i).Nodup := restrictListPath_nodup (pieceSimple i.val) A
  have cropAllowed : localOrderAdmissible half k crop := by
    cases half
    · exact restrictListPaths_fullFree pieceSimple allowed A B
    · exact restrictListPaths_halfFree pieceSimple allowed A B
  have cropLength (i : B) : (crop i).length ≤ L := calc
    _ = (raw i.val ∩ A).card := restrictListPath_length (pieceSimple i.val) A
    _ ≤ (raw i.val).card := card_le_card inter_subset_left
    _ = (pieces i.val).length := List.toFinset_card_of_nodup (pieceSimple i.val)
    _ ≤ L := length i.val
  have cropDegree (v : A) : (occurrences (fun i => (crop i).toFinset) v).card ≤ D := by
    have projected : (fun i => (crop i).toFinset) = rectanglePaths raw A B :=
      funext (restrictListPaths_toFinset pieces A B)
    rw [projected]
    exact (rectanglePaths_degree_le raw A B v).trans (degree v.val)
  have cropMass : (∑ i, (crop i).length) = ∑ i ∈ B, (raw i ∩ A).card := by
    rw [← Finset.sum_attach B (fun i => (raw i ∩ A).card)]
    exact sum_congr rfl fun i _ => restrictListPath_length (pieceSimple i.val) A
  have cropUpper : ∑ i, (crop i).length ≤ M := calc
    _ = ∑ i ∈ B, (raw i ∩ A).card := cropMass
    _ ≤ ∑ i ∈ B, (raw i).card := sum_le_sum fun _ _ => card_le_card inter_subset_left
    _ ≤ ∑ i, (raw i).card := sum_le_sum_of_subset (subset_univ B)
    _ ≤ M := setMass.trans_le upper
  refine regularization_list_frozen_after_caps_with_ratios_of_mass (retention := 104)
    (vNum := 1) (vDen := 1) (pNum := 1) (pDen := 1) crop cropSimple cropAllowed hn hp dense long
      (by decide) (by decide) (by decide) (by decide) ?_ ?_ cropLength cropDegree cropUpper ?_
  · simpa only [one_mul, Fintype.card_coe] using va
  · simpa only [one_mul, Fintype.card_coe] using ib
  · change 106 * M ≤ 208 * (∑ i, (crop i).length)
    rw [cropMass]
    exact (show ∀ {Q : ℕ}, 261 * M ≤ 512 * Q → 106 * M ≤ 208 * Q by intro _ h; omega) kept

local notation "Before" => SourceAudit.BeforeIn

private theorem restrict_all_rows_mass {V I : Type*} [LinearOrder V] [Fintype V] [Fintype I]
    (paths : I → List V) (simple : ∀ i, (paths i).Nodup) (A : Finset V) :
    (∑ i : (univ : Finset I), (restrictListPaths paths A univ i).length) =
      ∑ v ∈ A, (occurrences (fun i => (paths i).toFinset) v).card := by
  let raw (i : I) := (paths i).toFinset
  calc
    _ = ∑ i : (univ : Finset I), (raw i.val ∩ A).card :=
      sum_congr rfl fun i _ => restrictListPath_length (simple i.val) A
    _ = ∑ i, (raw i ∩ A).card :=
      (Finset.sum_subtype (univ : Finset I) (fun _ => Iff.rfl) (fun i => (raw i ∩ A).card)).symm
    _ = ∑ v, (occurrences (fun i => raw i ∩ A) v).card := (sum_occurrences _).symm
    _ = ∑ v, if v ∈ A then (occurrences raw v).card else 0 := by
      apply sum_congr rfl
      intro v _
      by_cases keeps : v ∈ A <;> simp [occurrences, keeps]
    _ = _ := by
      rw [← sum_filter]
      simp only [filter_mem_eq_inter, univ_inter, raw]

/-- After copying the vertices of reverse intersections, keep the
heaviest original-budget number of occupied copies. Nine sixteenths of
the original mass suffice for the quadratic trims and frozen peeling. -/
theorem regularization_list_frozen_of_reverse_support_ratio {half : Bool} {k n p : ℕ}
    (cutoff : k = 4 ∨ (k = 6 ∧ half = false)) (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (support : 9 * (activeListVertices (splitReverseIntersections paths)).card ≤ 16 * n) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 104 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let copies := splitReverseIntersections paths
  let ordinary := activeListPaths copies
  let Z (i : activeListIndices copies) := (ordinary i).toFinset
  have three : 3 ≤ k := by rcases cutoff with rfl | ⟨rfl, _⟩ <;> decide
  have halfFree : HalfBridgeFree (Before paths) k := by
    cases half
    · exact (show BridgeFree (Before paths) k from allowed).halfFree
    · exact allowed
  have copySimple : ∀ i, (copies i).Nodup := splitReverseIntersections_simple simple
  have copyAllowed : localOrderAdmissible half k copies := by
    cases half
    · exact splitReverseIntersections_fullFree simple allowed
    · have small : k ≤ 4 := by
        rcases cutoff with rfl | ⟨_, impossible⟩
        · exact le_rfl
        · cases impossible
      exact splitReverseIntersections_halfFree simple halfFree small
  have ordinaryUnique : ∀ {a b x y}, a ≠ b → x ∈ ordinary a → x ∈ ordinary b →
      y ∈ ordinary a → y ∈ ordinary b → x = y :=
    restrictListPaths_unique (fun different => splitReverseIntersections_unique halfFree three different) _ _
  have ordinarySimple : ∀ i, (ordinary i).Nodup := activeListPaths_simple copies copySimple
  have ordinaryAllowed : localOrderAdmissible half k ordinary :=
    activeListPaths_admissible copies copySimple copyAllowed
  have mass : (∑ i, (ordinary i).length) = M := by
    rw [activeListPaths_mass copies copySimple]
    simp only [copies, splitReverseIntersections_length, M]
  obtain ⟨A, _, fits, retained⟩ := trim_weights_ratio (n := n) (a := 9) (b := 16)
    (univ : Finset (activeListVertices copies)) (fun v => (occurrences Z v).card)
      (by decide) (by simpa only [card_univ, Fintype.card_coe] using support)
  let chosen := restrictListPaths ordinary A univ
  have chosenMass : (∑ i, (chosen i).length) = ∑ v ∈ A, (occurrences Z v).card :=
    restrict_all_rows_mass ordinary ordinarySimple A
  have total : (∑ v, (occurrences Z v).card) = M := by
    rw [sum_occurrences]
    simpa only [Z, List.toFinset_card_of_nodup (ordinarySimple _)] using mass
  have keeps : 9 * M ≤ 16 * (∑ i, (chosen i).length) := by simpa only [total, chosenMass] using retained
  have upper : (∑ i, (chosen i).length) ≤ M := by
    rw [chosenMass, ← total]
    exact sum_le_sum_of_subset (subset_univ _)
  have chosenUnique : ∀ {a b x y}, a ≠ b → x ∈ chosen a → x ∈ chosen b →
      y ∈ chosen a → y ∈ chosen b → x = y :=
    restrictListPaths_unique (fun different => ordinaryUnique different) _ _
  have chosenSimple (i : (univ : Finset (activeListIndices copies))) : (chosen i).Nodup :=
    restrictListPath_nodup (ordinarySimple i.val) A
  have chosenAllowed : localOrderAdmissible half k chosen := by
    cases half
    · exact restrictListPaths_fullFree ordinarySimple ordinaryAllowed _ _
    · exact restrictListPaths_halfFree ordinarySimple ordinaryAllowed _ _
  have safe (D L : ℕ) : localOrderAdmissible half k (listRegularizedPaths chosen D L) := by
    rcases cutoff with rfl | ⟨rfl, rfl⟩
    · cases half
      · exact listRegularizedPaths_fullFree chosenSimple chosenUnique chosenAllowed D L
      · exact listRegularizedPaths_halfFree chosenSimple chosenUnique chosenAllowed D L
    · have four : BridgeFree (Before chosen) 4 := fun _ small => chosenAllowed (small.trans (by decide))
      exact regularizedSix_bridge_free chosenSimple (fun {_ _ _ _} => chosenUnique) four chosenAllowed D L
  apply regularization_list_frozen_after_quadratic_width_trim chosen chosenSimple (safe _ _)
    hn hp dense long _ _ upper keeps
  · simpa only [Fintype.card_coe] using fits
  · simpa only [Fintype.card_coe, card_univ, Fintype.card_fin] using card_le_univ (activeListIndices copies)

/-- The support-ratio criterion applies when at most seven ninths of
the vertices have an outgoing reverse partner at any of their occurrences. -/
theorem regularization_list_frozen_of_seven_ninths_reverse_vertices {half : Bool} {k n p : ℕ}
    (cutoff : k = 4 ∨ (k = 6 ∧ half = false)) (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (few : 9 * (reversePartnerVertices paths).card ≤ 7 * n) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 104 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean := by
  apply regularization_list_frozen_of_reverse_support_ratio cutoff paths simple allowed hn hp dense long
  have occupied : (activeListVertices paths).card ≤ n := by
    simpa only [Fintype.card_fin] using card_le_univ (activeListVertices paths)
  have copied := splitReverseIntersections_support_le paths
  omega

end OnlineReachabilityPreservers
