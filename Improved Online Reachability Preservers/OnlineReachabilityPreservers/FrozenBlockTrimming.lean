import OnlineReachabilityPreservers.ActiveNestedCutCounting
import OnlineReachabilityPreservers.WidthBlockProfiles

/-! Trimming repaired width blocks while using their original mass profiles. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

private theorem average_width_room {M q : ℕ} (positive : 0 < q) (dense : q ≤ M) :
    3*M ≤ (4*M/q)*q := by
  have next := Nat.lt_mul_div_succ (4*M) positive
  rw [Nat.mul_succ,Nat.mul_comm q (4*M/q)] at next
  omega

private theorem inter_card_le_inter_card_add_loss {V : Type*} [DecidableEq V]
    {whole kept : Finset V} (sub : kept ⊆ whole) (A : Finset V) :
    (whole ∩ A).card ≤ (kept ∩ A).card + (whole \ kept).card := by
  have same : (whole ∩ A) ∩ kept = kept ∩ A := by
    ext x
    simp only [mem_inter]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨sub h.1,h.2⟩,h.1⟩⟩
  have inside : (whole ∩ A) \ kept ⊆ whole \ kept := by
    intro x hx
    simp only [mem_sdiff,mem_inter] at hx ⊢
    exact ⟨hx.1.1,hx.2⟩
  calc
    _ = ((whole ∩ A) \ kept).card + ((whole ∩ A) ∩ kept).card :=
      (card_sdiff_add_card_inter _ _).symm
    _ = (kept ∩ A).card + ((whole ∩ A) \ kept).card := by rw [same,add_comm]
    _ ≤ _ := Nat.add_le_add_left (card_le_card inside) _

private theorem restrict_after_deletions_mass {V I : Type*} [LinearOrder V] [Fintype I] [DecidableEq I]
    {pieces kept : I → List V} (simple : ∀ i, (pieces i).Nodup) (sub : ∀ i, List.Sublist (kept i) (pieces i))
    (A : Finset V) (B : Finset I) :
    (∑ i ∈ B, ((pieces i).toFinset ∩ A).card) + (∑ i, (kept i).length) ≤
      (∑ i : B, (restrictListPaths kept A B i).length) + (∑ i, (pieces i).length) := by
  let raw := fun i => (pieces i).toFinset
  let reduced := fun i => (kept i).toFinset
  have setSub (i : I) : reduced i ⊆ raw i := by
    intro v inside
    exact List.mem_toFinset.mpr ((sub i).subset (List.mem_toFinset.mp inside))
  have lost : (∑ i, (raw i \ reduced i).card) + (∑ i, (kept i).length) = ∑ i, (pieces i).length := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [← List.toFinset_card_of_nodup (simple i), ← List.toFinset_card_of_nodup ((sub i).nodup (simple i))]
    exact card_sdiff_add_card_eq_card (setSub i)
  have restricted : (∑ i : B, (restrictListPaths kept A B i).length) = ∑ i ∈ B, (reduced i ∩ A).card := by
    rw [← sum_attach B (fun i => (reduced i ∩ A).card)]
    exact sum_congr rfl (fun i _ => restrictListPath_length ((sub i.val).nodup (simple i.val)) A)
  have compares : (∑ i ∈ B, (raw i ∩ A).card) ≤
      (∑ i ∈ B, (reduced i ∩ A).card) + (∑ i, (raw i \ reduced i).card) := calc
    _ ≤ ∑ i ∈ B, ((reduced i ∩ A).card + (raw i \ reduced i).card) :=
      sum_le_sum (fun i _ => inter_card_le_inter_card_add_loss (setSub i) A)
    _ = _ + ∑ i ∈ B, (raw i \ reduced i).card := sum_add_distrib
    _ ≤ _ := Nat.add_le_add_left (sum_le_sum_of_subset (subset_univ B)) _
  rw [restricted,← lost]
  exact (Nat.add_le_add_right compares _).trans_eq (Nat.add_assoc _ _ _)

private theorem cropped_width_pieces_allowed {V I : Type*} [LinearOrder V] [LinearOrder I]
    {half : Bool} {k : ℕ} {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (valid : localOrderAdmissible half k paths) (A : Finset V) (B : Finset I) :
    localOrderAdmissible half k (restrictListPaths paths A B) := by
  cases half
  · exact restrictListPaths_fullFree simple valid A B
  · exact restrictListPaths_halfFree simple valid A B

/-- For the original four-average width splits, trimming to the original
supports loses at most one sixth of the original mass. Up to one quarter
more can be removed before the trims, provided those deletions exclude
the required bridges. Peeling at the original averages keeps `M / 12`. -/
theorem regularization_list_frozen_after_quarter_width_deletions {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (repair : let M := ∑ i, (paths i).length
      let pieces := listRegularizedPaths paths (4*M/n) (4*M/p)
      ∃ kept, (∀ i, List.Sublist (kept i) (pieces i)) ∧ localOrderAdmissible half k kept ∧
        3*M ≤ 4*(∑ i, (kept i).length)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 12*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let pieces := listRegularizedPaths paths D L
  let raw := fun i => (pieces i).toFinset
  obtain ⟨kept,sub,allowed,retained⟩ := repair
  have rawSimple := listRegularizedPaths_simple paths simple D L
  have simpleKept (i) : (kept i).Nodup := (sub i).nodup (rawSimple i)
  obtain ⟨dPos,_,_⟩ := four_average_width hn dense
  obtain ⟨lPos,_,_⟩ := four_average_width hp long
  obtain ⟨mass,lenCap,degreeCap⟩ := regularization_list_mass_caps paths simple D L dPos lPos
  have setMass : (∑ i, (raw i).card) = M :=
    (sum_congr rfl (fun i _ => List.toFinset_card_of_nodup (rawSimple i))).trans mass
  obtain ⟨fullV,fullI,filledV,restV,filledI,restI⟩ := listRegularizedPaths_full_block_profiles paths simple dPos lPos
  have roomV : 3*(∑ i, (raw i).card) ≤ D*n := by rw [setMass]; exact average_width_room hn dense
  have roomI : 3*(∑ i, (raw i).card) ≤ L*p := by rw [setMass]; exact average_width_room hp long
  obtain ⟨A,B,capA,capB,cropRaw⟩ := trim_full_block_rectangles raw fullV fullI dPos lPos hn hp filledV
    (by simpa only [Fintype.card_fin] using restV.le)
    (fun i full => (List.toFinset_card_of_nodup (rawSimple i)).trans (filledI i full))
    (by simpa only [Fintype.card_fin] using restI.le) roomV roomI
  let crop := restrictListPaths kept A B
  have cropSimple (i : B) : (crop i).Nodup := restrictListPath_nodup (simpleKept i.val) A
  have allowedCrop : localOrderAdmissible half k crop := cropped_width_pieces_allowed simpleKept allowed A B
  have croppedLength (i : B) : (crop i).length ≤ L := calc
    _ = ((kept i.val).toFinset ∩ A).card := restrictListPath_length (simpleKept i.val) A
    _ ≤ (kept i.val).toFinset.card := card_le_card inter_subset_left
    _ = (kept i.val).length := List.toFinset_card_of_nodup (simpleKept i.val)
    _ ≤ _ := (sub i.val).length_le.trans (lenCap i.val)
  have keptDegree (v : ListVertexBlockIndex paths D) :
      (occurrences (fun i => (kept i).toFinset) v).card ≤ D := by
    refine (card_le_card (t := occurrences raw v) ?_).trans (degreeCap v)
    intro i h
    have found : v ∈ (kept i).toFinset := (mem_occurrences (marks := fun j => (kept j).toFinset)).mp h
    exact mem_occurrences.mpr (List.mem_toFinset.mpr ((sub i).subset (List.mem_toFinset.mp found)))
  have croppedDegree (v : A) : (occurrences (fun i => (crop i).toFinset) v).card ≤ D := by
    let reduced := fun i => (kept i).toFinset
    have equals : (fun i : B => (crop i).toFinset) = rectanglePaths reduced A B :=
      funext (restrictListPaths_toFinset kept A B)
    have same := congrArg (fun family : B → Finset A => (occurrences family v).card) equals
    exact same.trans_le ((rectanglePaths_degree_le reduced A B v).trans (keptDegree v.val))
  have upper : (∑ i, (crop i).length) ≤ M := calc
    _ = ∑ i ∈ B, ((kept i).toFinset ∩ A).card := by
      rw [← sum_attach B (fun i => ((kept i).toFinset ∩ A).card)]
      exact sum_congr rfl (fun i _ => restrictListPath_length (simpleKept i.val) A)
    _ ≤ ∑ i ∈ B, (pieces i).length := sum_le_sum (fun i _ => calc
      _ ≤ (kept i).toFinset.card := card_le_card inter_subset_left
      _ = (kept i).length := List.toFinset_card_of_nodup (simpleKept i)
      _ ≤ (pieces i).length := (sub i).length_le)
    _ ≤ M := (sum_le_sum_of_subset (subset_univ B)).trans_eq mass
  have after := restrict_after_deletions_mass rawSimple sub A B
  rw [setMass] at cropRaw
  change (∑ i, (pieces i).length) = M at mass
  change (∑ i ∈ B, (raw i ∩ A).card) + (∑ i, (kept i).length) ≤
    (∑ i, (crop i).length) + (∑ i, (pieces i).length) at after
  rw [mass] at after
  refine regularization_list_frozen_after_caps_with_ratios_of_mass (half := half) (k := k) (retention := 12)
    (vNum := 1) (vDen := 1) (pNum := 1) (pDen := 1) crop cropSimple allowedCrop hn hp dense long
    (by decide) (by decide) (by decide) (by decide) ?_ ?_ croppedLength croppedDegree upper ?_
  · simpa only [one_mul,Fintype.card_coe] using capA
  · simpa only [one_mul,Fintype.card_coe] using capB
  · change 14*M ≤ 24*(∑ i, (crop i).length)
    change 3*M ≤ 4*(∑ i, (kept i).length) at retained
    omega

local notation "Before" => SourceAudit.BeforeIn

/-- The original budgets and four frozen caps hold at cutoff four if at
most one quarter of the mass consists of marked river starts. -/
theorem regularization_list_frozen_half_four_of_quarter_active_starts {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 4)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (few : let M := ∑ i, (paths i).length
      4*Nat.card (widthCutActiveNestedStarts paths (4*M/n) (4*M/p)) ≤ M) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 4 ∧
      M ≤ 12*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  obtain ⟨dPos,_,_⟩ := four_average_width hn dense
  obtain ⟨lPos,_,_⟩ := four_average_width hp long
  obtain ⟨mass,_,_⟩ := regularization_list_mass_caps paths simple D L dPos lPos
  obtain ⟨sub,valid,lost⟩ := repairWidthCutNestedStarts_spec paths simple free D L
  refine regularization_list_frozen_after_quarter_width_deletions (half := true) (k := 4)
    paths simple hn hp dense long ⟨repairWidthCutNestedStarts paths D L,sub,valid,?_⟩
  rw [mass] at lost
  change 4*Nat.card (widthCutActiveNestedStarts paths D L) ≤ M at few
  change 3*M ≤ 4*(∑ i, (repairWidthCutNestedStarts paths D L i).length)
  omega

/-- Later-block lengths alone suffice for the quarter-loss criterion. -/
theorem regularization_list_frozen_half_four_of_quarter_later_nonterminal {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 4)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (few : let M := ∑ i, (paths i).length
      4*(laterCutNonterminalIncidences paths (4*M/n) (4*M/p)).card ≤ M) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 4 ∧
      M ≤ 12*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_half_four_of_quarter_active_starts paths simple free hn hp dense long
    ((Nat.mul_le_mul_left 4 (widthCutActiveNestedStarts_card_le_later_nonterminal paths simple free _ _)).trans few)

end OnlineReachabilityPreservers
