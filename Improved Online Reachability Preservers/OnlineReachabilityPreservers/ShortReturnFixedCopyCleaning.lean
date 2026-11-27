import OnlineReachabilityPreservers.BackwardCopyReturns
import OnlineReachabilityPreservers.ShortReturnComponentClipping

/-! Retain the original degree labels while deleting and grouping path incidences. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

private theorem fixed_copy_crop_mass {M K R lostV lostI : ℕ} (mPos : 0 < M)
    (kept : 2*M ≤ 3*K) (upper : K ≤ M) (paid : K ≤ R + (lostV+lostI))
    (lossV : 12*lostV ≤ M) (lossI : 8*M*lostI ≤ K^2) : 38*M ≤ 72*R := by
  have paidNat := Nat.mul_le_mul_left (24*M) paid
  have vertexNat := Nat.mul_le_mul_left (2*M) lossV
  have rowNat := Nat.mul_le_mul_left 3 lossI
  have paidInt : 24*(M:ℤ)*K ≤ 24*(M:ℤ)*(R+(lostV+lostI)) := by exact_mod_cast paidNat
  have vertexInt : 2*(M:ℤ)*(12*lostV) ≤ 2*(M:ℤ)*M := by exact_mod_cast vertexNat
  have rowInt : 3*(8*(M:ℤ)*lostI) ≤ 3*(K:ℤ)^2 := by exact_mod_cast rowNat
  have lo : 2*(M:ℤ) ≤ 3*(K:ℤ) := by exact_mod_cast kept
  have hi : (K:ℤ) ≤ M := by exact_mod_cast upper
  have factor : 0 ≤ (3*(K:ℤ)-2*M)*(22*(M:ℤ)-3*K) :=
    mul_nonneg (by omega) (by omega)
  apply (Nat.mul_le_mul_right_iff mPos).mp
  exact_mod_cast
    (show (38*(M:ℤ))*M ≤ (72*(R:ℤ))*M by nlinarith only [paidInt, vertexInt, rowInt, factor])

/-- Keep the labels of the original standard degree copies. A restriction
of the copied rows retaining two thirds of the mass, with the chosen
bridge exclusion and bounded path components, gives a frozen witness of
mass at least one thirty-sixth of the original mass. -/
theorem regularization_list_frozen_of_fixed_copy_path_restriction {n p k : ℕ} {half : Bool}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (kept : Fin p → List (ListVertexBlockIndex rows (4*(∑ i, (rows i).length)/n)))
    (sub : let M := ∑ i, (rows i).length
      ∀ i, (kept i).Sublist (splitListVertices rows (4*M/n) i))
    (legal : localOrderAdmissible half k kept)
    (pathRoom : let M := ∑ i, (rows i).length
      ∀ i, ∀ v ∈ kept i, (shortReturnRowComponent kept k i v).card ≤ 4*M/p)
    (roomMass : 2*(∑ i, (rows i).length) ≤ 3*(∑ i, (kept i).length)) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 36*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean := by
  classical
  let M := ∑ i, (rows i).length
  let K := ∑ i, (kept i).length
  let D := 4*M/n
  let L := 4*M/p
  let V := ListVertexBlockIndex rows D
  let copies := splitListVertices rows D
  let copyMarks (i : Fin p) := (copies i).toFinset
  let keptMarks (i : Fin p) := (kept i).toFinset
  have mPos : 0 < M := hn.trans_le dense
  have dPos : 0 < D := (four_average_width hn dense).1
  have degreeRoom : 3*M ≤ D*n := by
    have bounds := four_average_width_product (M := M) hn
    change 4*M < D*n+n at bounds
    omega
  have pathCapacity : 2*M ≤ (L/2+1)*p := half_average_width_capacity hp
  have copySimple (i : Fin p) : (copies i).Nodup := splitListVertices_simple rows D i (simple i)
  have keptSimple (i : Fin p) : (kept i).Nodup := (sub i).nodup (copySimple i)
  have degree (v : V) : (occurrences copyMarks v).card ≤ D := by
    have same : copyMarks = splitVertices (fun i => (rows i).toFinset) D :=
      funext (splitListVertices_toFinset rows D)
    rw [same]
    exact splitVertices_degree (fun i => (rows i).toFinset) dPos v
  have degreeLe (v : V) : (occurrences keptMarks v).card ≤ (occurrences copyMarks v).card := by
    apply card_le_card
    intro i on
    simp only [mem_occurrences, keptMarks, copyMarks, List.mem_toFinset] at on ⊢
    exact (sub i).subset on
  have originalDegreeMass : (∑ v, (occurrences copyMarks v).card) = M := by
    rw [sum_occurrences]
    simp [copyMarks, copies, List.toFinset_card_of_nodup, copySimple, M]
  have keptUpper : K ≤ M := by
    calc
      _ ≤ ∑ i, (copies i).length := sum_le_sum (fun i _ => (sub i).length_le)
      _ = _ := by simp [copies, M]
  obtain ⟨fullV, filledV, restV⟩ := splitListVertices_full_block_profile rows dPos
  obtain ⟨A, aCard, chargeV⟩ := trim_full_weight_blocks_quadratic_of_lower_bound
    (fun v => (occurrences copyMarks v).card) fullV (budget := n) dPos
    (fun v on => (filledV v on).ge) (restV.le.trans_eq (Fintype.card_fin n))
    (originalDegreeMass.trans_le ((by omega : M ≤ 3*M).trans degreeRoom))
  let lostV := ∑ v ∈ univ \ A, (occurrences copyMarks v).card
  have boundV : 12*lostV ≤ M := by
    apply (Nat.mul_le_mul_left_iff mPos).mp
    calc
      _ = 4*(3*M)*lostV := by ring
      _ ≤ 4*(D*n)*lostV := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 degreeRoom)
      _ ≤ _ := by
        rw [originalDegreeMass] at chargeV
        simpa only [pow_two] using chargeV
  obtain ⟨sizes, pieces, pieceSimple, pieceLegal, length, pieceMass, pieceDegree, lightI⟩ :=
    split_of_cappedShortReturnPartition keptSimple legal
      ((hasCappedShortReturnPartition_iff_component_room kept L k).mpr pathRoom)
  let I := Σₗ i : Fin p, Fin (sizes i)
  let marks (i : I) := (pieces i).toFinset
  let fullI : Finset I := univ.filter fun i => L/2 < (pieces i).length
  have remainder : (univ \ fullI).card ≤ p := by
    have complement : univ \ fullI = ({i ∈ univ | (pieces i).length ≤ L/2} : Finset I) := by
      ext i
      simp [fullI]
    exact complement ▸ lightI
  have pathMass : (∑ i : I, (pieces i).length) = K := pieceMass
  obtain ⟨B, bCard, chargeI⟩ := trim_full_weight_blocks_quadratic_of_lower_bound
    (fun i => (pieces i).length) fullI (Nat.succ_pos _)
    (fun i on => (mem_filter.mp on).2)
    remainder (pathMass.trans_le (keptUpper.trans ((by omega : M ≤ 2*M).trans pathCapacity)))
  let lostI := ∑ i ∈ univ \ B, (pieces i).length
  have boundI : 8*M*lostI ≤ K^2 := calc
    _ = 4*(2*M)*lostI := by ring
    _ ≤ 4*((L/2+1)*p)*lostI := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 pathCapacity)
    _ ≤ _ := by rw [← pathMass]; exact chargeI
  have setMass : (∑ i, (marks i).card) = K :=
    (sum_congr rfl (fun i _ => List.toFinset_card_of_nodup (pieceSimple i))).trans pathMass
  have restMass : (∑ i, (marks i ∩ A).card) + (∑ v ∈ univ \ A, (occurrences marks v).card) = K := by
    have cols : (∑ i, (marks i ∩ A).card) = ∑ v ∈ A, (occurrences marks v).card := by
      rw [← sum_occurrences (fun i => marks i ∩ A)]
      have weight (v : V) : (occurrences (fun i => marks i ∩ A) v).card =
          if v ∈ A then (occurrences marks v).card else 0 := by
        by_cases on : v ∈ A <;> simp [occurrences, on]
      simp only [weight, ← sum_filter, filter_mem_eq_inter, univ_inter]
      rfl
    rw [cols, add_comm, sum_sdiff (subset_univ A), sum_occurrences, setMass]
  have restBound : (∑ v ∈ univ \ A, (occurrences marks v).card) ≤ lostV :=
    sum_le_sum (fun v _ => (pieceDegree v).trans_le (degreeLe v))
  let R := ∑ i ∈ B, (marks i ∩ A).card
  have rowCrop : (∑ i, (marks i ∩ A).card) ≤ R + lostI := calc
    _ = (∑ i ∈ univ \ B, (marks i ∩ A).card) + R := (sum_sdiff (subset_univ B)).symm
    _ ≤ lostI + R := Nat.add_le_add_right (sum_le_sum fun i _ =>
      (card_le_card inter_subset_left).trans_eq (List.toFinset_card_of_nodup (pieceSimple i))) R
    _ = _ := Nat.add_comm _ _
  have lower : 38*M ≤ 72*R :=
    fixed_copy_crop_mass mPos roomMass keptUpper (by omega) boundV boundI
  let crop := restrictListPaths pieces A B
  have cropAllowed : localOrderAdmissible half k crop := by
    cases half
    · exact restrictListPaths_fullFree pieceSimple pieceLegal A B
    · exact restrictListPaths_halfFree pieceSimple pieceLegal A B
  have cropSimple (i : B) : (crop i).Nodup := restrictListPath_nodup (pieceSimple i.val) A
  have cropLength (i : B) : (crop i).length ≤ L := calc
    _ = (marks i.val ∩ A).card := restrictListPath_length (pieceSimple i.val) A
    _ ≤ (marks i.val).card := card_le_card inter_subset_left
    _ = (pieces i.val).length := List.toFinset_card_of_nodup (pieceSimple i.val)
    _ ≤ _ := length i.val
  have cropDegree (v : A) : (occurrences (fun i => (crop i).toFinset) v).card ≤ D := by
    rw [show (fun i => (crop i).toFinset) = rectanglePaths marks A B from
      funext (restrictListPaths_toFinset pieces A B)]
    exact (rectanglePaths_degree_le marks A B v).trans
      ((pieceDegree v.val).trans_le ((degreeLe v.val).trans (degree v.val)))
  have cropMass : ∑ i, (crop i).length = R := by
    change _ = ∑ i ∈ B, (marks i ∩ A).card
    rw [← Finset.sum_attach B (fun i => (marks i ∩ A).card)]
    exact sum_congr rfl (fun i _ => restrictListPath_length (pieceSimple i.val) A)
  have cropUpper : (∑ i, (crop i).length) ≤ K := calc
    _ = R := cropMass
    _ ≤ ∑ i ∈ B, (marks i).card := sum_le_sum (fun i _ => card_le_card inter_subset_left)
    _ ≤ ∑ i, (marks i).card := sum_le_sum_of_subset (subset_univ B)
    _ = K := setMass
  refine regularization_list_frozen_after_caps_with_ratios_of_mass (retention := 36)
    (vNum := 1) (vDen := 1) (pNum := 1) (pDen := 1) crop cropSimple cropAllowed hn hp dense long
    (by decide) (by decide) (by decide) (by decide) ?_ ?_ cropLength cropDegree (cropUpper.trans keptUpper) ?_
  · simpa only [one_mul, Fintype.card_coe] using aCard
  · simpa only [one_mul, Fintype.card_coe] using bCard
  · simpa only [one_mul, cropMass] using lower

/-- On fixed degree copies, charge both the initial deletions and the
path-component excess of the retained rows. Losing at most one third of
the original mass still gives a frozen witness. -/
theorem regularization_list_frozen_of_small_fixed_copy_path_excess {n p k : ℕ} {half : Bool}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (kept : Fin p → List (ListVertexBlockIndex rows (4*(∑ i, (rows i).length)/n)))
    (sub : let M := ∑ i, (rows i).length
      ∀ i, (kept i).Sublist (splitListVertices rows (4*M/n) i))
    (legal : localOrderAdmissible half k kept)
    (excess : let M := ∑ i, (rows i).length
      3*(M - (∑ i, (kept i).length) + shortReturnPathExcessMass kept (4*M/p) k) ≤ M) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 36*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  let L := 4*M/p
  let K := ∑ i, (kept i).length
  let clipped := clipShortReturnPathComponents kept L k
  have keptSimple (i : Fin p) : (kept i).Nodup :=
    (sub i).nodup (splitListVertices_simple rows _ i (simple i))
  have upper : K ≤ M := by
    calc
      _ ≤ ∑ i, (splitListVertices rows (4*M/n) i).length := sum_le_sum (fun i _ => (sub i).length_le)
      _ = _ := by simp [M]
  have mass : (∑ i, (clipped i).length) + shortReturnPathExcessMass kept L k = K :=
    clipShortReturnPathComponents_mass kept keptSimple L k
  have clipSub := clipShortReturnPathComponents_sublist kept L k
  have clipAllowed := localOrderAdmissible_of_sublist keptSimple clipSub legal
  change 3*(M - K + shortReturnPathExcessMass kept L k) ≤ M at excess
  exact regularization_list_frozen_of_fixed_copy_path_restriction rows simple hn hp dense long clipped
    (fun i => (clipSub i).trans (sub i)) clipAllowed
    (clipShortReturnPathComponents_room kept keptSimple L k) (by omega)

/-- Full exclusion suffices for the initial degree split. The one-third
path-excess test can then be checked on the copied graph. -/
theorem regularization_list_frozen_full_of_small_copied_path_excess {n p k : ℕ}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : BridgeFree (Before rows) k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (excess : let M := ∑ i, (rows i).length
      3*shortReturnPathExcessMass (splitListVertices rows (4*M/n)) (4*M/p) k ≤ M) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 36*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  let copies := splitListVertices rows (4*M/n)
  have legal : BridgeFree (Before copies) k :=
    free.split_list_vertices_any (·.fst) (fun {i _ _} step => splitListVertices_step (simple i) step)
  have mass : (∑ i, (copies i).length) = M := by simp [copies, M]
  refine regularization_list_frozen_of_small_fixed_copy_path_excess (half := false)
    rows simple hn hp dense long copies (fun _ => List.Sublist.refl _) legal ?_
  dsimp only
  change 3*(M - (∑ i, (copies i).length) + shortReturnPathExcessMass copies (4*M/p) k) ≤ M
  simpa only [mass, Nat.sub_self, zero_add] using excess

/-- In half mode the earlier-copy return test certifies the exclusion
on the retained copies before the path-component clipping. -/
theorem regularization_list_frozen_half_of_small_fixed_copy_path_excess {n p k : ℕ}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : HalfBridgeFree (Before rows) k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (kept : Fin p → List (ListVertexBlockIndex rows (4*(∑ i, (rows i).length)/n)))
    (sub : let M := ∑ i, (rows i).length
      ∀ i, (kept i).Sublist (splitListVertices rows (4*M/n) i))
    (noReturns : NoShortBackwardCopyReturnIn kept (k-3))
    (excess : let M := ∑ i, (rows i).length
      3*(M - (∑ i, (kept i).length) + shortReturnPathExcessMass kept (4*M/p) k) ≤ M) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) k ∧
      M ≤ 36*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean :=
  regularization_list_frozen_of_small_fixed_copy_path_excess (half := true)
    rows simple hn hp dense long kept sub
    (copied_subrows_halfFree_of_noShortBackwardCopyReturn rows simple kept sub free noReturns)
    excess

end OnlineReachabilityPreservers
