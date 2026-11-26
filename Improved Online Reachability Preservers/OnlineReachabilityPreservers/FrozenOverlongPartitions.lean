import OnlineReachabilityPreservers.ClippedVertexPartitions
import OnlineReachabilityPreservers.FrozenLengthCappedPaths

/-! A common vertex partition for overlong rows when their pair count is small. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

/-- Fit the pieces from a common vertex partition within half the original
path budget. If clipping leaves two fifths of the original mass, the
frozen caps can be met without pruning opposite intersections. -/
theorem regularization_list_frozen_by_half_budget_clipped_partition {I : Type*} [LinearOrder I] [Fintype I]
    {half : Bool} {k n p M r lossBudget : ℕ} (paths : I → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths) (size : half = true → k ≤ 4)
    (rPos : 0 < r) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (room : 2 * (Fintype.card I * r) ≤ p)
    (pairs : (∑ i, (paths i).length * ((paths i).length - 1)) ≤ r * (4 * (4*M/p) - 2) * lossBudget)
    (enough : 2*M + 5*lossBudget ≤ 5*(∑ i, (paths i).length)) (upper : (∑ i, (paths i).length) ≤ M) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 90*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let L := 4*M/p
  have width : 4 ≤ L := (Nat.le_div_iff_mul_le hp).mpr (Nat.mul_le_mul_left _ long)
  obtain ⟨part, loss⟩ := exists_clippedPartitionListPaths rPos (show 0 < L by omega) paths simple
  let pieces := partitionListPaths paths part
  let kept := clippedPartitionListPaths paths part L
  have coefficient : 0 < r * (4 * L - 2) := Nat.mul_pos rPos (by omega)
  have atMost : (∑ i, (paths i).length) - (∑ j, (kept j).length) ≤ lossBudget :=
    Nat.le_of_mul_le_mul_left (loss.trans pairs) coefficient
  have sub (j) : (kept j).Sublist (pieces j) := List.take_sublist L (pieces j)
  have keptSimple (j) : (kept j).Nodup :=
    (sub j).nodup (List.filter_sublist.nodup (simple (ofLex j).1))
  have legal : localOrderAdmissible half k kept := clippedPartitionListPaths_admissible paths part simple allowed
  have keptMass : (∑ j, (kept j).length) ≤ ∑ i, (paths i).length :=
    (sum_le_sum (fun j _ => (sub j).length_le)).trans (partitionListPaths_mass paths part simple).le
  have pieceCount : 2 * Fintype.card (I ×ₗ Fin r) ≤ p := by
    simpa only [Fintype.card_lex, Fintype.card_prod, Fintype.card_fin] using room
  exact regularization_list_frozen_of_length_capped_half_path_budget kept keptSimple legal size hn hp dense long
    pieceCount (fun j => List.length_take.trans_le (min_le_left _ _)) (keptMass.trans upper) (by omega)

/-- When clipping all paths would lose over seven fifteenths, retain only
the overlong rows and partition their vertices in common. A bound on
their ordered-pair count pays for the new clipping. The result applies
at every full cutoff and at half cutoffs through four. -/
theorem regularization_list_frozen_of_overlong_partition_pairs {half : Bool} {k n p r : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (size : half = true → k ≤ 4)
    (rPos : 0 < r) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (room : let M := ∑ i, (paths i).length
      let rows := univ.filter fun i => 4*M/p < (paths i).length
      2 * (rows.card * r) ≤ p)
    (pairs : let M := ∑ i, (paths i).length
      let L := 4*M/p
      let rows := univ.filter fun i => L < (paths i).length
      (∑ i ∈ rows, (paths i).length*((paths i).length-1)) ≤ r*(4*L-2)*(M/15)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 104*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let L := 4*M/p
  let T := listLengthExcess paths L
  let S := listMassAboveWidth paths L
  let rows := (univ : Finset (Fin p)).filter fun i => L < (paths i).length
  let chosen (i : rows) := paths i.val
  by_cases clipping : 15*T ≤ 7*M
  · exact regularization_list_frozen_of_small_length_excess paths simple allowed size hn hp dense long clipping
  have legal : localOrderAdmissible half k chosen := by
    cases half
    · change BridgeFree (ListBefore paths) k at allowed
      change BridgeFree (ListBefore chosen) k
      intro j limit
      exact ⟨fun b => (allowed limit).false (b.mapPaths Subtype.val Subtype.val_injective (fun _ _ _ step => step))⟩
    · change HalfBridgeFree (ListBefore paths) k at allowed
      change HalfBridgeFree (ListBefore chosen) k
      intro j limit b arrival
      exact allowed limit (b.mapPaths Subtype.val Subtype.val_injective (fun _ _ _ step => step)) arrival
  have count : 2*(Fintype.card rows*r) ≤ p := by simpa only [Fintype.card_coe] using room
  have pairSum : (∑ i : rows, (chosen i).length*((chosen i).length-1)) ≤ r*(4*L-2)*(M/15) := by
    have pairEq : (∑ i : rows, (chosen i).length*((chosen i).length-1)) =
        ∑ i ∈ rows, (paths i).length*((paths i).length-1) :=
      sum_attach rows (fun i => (paths i).length*((paths i).length-1))
    exact pairEq.le.trans pairs
  have sum : (∑ i : rows, (chosen i).length) = S := sum_attach rows (fun i => (paths i).length)
  have excess : T + rows.card * L = S := listLengthExcess_add_count_mul paths L
  have limit := Nat.div_mul_le_self M 15
  have lower : 2*M+5*(M/15) ≤ 5*(∑ i : rows, (chosen i).length) := by rw [sum]; omega
  have upper : (∑ i : rows, (chosen i).length) ≤ M := by
    rw [sum]
    exact sum_le_sum_of_subset (subset_univ rows)
  obtain ⟨n',nCap,p',pCap,clean,cleanSimple,good,mass,upperMass,caps⟩ :=
    regularization_list_frozen_by_half_budget_clipped_partition chosen (fun i => simple i.val)
      legal size rPos hn hp dense long count pairSum lower upper
  exact ⟨n',nCap,p',pCap,clean,cleanSimple,good,mass.trans (by omega),upperMass,caps⟩

end OnlineReachabilityPreservers
