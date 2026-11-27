import OnlineReachabilityPreservers.FullThreeLiteralFeasibility
import OnlineReachabilityPreservers.FrozenFullNearCutoff

/-! Incidence-mass transfer from finite full cutoffs to exclusion at every size. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- Keeping only the highest-mass original rows retains the row-support
fraction. The rows stay intact, including their singleton rows. -/
theorem literal_full_all_mass_of_row_cutoff_ratio {n p cutoff a b : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (well : ∀ i, paths i ≠ [] ∧ (paths i).Nodup) (free : BridgeFree (Before paths) cutoff)
    (ratio : a ≤ b) (near : a*p ≤ b*cutoff) :
    ∃ q ≤ p, ∃ witness : Fin q → List (Fin n), Function.Injective witness ∧
      (∀ i, witness i ≠ [] ∧ (witness i).Nodup) ∧ (∀ d, IsEmpty (Bridge (Before witness) d)) ∧
      a*(∑ i, (paths i).length) ≤ b*(∑ i, (witness i).length) ∧
      (∑ i, (witness i).length) ≤ ∑ i, (paths i).length := by
  have fits : a*(univ : Finset (Fin p)).card ≤ b*cutoff := by simpa using near
  obtain ⟨B,subset,small,retained⟩ := trim_weights_ratio univ (fun i => (paths i).length) ratio fits
  let order := (Fintype.equivFinOfCardEq (Fintype.card_coe B)).symm
  let label (i : Fin B.card) : Fin p := (order i).val
  have labelInjective : Function.Injective label := Subtype.val_injective.comp order.injective
  let witness (i : Fin B.card) := paths (label i)
  have weight : (∑ i, (witness i).length) = ∑ i ∈ B, (paths i).length :=
    (Equiv.sum_comp order (fun i : B => (paths i.val).length)).trans (B.sum_coe_sort (fun i => (paths i).length))
  have rowBudget : B.card ≤ p := by simpa using card_le_univ B
  refine ⟨B.card,rowBudget,witness,distinct.comp labelInjective,fun i => well (label i),?_,?_,?_⟩
  · intro d
    refine ⟨fun bridge => ?_⟩
    have size : d+2 ≤ B.card := by simpa using SourceAudit.bridge_path_count_le bridge
    exact (free (size.trans small)).false (bridge.mapPaths label labelInjective (fun _ _ _ step => step))
  · rw [weight]
    exact retained
  · rw [weight]
    exact sum_le_sum_of_subset_of_nonneg subset (fun _ _ _ => Nat.zero_le _)

private theorem full_all_literal_long_rows {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (all : ∀ d, IsEmpty (Bridge (Before paths) d)) :
    ∃ q ≤ p, ∃ kept : Fin q → List (Fin n), Function.Injective kept ∧
      (∀ i, kept i ≠ [] ∧ (kept i).Nodup) ∧ (∀ d, IsEmpty (Bridge (Before kept) d)) ∧
      (∑ i, (kept i).length) ≤ (∑ i, (paths i).length) ∧
      (∑ i, (paths i).length) ≤ (∑ i, (kept i).length)+p := by
  let long := (univ : Finset (Fin p)).filter fun i => 2 ≤ (paths i).length
  let order := (Fintype.equivFinOfCardEq (Fintype.card_coe long)).symm
  let label (i : Fin long.card) := (order i).val
  let kept (i : Fin long.card) := paths (label i)
  have rows (i : Fin long.card) : (kept i).Nodup ∧ 2 ≤ (kept i).length :=
    ⟨simple _,(mem_filter.mp (order i).property).2⟩
  have keptAll (d : ℕ) : IsEmpty (Bridge (Before kept) d) :=
    ⟨fun bridge => (all d).false (bridge.mapPaths label (Subtype.val_injective.comp order.injective)
      (fun _ _ _ step => step))⟩
  have keptTwo : BridgeFree (Before kept) 2 := fun d _ => keptAll d
  have keptMass : (∑ i, (kept i).length) = ∑ i ∈ long, (paths i).length :=
    (Equiv.sum_comp order (fun i : long => (paths i.val).length)).trans
      (long.sum_coe_sort (fun i => (paths i).length))
  have count : long.card ≤ p := by simpa using card_le_univ long
  refine ⟨long.card,count,kept,nontrivial_halfFree_paths_injective (fun i => (rows i).1)
    (fun i => (rows i).2) le_rfl keptTwo.halfFree,
    fun i => ⟨List.length_pos_iff.mp (by have := (rows i).2; omega),(rows i).1⟩,keptAll,?_,?_⟩
  · rw [keptMass]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
  · rw [keptMass,← sum_add_sum_compl long (fun i => (paths i).length)]
    apply Nat.add_le_add_left
    calc
      _ ≤ ∑ _ ∈ longᶜ, 1 := sum_le_sum fun i outside => by
        have short : ¬ 2 ≤ (paths i).length := fun big =>
          (mem_compl.mp outside) (mem_filter.mpr ⟨mem_univ _,big⟩)
        omega
      _ = (longᶜ : Finset (Fin p)).card := by simp
      _ ≤ p := by simpa using card_le_univ (longᶜ : Finset (Fin p))

/-- At a full cutoff of at least three, simple literal families admit an
all-size full-free literal witness within both budgets, losing at most
twice the smaller-support restriction factor. This is a mass comparison. -/
theorem literal_full_all_mass_of_cutoff_ratio {n p cutoff a b : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (well : ∀ i, paths i ≠ [] ∧ (paths i).Nodup) (free : BridgeFree (Before paths) cutoff)
    (three : 3 ≤ cutoff) (ratio : a ≤ b) (near : a*min n p ≤ b*cutoff) :
    ∃ q ≤ p, ∃ witness : Fin q → List (Fin n), Function.Injective witness ∧
      (∀ i, witness i ≠ [] ∧ (witness i).Nodup) ∧ (∀ d, IsEmpty (Bridge (Before witness) d)) ∧
      a*(∑ i, (paths i).length) ≤ (2*b)*(∑ i, (witness i).length) ∧
      (∑ i, (witness i).length) ≤ ∑ i, (paths i).length := by
  let M := ∑ i, (paths i).length
  have pLeMass : p ≤ M := by
    simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,mul_one] using
      (sum_le_sum (s := (univ : Finset (Fin p))) (fun i _ => List.length_pos_iff.mpr (well i).1) :
        (∑ _i : Fin p, (1:ℕ)) ≤ ∑ i, (paths i).length)
  have capacity := literal_full_path_count_le_balanced_bipartite paths distinct (fun i => (well i).1)
    (fun i => (well i).2) free three
  obtain ⟨kept,sub,all,weighted⟩ := fullBridgeFree_subrows_mass_of_cutoff_ratio paths (fun i => (well i).2) free ratio near
  have keptSimple (i : Fin p) : (kept i).Nodup := (sub i).nodup (well i).2
  have keptBound : (∑ i, (kept i).length) ≤ M := sum_le_sum fun i _ => (sub i).length_le
  obtain ⟨q,bound,long,unique,longWell,longAll,longBound,loses⟩ := full_all_literal_long_rows kept keptSimple all
  have weightedLoss := weighted.trans (Nat.mul_le_mul_left _ loses)
  by_cases largeLong : p ≤ ∑ i, (long i).length
  · refine ⟨q,bound,long,unique,longWell,longAll,?_,longBound.trans keptBound⟩
    rw [Nat.mul_comm 2 b,Nat.mul_assoc,Nat.two_mul]
    exact weightedLoss.trans (Nat.mul_le_mul_left _ (by omega))
  · obtain ⟨r,rFits,base,baseDistinct,baseWell,baseAll,baseMass⟩ := literal_full_all_mass_at_path_budget capacity
    refine ⟨r,rFits,base,baseDistinct,baseWell,baseAll,?_,baseMass.le.trans pLeMass⟩
    rw [baseMass,Nat.mul_comm 2 b,Nat.mul_assoc,Nat.two_mul]
    exact weightedLoss.trans (Nat.mul_le_mul_left _ (by omega))

end OnlineReachabilityPreservers
