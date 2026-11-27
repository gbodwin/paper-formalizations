import OnlineReachabilityPreservers.UnbalancedBridgeExtrema

/-! Starting-average full witnesses for low-mass literal half families. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- A low-mass literal half family has a distinct nonempty full witness
at every cutoff simultaneously. Both budgets and the four caps use the
starting data. -/
theorem regularization_literal_half_full_all_of_low_mass {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup) (half : HalfBridgeFree (Before paths) k) (two : 2 ≤ k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length)
    (low : (∑ i, (paths i).length) ≤ 8*max n p) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
      (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ (∀ cutoff, BridgeFree (Before rows) cutoff) ∧
      M ≤ 8*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  let M := ∑ i, (paths i).length
  let fullCutoff := max 2 n
  have long : p ≤ M := calc
    _ = ∑ _ : Fin p, (1:ℕ) := by simp
    _ ≤ _ := sum_le_sum (fun i _ => List.length_pos_iff.mpr (valid i).1)
  obtain ⟨v,vFit,q,qFit,rows,injective,nonempty,simple,free,retain,upper,caps⟩ :
      ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
        (∀ i, rows i ≠ []) ∧ (∀ i, (rows i).Nodup) ∧ BridgeFree (Before rows) fullCutoff ∧
        M ≤ 8*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
    by_cases short : M ≤ 4*p
    · exact regularization_list_frozen_distinct_of_small_mean fullCutoff paths distinct
        (fun i => (valid i).1) (fun i => (valid i).2) half two hn hp dense long short
    · obtain ⟨v,vFit,q,qFit,rows,simple,free,retain,upper,caps⟩ :=
        regularization_list_frozen_low_mass_at_cutoff fullCutoff paths
          (fun i => (valid i).2) half two hn hp dense long low
      obtain ⟨injective,nonempty⟩ := frozen_length_distinct_of_large_mean simple free.halfFree
        (le_max_left 2 n) hp (lt_of_not_ge short) caps
      exact ⟨v,vFit,q,qFit,rows,injective,nonempty,simple,free,retain,upper,caps⟩
  have all (cutoff : ℕ) : BridgeFree (Before rows) cutoff := by
    intro d _
    refine ⟨fun bridge => ?_⟩
    have count : d+2 ≤ v := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ bridge.distinctVertices
    exact (free (count.trans (vFit.trans (le_max_right 2 n)))).false bridge
  exact ⟨v,vFit,q,qFit,rows,injective,fun i => ⟨nonempty i,simple i⟩,all,retain,upper,caps⟩

/-- For feasible literal half budgets, the small-side or unbalanced
pair-count conditions give the starting-average conclusion of the
literal full cleaning claim at every input cutoff of at least two. -/
theorem localOrderDistinctExtremal_frozen_full_all_of_unbalanced_budgets {n p k : ℕ}
    (hn : 0 < n) (hp : 0 < p) (two : 2 ≤ k)
    (shape : min n p ≤ 8 ∨ UnbalancedBridgeBudgets n p k 8)
    (feasible : ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (Before paths) k) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (Before paths) k ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → HalfBridgeFree (Before other) k →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
        (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ (∀ cutoff, BridgeFree (Before rows) cutoff) ∧
        M ≤ 8*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  obtain ⟨paths,distinct,valid,half,maximal,dense,_⟩ := localOrderDistinctExtremal_isDense (k := k) true hp feasible
  have low : (∑ i, (paths i).length) ≤ 8*max n p := by
    rcases shape with small | unbalanced
    · have product : (∑ i, (paths i).length) ≤ p*n := calc
        _ ≤ ∑ _ : Fin p, n := sum_le_sum (fun i _ => by
          rw [← List.toFinset_card_of_nodup (valid i).2]
          simpa only [Fintype.card_fin] using card_le_univ (paths i).toFinset)
        _ = _ := by simp
      have budgets : p*n = min n p*max n p := by
        rcases le_total n p with h | h
        · simp [min_eq_left h,max_eq_right h,Nat.mul_comm]
        · simp [min_eq_right h,max_eq_left h]
      exact product.trans (budgets.trans_le (Nat.mul_le_mul_right _ small))
    · exact halfBridgeFree_mass_le_of_unbalanced_budgets paths (fun i => (valid i).2)
        half two hn hp (by decide) unbalanced
  exact ⟨paths,distinct,valid,half,maximal,
    regularization_literal_half_full_all_of_low_mass paths distinct valid half two hn hp dense low⟩

end OnlineReachabilityPreservers
