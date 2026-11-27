import OnlineReachabilityPreservers.SharedCapacityClipping

/-! The optimal deletion count for two fixed partitions. -/

namespace OnlineReachabilityPreservers.FiberClipping

open Finset

variable {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]
  [Fintype B] [Fintype C]

/-- Enumerate shared deletions that fit both original excess partitions. -/
def sharedDeletionChoices (items : Finset A) (left : A → B) (right : A → C) (d l : ℕ) :
    Finset (Finset A) :=
  items.powerset.filter fun shared =>
    (∀ b, (shared.filter fun a => left a = b).card ≤ excess items left d b) ∧
    (∀ c, (shared.filter fun a => right a = c).card ≤ excess items right l c)

omit [DecidableEq A] in
theorem mem_sharedDeletionChoices {items shared : Finset A}
    {left : A → B} {right : A → C} {d l : ℕ} :
    shared ∈ sharedDeletionChoices items left right d l ↔
      shared ⊆ items ∧
      (∀ b, (shared.filter fun a => left a = b).card ≤ excess items left d b) ∧
      (∀ c, (shared.filter fun a => right a = c).card ≤ excess items right l c) := by
  simp only [sharedDeletionChoices, mem_filter, mem_powerset]

/-- The maximum number of deletions that can count toward both sets of
fixed excess quotas. The empty set is always a candidate. -/
def optimalSharedDeletionCount (items : Finset A) (left : A → B) (right : A → C) (d l : ℕ) : ℕ :=
  (sharedDeletionChoices items left right d l).sup Finset.card

omit [DecidableEq A] in
theorem exists_optimalSharedDeletion (items : Finset A) (left : A → B) (right : A → C)
    (d l : ℕ) :
    ∃ shared ∈ sharedDeletionChoices items left right d l,
      shared.card = optimalSharedDeletionCount items left right d l := by
  have empty : ∅ ∈ sharedDeletionChoices items left right d l :=
    mem_sharedDeletionChoices.mpr ⟨empty_subset _, by simp, by simp⟩
  obtain ⟨shared, allowed, attained⟩ :=
    exists_mem_eq_sup _ ⟨∅, empty⟩ (Finset.card : Finset A → ℕ)
  exact ⟨shared, allowed, attained.symm⟩

omit [DecidableEq A] in
theorem card_le_optimalSharedDeletionCount {items shared : Finset A}
    {left : A → B} {right : A → C} {d l : ℕ}
    (allowed : shared ∈ sharedDeletionChoices items left right d l) :
    shared.card ≤ optimalSharedDeletionCount items left right d l :=
  le_sup allowed

omit [DecidableEq A] in
/-- The shared credit is bounded by each of the two separate deletion counts. -/
theorem optimalSharedDeletionCount_le_excesses (items : Finset A) (left : A → B)
    (right : A → C) (d l : ℕ) :
    optimalSharedDeletionCount items left right d l ≤ totalExcess items left d ∧
      optimalSharedDeletionCount items left right d l ≤ totalExcess items right l := by
  obtain ⟨shared, allowed, exactCard⟩ := exists_optimalSharedDeletion items left right d l
  obtain ⟨_, fitLeft, fitRight⟩ := mem_sharedDeletionChoices.mp allowed
  rw [← exactCard]
  constructor
  · rw [card_eq_sum_card_fiberwise (f := left) (t := univ) (fun a _ => mem_univ (left a))]
    exact sum_le_sum (fun b _ => fitLeft b)
  · rw [card_eq_sum_card_fiberwise (f := right) (t := univ) (fun a _ => mem_univ (right a))]
    exact sum_le_sum (fun c _ => fitRight c)

/-- The minimum cost for bringing both fixed partitions within their widths. -/
def minimumFixedDeletionCount (items : Finset A) (left : A → B) (right : A → C) (d l : ℕ) : ℕ :=
  totalExcess items left d + totalExcess items right l - optimalSharedDeletionCount items left right d l

/-- A budget suffices exactly when it covers the original two excesses
less the largest shared-deletion credit. -/
theorem exists_capped_deletion_iff_minimumFixedDeletionCount
    (items : Finset A) (left : A → B) (right : A → C) (d l cost : ℕ) :
    (∃ deleted : Finset A, deleted ⊆ items ∧ deleted.card ≤ cost ∧
      (∀ b, ((items \ deleted).filter fun a => left a = b).card ≤ d) ∧
      (∀ c, ((items \ deleted).filter fun a => right a = c).card ≤ l)) ↔
    minimumFixedDeletionCount items left right d l ≤ cost := by
  rw [exists_capped_deletion_iff]
  unfold minimumFixedDeletionCount
  constructor
  · rintro ⟨shared, within, paid, fitLeft, fitRight⟩
    have upper := card_le_optimalSharedDeletionCount
      (mem_sharedDeletionChoices.mpr ⟨within, fitLeft, fitRight⟩)
    omega
  · intro enough
    obtain ⟨shared, allowed, exactCard⟩ := exists_optimalSharedDeletion items left right d l
    obtain ⟨within, fitLeft, fitRight⟩ := mem_sharedDeletionChoices.mp allowed
    exact ⟨shared, within, by omega, fitLeft, fitRight⟩

/-- The explicit minimum cost is achieved by a deletion set. -/
theorem exists_minimumFixedDeletion (items : Finset A) (left : A → B)
    (right : A → C) (d l : ℕ) :
    ∃ deleted : Finset A, deleted ⊆ items ∧
      deleted.card = minimumFixedDeletionCount items left right d l ∧
      (∀ b, ((items \ deleted).filter fun a => left a = b).card ≤ d) ∧
      (∀ c, ((items \ deleted).filter fun a => right a = c).card ≤ l) := by
  obtain ⟨deleted, within, budget, fitLeft, fitRight⟩ :=
    (exists_capped_deletion_iff_minimumFixedDeletionCount items left right d l _).mpr le_rfl
  have optimal :=
    (exists_capped_deletion_iff_minimumFixedDeletionCount items left right d l deleted.card).mp
      ⟨deleted, within, le_rfl, fitLeft, fitRight⟩
  exact ⟨deleted, within, Nat.le_antisymm budget optimal, fitLeft, fitRight⟩

end OnlineReachabilityPreservers.FiberClipping
