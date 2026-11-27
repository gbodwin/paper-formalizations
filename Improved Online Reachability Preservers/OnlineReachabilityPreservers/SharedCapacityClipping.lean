import OnlineReachabilityPreservers.Basic

/-! Count deletions that reduce excess in two fixed partitions. -/

namespace OnlineReachabilityPreservers.FiberClipping

open Finset

variable {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-- Excess over the width in a class of the original partition. -/
def excess (items : Finset A) (label : A → B) (width : ℕ) (b : B) : ℕ :=
  (items.filter fun a => label a = b).card - width

/-- Sum the original excess over all classes. -/
def totalExcess [Fintype B] (items : Finset A) (label : A → B) (width : ℕ) : ℕ :=
  ∑ b, excess items label width b

private theorem filter_of_sdiff (items deleted : Finset A) (label : A → B) (b : B) :
    ((items \ deleted).filter fun a => label a = b) =
      ((items.filter fun a => label a = b) \ (deleted.filter fun a => label a = b)) := by
  ext a
  simp only [mem_filter, mem_sdiff]
  tauto

private theorem bounded_after_deletion_iff {items deleted : Finset A} (within : deleted ⊆ items)
    (label : A → B) (width : ℕ) (b : B) :
    ((items \ deleted).filter fun a => label a = b).card ≤ width ↔
      excess items label width b ≤ (deleted.filter fun a => label a = b).card := by
  have sub : (deleted.filter fun a => label a = b) ⊆ (items.filter fun a => label a = b) :=
    filter_subset_filter _ within
  rw [filter_of_sdiff, card_sdiff_of_subset sub]
  unfold excess
  omega

private theorem exists_fiber_counts [Fintype B] {initial available : Finset A}
    (sub : initial ⊆ available) (label : A → B) (target : B → ℕ)
    (lower : ∀ b, (initial.filter fun a => label a = b).card ≤ target b)
    (upper : ∀ b, target b ≤ (available.filter fun a => label a = b).card) :
    ∃ chosen : Finset A, initial ⊆ chosen ∧ chosen ⊆ available ∧
      (∀ b, (chosen.filter fun a => label a = b).card = target b) ∧
      chosen.card = ∑ b, target b := by
  classical
  let old (b : B) := initial.filter fun a => label a = b
  let possible (b : B) := available.filter fun a => label a = b
  have extension (b : B) :
      ∃ add : Finset A, add ⊆ possible b \ old b ∧ add.card = target b - (old b).card := by
    apply exists_subset_card_eq
    rw [card_sdiff_of_subset (filter_subset_filter _ sub)]
    exact Nat.sub_le_sub_right (upper b) _
  choose extra extraSub extraCard using extension
  let part (b : B) := old b ∪ extra b
  have partWithin (b : B) : part b ⊆ possible b :=
    union_subset (filter_subset_filter _ sub) ((extraSub b).trans sdiff_subset)
  have partCard (b : B) : (part b).card = target b := by
    have disjoint : Disjoint (old b) (extra b) :=
      Finset.disjoint_sdiff.mono_right (extraSub b)
    change (old b ∪ extra b).card = target b
    rw [card_union_of_disjoint disjoint, extraCard b]
    exact Nat.add_sub_of_le (lower b)
  let chosen := (univ : Finset B).biUnion part
  have selected (b : B) : (chosen.filter fun a => label a = b) = part b := by
    ext a
    constructor
    · intro on
      obtain ⟨inChosen, hasLabel⟩ := mem_filter.mp on
      obtain ⟨c, _, inPart⟩ := mem_biUnion.mp inChosen
      have same := ((mem_filter.mp (partWithin c inPart)).2).symm.trans hasLabel
      exact same ▸ inPart
    · intro on
      exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨b, mem_univ _, on⟩, (mem_filter.mp (partWithin b on)).2⟩
  have cardByFiber (b : B) : (chosen.filter fun a => label a = b).card = target b := by
    rw [selected, partCard]
  refine ⟨chosen, ?_, ?_, cardByFiber, ?_⟩
  · intro a on
    exact mem_biUnion.mpr ⟨label a, mem_univ _, mem_union_left _ (mem_filter.mpr ⟨on, rfl⟩)⟩
  · intro a on
    obtain ⟨c, _, inPart⟩ := mem_biUnion.mp on
    exact (mem_filter.mp (partWithin c inPart)).1
  · rw [card_eq_sum_card_fiberwise (f := label) (t := univ) (fun a _ => mem_univ (label a))]
    exact sum_congr rfl (fun b _ => cardByFiber b)

/-- The two fixed partitions can be brought within their widths with at most
`cost` deletions exactly when enough deletions can be charged to both
excess sums. A shared deletion consumes one unit from each class's
original excess budget. -/
theorem exists_capped_deletion_iff [Fintype B] [Fintype C]
    (items : Finset A) (left : A → B) (right : A → C) (d l cost : ℕ) :
    (∃ deleted : Finset A, deleted ⊆ items ∧ deleted.card ≤ cost ∧
      (∀ b, ((items \ deleted).filter fun a => left a = b).card ≤ d) ∧
      (∀ c, ((items \ deleted).filter fun a => right a = c).card ≤ l)) ↔
    (∃ shared : Finset A, shared ⊆ items ∧
      totalExcess items left d + totalExcess items right l ≤ cost + shared.card ∧
      (∀ b, (shared.filter fun a => left a = b).card ≤ excess items left d b) ∧
      (∀ c, (shared.filter fun a => right a = c).card ≤ excess items right l c)) := by
  constructor
  · rintro ⟨deleted, within, costBound, fitsLeft, fitsRight⟩
    obtain ⟨chosenLeft, _, leftSub, leftCounts, leftTotal⟩ := exists_fiber_counts
      (initial := ∅) (empty_subset deleted) left (excess items left d)
      (by simp) (fun b => (bounded_after_deletion_iff within left d b).mp (fitsLeft b))
    obtain ⟨chosenRight, _, rightSub, rightCounts, rightTotal⟩ := exists_fiber_counts
      (initial := ∅) (empty_subset deleted) right (excess items right l)
      (by simp) (fun c => (bounded_after_deletion_iff within right l c).mp (fitsRight c))
    let shared := chosenLeft ∩ chosenRight
    have unionBound : (chosenLeft ∪ chosenRight).card ≤ cost :=
      (card_le_card (union_subset leftSub rightSub)).trans costBound
    have accounting : totalExcess items left d + totalExcess items right l ≤ cost + shared.card := by
      rw [totalExcess, totalExcess, ← leftTotal, ← rightTotal, ← card_union_add_card_inter]
      exact Nat.add_le_add_right unionBound _
    refine ⟨shared, inter_subset_left.trans (leftSub.trans within), accounting, ?_, ?_⟩
    · intro b
      exact (card_le_card (filter_subset_filter _ inter_subset_left)).trans_eq (leftCounts b)
    · intro c
      exact (card_le_card (filter_subset_filter _ inter_subset_right)).trans_eq (rightCounts c)
  · rintro ⟨shared, within, costBound, fitsLeft, fitsRight⟩
    obtain ⟨chosenLeft, sharedLeft, leftSub, leftCounts, leftTotal⟩ :=
      exists_fiber_counts within left (excess items left d) fitsLeft (fun b => Nat.sub_le _ _)
    obtain ⟨chosenRight, sharedRight, rightSub, rightCounts, rightTotal⟩ :=
      exists_fiber_counts within right (excess items right l) fitsRight (fun c => Nat.sub_le _ _)
    let deleted := chosenLeft ∪ chosenRight
    have sub : deleted ⊆ items := union_subset leftSub rightSub
    have savings : shared.card ≤ (chosenLeft ∩ chosenRight).card :=
      card_le_card (subset_inter sharedLeft sharedRight)
    have count : deleted.card ≤ cost := by
      dsimp only [totalExcess] at costBound
      rw [← leftTotal, ← rightTotal, ← card_union_add_card_inter] at costBound
      change deleted.card + (chosenLeft ∩ chosenRight).card ≤ cost + shared.card at costBound
      omega
    refine ⟨deleted, sub, count, ?_, ?_⟩
    · intro b
      apply (bounded_after_deletion_iff sub left d b).mpr
      rw [← leftCounts b]
      exact card_le_card (filter_subset_filter _ subset_union_left)
    · intro c
      apply (bounded_after_deletion_iff sub right l c).mpr
      rw [← rightCounts c]
      exact card_le_card (filter_subset_filter _ subset_union_right)

omit [DecidableEq A] in
/-- Restricting the underlying set cannot increase excess at a fixed partition. -/
theorem totalExcess_mono [Fintype B] {small large : Finset A}
    (sub : small ⊆ large) (label : A → B) (width : ℕ) :
    totalExcess small label width ≤ totalExcess large label width := by
  unfold totalExcess excess
  exact sum_le_sum (fun _ _ => Nat.sub_le_sub_right
    (card_le_card (filter_subset_filter _ sub)) _)

/-- Deleting at most the original excess in every class reduces the
excess of the fixed partition by exactly the number of deletions. -/
theorem totalExcess_sdiff_add_card_of_fits [Fintype B] {items deleted : Finset A}
    (within : deleted ⊆ items) (label : A → B) (width : ℕ)
    (fits : ∀ b, (deleted.filter fun a => label a = b).card ≤ excess items label width b) :
    totalExcess (items \ deleted) label width + deleted.card = totalExcess items label width := by
  have count : deleted.card = ∑ b, (deleted.filter fun a => label a = b).card :=
    card_eq_sum_card_fiberwise (t := univ) (fun a _ => mem_univ (label a))
  rw [totalExcess, totalExcess, count, ← sum_add_distrib]
  apply sum_congr rfl
  intro b _
  have small : (deleted.filter fun a => label a = b) ⊆ (items.filter fun a => label a = b) :=
    filter_subset_filter _ within
  have bound := fits b
  unfold excess at bound ⊢
  rw [filter_of_sdiff, card_sdiff_of_subset small]
  omega

/-- Refining a partition cannot increase its total excess at a fixed width. -/
theorem totalExcess_le_of_refinement [Fintype B] [Fintype C]
    (items : Finset A) (fine : A → C) (coarse : A → B) (width : ℕ)
    (refines : ∀ ⦃x y⦄, x ∈ items → y ∈ items → fine x = fine y → coarse x = coarse y) :
    totalExcess items fine width ≤ totalExcess items coarse width := by
  obtain ⟨deleted, _, within, quota, exactMass⟩ := exists_fiber_counts (initial := ∅)
    (empty_subset items) coarse (excess items coarse width) (by simp) (fun b => Nat.sub_le _ _)
  have coarseCaps (b : B) : ((items \ deleted).filter fun a => coarse a = b).card ≤ width :=
    (bounded_after_deletion_iff within coarse width b).mpr (quota b).ge
  have fineCaps (c : C) : ((items \ deleted).filter fun a => fine a = c).card ≤ width := by
    let fiber := (items \ deleted).filter fun a => fine a = c
    by_cases empty : fiber = ∅
    · change fiber.card ≤ width
      simp [empty]
    · obtain ⟨sample, selected⟩ := Finset.nonempty_iff_ne_empty.mpr empty
      have onSample : sample ∈ items := (mem_sdiff.mp (mem_filter.mp selected).1).1
      have inFiber : fine sample = c := (mem_filter.mp selected).2
      have subset : fiber ⊆ (items \ deleted).filter (fun a => coarse a = coarse sample) := by
        intro a on
        obtain ⟨survives, fineA⟩ := mem_filter.mp on
        exact mem_filter.mpr ⟨survives, refines (mem_sdiff.mp survives).1 onSample (fineA.trans inFiber.symm)⟩
      exact (card_le_card subset).trans (coarseCaps (coarse sample))
  have counted : deleted.card = ∑ c, (deleted.filter fun a => fine a = c).card :=
    card_eq_sum_card_fiberwise (t := univ) (fun a _ => mem_univ (fine a))
  calc
    _ ≤ ∑ c, (deleted.filter fun a => fine a = c).card :=
      sum_le_sum (fun c _ => (bounded_after_deletion_iff within fine width c).mp (fineCaps c))
    _ = deleted.card := counted.symm
    _ = _ := exactMass

end OnlineReachabilityPreservers.FiberClipping
