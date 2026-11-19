module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Nat.Size
import all Init.Data.List.Sort.Impl

/-! Count comparisons in the merge schedule used by Lean's finite-set sort. -/

public section

namespace OnlineReachabilityPreservers

open List.MergeSort.Internal

private def mergeWithChecks {A : Type*} (le : A → A → Bool) : List A → List A → List A × ℕ
  | [], ys => (ys,0)
  | x::xs, [] => (x::xs,0)
  | x::xs, y::ys =>
    if le x y then
      let next := mergeWithChecks le xs (y::ys)
      (x::next.1,next.2+1)
    else
      let next := mergeWithChecks le (x::xs) ys
      (y::next.1,next.2+1)
termination_by xs ys => xs.length + ys.length
decreasing_by all_goals simp

private theorem mergeWithChecks_spec {A : Type*} (le : A → A → Bool) (xs ys : List A) :
    (mergeWithChecks le xs ys).1 = List.merge xs ys le ∧
      (mergeWithChecks le xs ys).2 ≤ xs.length+ys.length := by
  cases xs with
  | nil => simp [mergeWithChecks]
  | cons x xs =>
    cases ys with
    | nil => simp [mergeWithChecks]
    | cons y ys =>
      rw [mergeWithChecks, List.merge]
      split
      · have rest := mergeWithChecks_spec le xs (y::ys)
        simp only [List.length_cons]
        constructor
        · exact congrArg (x::·) rest.1
        · simp only [List.length_cons] at rest
          omega
      · have rest := mergeWithChecks_spec le (x::xs) ys
        simp only [List.length_cons]
        constructor
        · exact congrArg (y::·) rest.1
        · simp only [List.length_cons] at rest
          omega
termination_by xs.length + ys.length
decreasing_by all_goals simp

private def mergeSortWithChecks {A : Type*} (le : A → A → Bool) (reverse : Bool) :
    {n : ℕ} → {xs : List A // xs.length = n} → List A × ℕ
  | 0, ⟨[],_⟩ => ([],0)
  | 1, ⟨[x],_⟩ => ([x],0)
  | n+2, xs =>
    if reverse then
      let (left,right) := splitRevInTwo' xs
      let leftOutput := mergeSortWithChecks le false left
      let rightOutput := mergeSortWithChecks le true right
      let merged := mergeWithChecks le rightOutput.1 leftOutput.1
      (merged.1,leftOutput.2+rightOutput.2+merged.2)
    else
      let (left,right) := splitRevInTwo xs
      let leftOutput := mergeSortWithChecks le true left
      let rightOutput := mergeSortWithChecks le false right
      let merged := mergeWithChecks le leftOutput.1 rightOutput.1
      (merged.1,leftOutput.2+rightOutput.2+merged.2)
termination_by n _ => n
decreasing_by all_goals omega

private theorem mergeSortWithChecks_spec {A : Type*} (le : A → A → Bool) (reverse : Bool)
    {n : ℕ} (xs : {xs : List A // xs.length = n}) (depth : ℕ) (fits : n ≤ 2^depth) :
    (mergeSortWithChecks le reverse xs).1 =
      (if reverse then mergeSortTR₂.run' le xs else mergeSortTR₂.run le xs) ∧
    (mergeSortWithChecks le reverse xs).1.length = n ∧
    (mergeSortWithChecks le reverse xs).2 ≤ n*depth := by
  cases n with
  | zero =>
    have empty := List.length_eq_zero_iff.mp xs.property
    obtain ⟨xs,length⟩ := xs
    dsimp only at empty
    subst xs
    cases reverse <;> simp [mergeSortWithChecks, mergeSortTR₂.run, mergeSortTR₂.run']
  | succ n =>
    cases n with
    | zero =>
      obtain ⟨x,theList⟩ := List.length_eq_one_iff.mp xs.property
      obtain ⟨xs,length⟩ := xs
      dsimp only at theList
      subst xs
      cases reverse <;> simp [mergeSortWithChecks, mergeSortTR₂.run, mergeSortTR₂.run']
    | succ n =>
      cases depth with
      | zero => simp at fits
      | succ depth =>
        have small : (n+1+1)/2 ≤ 2^depth := by rw [Nat.pow_succ] at fits; omega
        have large : (n+1+1+1)/2 ≤ 2^depth := by rw [Nat.pow_succ] at fits; omega
        cases reverse with
        | false =>
          let halves := splitRevInTwo xs
          let l := halves.1
          let r := halves.2
          have left := mergeSortWithChecks_spec le true l depth large
          have right := mergeSortWithChecks_spec le false r depth small
          simp only [Bool.false_eq_true, ite_false, ite_true] at left right
          have merged := mergeWithChecks_spec le (mergeSortWithChecks le true l).1 (mergeSortWithChecks le false r).1
          rw [left.2.1,right.2.1] at merged
          simp only [mergeSortWithChecks, mergeSortTR₂.run, Bool.false_eq_true, ite_false]
          change (mergeWithChecks le (mergeSortWithChecks le true l).1 (mergeSortWithChecks le false r).1).1 =
              mergeTR (mergeSortTR₂.run' le l) (mergeSortTR₂.run le r) le ∧
            (mergeWithChecks le (mergeSortWithChecks le true l).1 (mergeSortWithChecks le false r).1).1.length = n+1+1 ∧
            (mergeSortWithChecks le true l).2+(mergeSortWithChecks le false r).2+
              (mergeWithChecks le (mergeSortWithChecks le true l).1 (mergeSortWithChecks le false r).1).2 ≤ (n+1+1)*(depth+1)
          refine ⟨?_,?_,?_⟩
          · rw [merged.1,left.1,right.1, ← merge_eq_mergeTR]
          · rw [merged.1, List.length_merge, left.2.1, right.2.1]
            omega
          · have cap := Nat.add_le_add (Nat.add_le_add left.2.2 right.2.2) merged.2
            rw [← Nat.add_mul, show (n+1+1+1)/2+(n+1+1)/2 = n+1+1 by omega, ← Nat.mul_succ] at cap
            exact cap
        | true =>
          let halves := splitRevInTwo' xs
          let l := halves.1
          let r := halves.2
          have left := mergeSortWithChecks_spec le false l depth small
          have right := mergeSortWithChecks_spec le true r depth large
          simp only [Bool.false_eq_true, ite_false, ite_true] at left right
          have merged := mergeWithChecks_spec le (mergeSortWithChecks le true r).1 (mergeSortWithChecks le false l).1
          rw [right.2.1,left.2.1] at merged
          simp only [mergeSortWithChecks, mergeSortTR₂.run', ite_true]
          change (mergeWithChecks le (mergeSortWithChecks le true r).1 (mergeSortWithChecks le false l).1).1 =
              mergeTR (mergeSortTR₂.run' le r) (mergeSortTR₂.run le l) le ∧
            (mergeWithChecks le (mergeSortWithChecks le true r).1 (mergeSortWithChecks le false l).1).1.length = n+1+1 ∧
            (mergeSortWithChecks le false l).2+(mergeSortWithChecks le true r).2+
              (mergeWithChecks le (mergeSortWithChecks le true r).1 (mergeSortWithChecks le false l).1).2 ≤ (n+1+1)*(depth+1)
          refine ⟨?_,?_,?_⟩
          · rw [merged.1,left.1,right.1, ← merge_eq_mergeTR]
          · rw [merged.1, List.length_merge, right.2.1, left.2.1]
            omega
          · have cap := Nat.add_le_add (Nat.add_le_add left.2.2 right.2.2) merged.2
            rw [← Nat.add_mul, show (n+1+1)/2+(n+1+1+1)/2 = n+1+1 by omega,
              show (n+1+1+1)/2+(n+1+1)/2 = n+1+1 by omega, ← Nat.mul_succ] at cap
            exact cap
termination_by n
decreasing_by all_goals omega

/-- Count comparator calls made by the merge schedule used by compiled Lean list sorting. -/
def listSortWithChecks {A : Type*} (le : A → A → Bool) (xs : List A) : List A × ℕ :=
  mergeSortWithChecks le false ⟨xs,rfl⟩

/-- The metered schedule has the same output as the native merge sort and
uses at most list length times its bit length in comparator calls. -/
theorem listSortWithChecks_spec {A : Type*} (le : A → A → Bool) (xs : List A) :
    (listSortWithChecks le xs).1 = List.mergeSort xs le ∧
      (listSortWithChecks le xs).2 ≤ xs.length*xs.length.size := by
  obtain ⟨same,_,bound⟩ := mergeSortWithChecks_spec le false ⟨xs,rfl⟩
    xs.length.size (Nat.le_of_lt (Nat.lt_size_self _))
  rw [mergeSort_eq_mergeSortTR₂]
  exact ⟨same,bound⟩

/-- Counting the comparison schedule on any list representative gives the
canonical set order and the same length-based cap. -/
theorem listSortWithChecks_finset {A : Type*} [LinearOrder A] (values : Finset A) (entries : List A)
    (representative : (entries : Multiset A) = values.val) :
    let out := listSortWithChecks (fun a b => decide (a ≤ b)) entries
    out.1 = values.sort ∧ out.2 ≤ values.card*values.card.size := by
  obtain ⟨sorted,bound⟩ := listSortWithChecks_spec (fun a b => decide (a ≤ b)) entries
  have length : entries.length = values.card := by
    simpa only [Multiset.coe_card, Finset.card_def] using congrArg Multiset.card representative
  refine ⟨?_,?_⟩
  · rw [sorted, ← Multiset.coe_sort (r := (· ≤ ·)), representative]
    rfl
  · simpa only [length] using bound

end OnlineReachabilityPreservers
