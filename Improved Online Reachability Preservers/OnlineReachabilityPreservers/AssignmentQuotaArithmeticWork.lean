import OnlineReachabilityPreservers.DeterministicListWork
import OnlineReachabilityPreservers.IndexSensitive

/-! Count the integer square-root scan and quota doubling used by path assignments. -/

namespace OnlineReachabilityPreservers

open Finset

/-- Search an explicit range for the first integer whose successor square
exceeds the input, with a charge for every test and list cell. -/
def natSqrtWithWordWork (n : ℕ) : ℕ × ℕ :=
  let found := leastWhereWithChecks (fun k => (decide (n < (k+1)^2),5)) (List.range (n+1))
  (found.1.getD n,found.2+14*(n+1)+5)

theorem natSqrtWithWordWork_spec (n : ℕ) :
    let out := natSqrtWithWordWork n
    out.1 = n.sqrt ∧ out.2 ≤ 20*(n+1)+5 := by
  let P := fun k => n < (k+1)^2
  let keys := List.range (n+1)
  let domain := keys.toFinset.filter P
  obtain ⟨same, work⟩ := leastWhereWithChecks_spec (fun k => (decide (P k),5)) P keys 5
    (fun _ _ => rfl) (fun _ _ => le_rfl)
  have inside : n.sqrt ∈ domain := by
    apply mem_filter.mpr
    exact ⟨List.mem_toFinset.mpr (List.mem_range.mpr (Nat.lt_succ_of_le (Nat.sqrt_le_self n))), Nat.lt_succ_sqrt' n⟩
  obtain ⟨least, chosen⟩ := least?_some ⟨_,inside⟩
  have right : least ≤ n.sqrt := least?_le chosen inside
  have left : n.sqrt ≤ least := Nat.le_of_lt_succ
    (Nat.sqrt_lt'.mpr (mem_filter.mp (least?_mem chosen)).2)
  constructor
  · change (leastWhereWithChecks (fun k => (decide (P k),5)) keys).1.getD n = _
    rw [same, show keys.toFinset.filter P = domain from rfl, chosen, le_antisymm right left]
    rfl
  · change (leastWhereWithChecks (fun k => (decide (P k),5)) keys).2+14*(n+1)+5 ≤ _
    have len : keys.length = n+1 := List.length_range
    rw [len] at work
    exact (Nat.add_le_add_right (Nat.add_le_add_right work _) _).trans_eq (by ring)

private def coverByDoublingWithWordWork (needed : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, quota => (quota,1)
  | steps+1, quota =>
    if needed ≤ quota then (quota,4)
    else
      let rest := coverByDoublingWithWordWork needed steps (2*quota)
      (rest.1,rest.2+6)

private theorem coverByDoublingWithWordWork_cost (needed fuel quota : ℕ) :
    (coverByDoublingWithWordWork needed fuel quota).2 ≤ 1+6*fuel := by
  induction fuel generalizing quota with
  | zero => simp [coverByDoublingWithWordWork]
  | succ k ih =>
    rw [coverByDoublingWithWordWork]
    split
    · change 4 ≤ 1+6*(k+1)
      omega
    · have bound := ih (2*quota)
      change (coverByDoublingWithWordWork needed k (2*quota)).2+6 ≤ 1+6*(k+1)
      omega

private theorem coverByDoublingWithWordWork_exact {base : ℕ} (positive : 0 < base) (i fuel level : ℕ)
    (before : level ≤ indexLevel base i) (enough : indexLevel base i ≤ level+fuel) :
    (coverByDoublingWithWordWork (i+1) fuel (dyadicQuota base level)).1 =
      dyadicQuota base (indexLevel base i) := by
  induction fuel generalizing level with
  | zero =>
    have exactLevel : level = indexLevel base i := le_antisymm before (by simpa using enough)
    simp [coverByDoublingWithWordWork, exactLevel]
  | succ k ih =>
    rw [coverByDoublingWithWordWork]
    split
    · rename_i covered
      have exactLevel : level = indexLevel base i := le_antisymm before (indexLevel_le_of_cover positive covered)
      rw [exactLevel]
    · rename_i missing
      have next : level+1 ≤ indexLevel base i := by
        apply Nat.succ_le_of_lt
        refine lt_of_le_of_ne before ?_
        intro equal
        exact missing (equal.symm ▸ indexLevel_covers positive i)
      have continued := ih (level+1) next (by omega)
      rw [dyadicQuota_succ] at continued
      exact continued


/-- Start from a positive base and double until the next request count is covered. -/
def indexQuotaWithWordWork (base i : ℕ) : ℕ × ℕ :=
  coverByDoublingWithWordWork (i+1) (i+1) base

theorem indexQuotaWithWordWork_spec (base i : ℕ) (positive : 0 < base) :
    let out := indexQuotaWithWordWork base i
    out.1 = dyadicQuota base (indexLevel base i) ∧ out.2 ≤ 1+6*(i+1) := by
  have feasible : indexLevel base i ≤ 0+(i+1) :=
    (indexLevel_le_log2_succ positive i).trans (by have := Nat.log2_le_self i; omega)
  have solved := coverByDoublingWithWordWork_exact positive i (i+1) 0 (Nat.zero_le _) feasible
  exact ⟨by simpa only [indexQuotaWithWordWork, dyadicQuota, pow_zero, Nat.mul_one] using solved,
    coverByDoublingWithWordWork_cost (i+1) (i+1) base⟩

theorem indexQuota_le_add {base : ℕ} (positive : 0 < base) (i : ℕ) :
    dyadicQuota base (indexLevel base i) ≤ base+2*(i+1) := by
  have bound := finalQuota_le positive (p := i+1) (Nat.succ_pos i)
  exact (by simpa only [Nat.add_sub_cancel] using bound :
    dyadicQuota base (indexLevel base i) ≤ max base (2*(i+1))).trans
      (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))

end OnlineReachabilityPreservers
