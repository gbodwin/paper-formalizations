import OnlineReachabilityPreservers.SteinerBitOrders

/-! Count the full unit operations of one stored-array index lookup. -/

namespace OnlineReachabilityPreservers

/-- Midpoint search with one charge for the stop or each comparison step.
Array access, key comparisons and natural arithmetic use unit charges. -/
def arrayLowerBoundWithWordWork {A : Type*} [LinearOrder A] (values : Array A) (key : A) :
    (fuel lo hi : ℕ) → hi ≤ values.size → ℕ × ℕ
  | 0,lo,_,_ => (lo,4)
  | fuel+1,lo,hi,cap =>
    if room : lo < hi then
      let middle := lo+(hi-lo)/2
      let value := values[middle]'(by omega)
      let found := if value < key then
        arrayLowerBoundWithWordWork values key fuel (middle+1) hi cap
      else arrayLowerBoundWithWordWork values key fuel lo middle (by omega)
      (found.1,found.2+24)
    else (lo,4)

theorem arrayLowerBoundWithWordWork_spec {A : Type*} [LinearOrder A]
    (values : Array A) (key : A) (fuel lo hi : ℕ) (cap : hi ≤ values.size) :
    let out := arrayLowerBoundWithWordWork values key fuel lo hi cap
    let old := arrayLowerBoundWithChecks values key fuel lo hi cap
    out.1 = old.1 ∧ out.2 = 24*old.2+4 := by
  induction fuel generalizing lo hi with
  | zero => simp [arrayLowerBoundWithWordWork,arrayLowerBoundWithChecks]
  | succ fuel ih =>
    by_cases room : lo < hi
    · let mid := lo+(hi-lo)/2
      have found : mid < values.size := by dsimp only [mid]; omega
      by_cases check : values[mid]'found < key
      · obtain ⟨same,work⟩ := ih (mid+1) hi cap
        simp only [arrayLowerBoundWithWordWork,arrayLowerBoundWithChecks,dite_eq_left room,mid,
          ite_eq_left check,same,work,Nat.mul_succ]
        trivial
      · have midCap : mid ≤ values.size := Nat.le_of_lt found
        obtain ⟨same,work⟩ := ih lo mid midCap
        simp only [arrayLowerBoundWithWordWork,arrayLowerBoundWithChecks,dite_eq_left room,mid,
          ite_eq_right check,same,work,Nat.mul_succ]
        trivial
    · simp [arrayLowerBoundWithWordWork,arrayLowerBoundWithChecks,room]

theorem sortedArrayRankWithWordWork_spec {A : Type*} [LinearOrder A]
    (keys : Finset A) (array : Array A) (same : array = keys.sort.toArray)
    (fuel : ℕ) (fuelEq : fuel = array.size.size) (key : keys) :
    let out := arrayLowerBoundWithWordWork array key.val fuel 0 array.size le_rfl
    out.1 = keys.sort.idxOf key.val ∧ out.2 ≤ 24*keys.card.size+4 := by
  obtain ⟨value,steps⟩ := arrayLowerBoundWithWordWork_spec array key.val fuel 0 array.size le_rfl
  have checked := binarySortedIndexWithChecks_spec keys key
  dsimp only
  rw [value,steps,fuelEq,same]
  exact ⟨checked.1,Nat.add_le_add_right (Nat.mul_le_mul_left 24 checked.2) 4⟩

end OnlineReachabilityPreservers
