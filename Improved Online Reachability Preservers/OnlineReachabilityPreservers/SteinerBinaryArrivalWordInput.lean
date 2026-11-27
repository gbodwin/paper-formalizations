import OnlineReachabilityPreservers.SteinerBinaryArrivals
import OnlineReachabilityPreservers.SteinerBinaryInputGuard

/-! Decode only the current demand of the sampled arrival solver. -/

namespace OnlineReachabilityPreservers

/-- The first component is the typed solver's next state on acceptance.
The second component charges the input check and decoding separately. -/
def finSteinerBinaryArrivalStepFromWords {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height width : ℕ) (seed : Vector Bool (steinerBitBudget G height))
    (state : FinSteinerBinaryArrivalState n) (words : List Bool × List Bool) :
    Option (FinSteinerBinaryArrivalState n) × ℕ :=
  let decoded := decodeCheckedBinaryFinArcRowsWithWork (n := n) width [words]
  let updated := match decoded.1 with
    | some [demand] => some (finSteinerBinaryArrivalStepFromSeed G raw same height seed state demand)
    | _ => none
  (updated,decoded.2+4)

/-- Accepted words cause exactly one typed arrival with their decoded
endpoint values. A rejected row produces no next state. -/
theorem finSteinerBinaryArrivalStepFromWords_eq_some_iff {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height width : ℕ)
    (seed : Vector Bool (steinerBitBudget G height)) (state updated : FinSteinerBinaryArrivalState n)
    (words : List Bool × List Bool) :
    (finSteinerBinaryArrivalStepFromWords G raw same height width seed state words).1 = some updated ↔
      ∃ demand : Fin n × Fin n, words.1.length ≤ width ∧ words.2.length ≤ width ∧
        demand.1.val = binaryWordValue words.1 ∧ demand.2.val = binaryWordValue words.2 ∧
        updated = finSteinerBinaryArrivalStepFromSeed G raw same height seed state demand := by
  let decoded := decodeCheckedBinaryFinArcRowsWithWork (n := n) width [words]
  change (match decoded.1 with
    | some [demand] => some (finSteinerBinaryArrivalStepFromSeed G raw same height seed state demand)
    | _ => none) = some updated ↔ _
  constructor
  · intro accepted
    cases decision : decoded.1 with
    | none => simp [decision] at accepted
    | some rows =>
      cases rows with
      | nil => simp [decision] at accepted
      | cons demand rest =>
        cases rest with
        | cons second rest => simp [decision] at accepted
        | nil =>
          obtain ⟨fits,values⟩ := (decodeCheckedBinaryFinArcRowsWithWork_eq_some_iff width [words] [demand]).mp decision
          have lengths := fits words List.mem_cons_self
          have sameValues := (List.cons.inj values).1
          have sameState : finSteinerBinaryArrivalStepFromSeed G raw same height seed state demand = updated := by
            simpa only [decision,Option.some.injEq] using accepted
          exact ⟨demand,lengths.1,lengths.2,congrArg Prod.fst sameValues,congrArg Prod.snd sameValues,sameState.symm⟩
  · rintro ⟨demand,left,right,valueLeft,valueRight,equal⟩
    have success : decoded.1 = some [demand] := by
      apply (decodeCheckedBinaryFinArcRowsWithWork_eq_some_iff width [words] [demand]).mpr
      refine ⟨?_,?_⟩
      · intro word here
        simp only [List.mem_singleton] at here
        subst word
        exact ⟨left,right⟩
      · simp only [List.map_cons,List.map_nil,valueLeft,valueRight]
    rw [success,equal]

/-- The encoded arrival accepts exactly the width- and range-valid pairs. -/
theorem finSteinerBinaryArrivalStepFromWords_some_iff_valid {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height width : ℕ)
    (seed : Vector Bool (steinerBitBudget G height)) (state : FinSteinerBinaryArrivalState n)
    (words : List Bool × List Bool) :
    (∃ next, (finSteinerBinaryArrivalStepFromWords G raw same height width seed state words).1 = some next) ↔
      words.1.length ≤ width ∧ words.2.length ≤ width ∧
        binaryWordValue words.1 < n ∧ binaryWordValue words.2 < n := by
  constructor
  · rintro ⟨next,accepted⟩
    obtain ⟨demand,left,right,leftValue,rightValue,_⟩ :=
      (finSteinerBinaryArrivalStepFromWords_eq_some_iff G raw same height width seed state next words).mp accepted
    exact ⟨left,right,leftValue ▸ demand.1.isLt,rightValue ▸ demand.2.isLt⟩
  · rintro ⟨left,right,leftValue,rightValue⟩
    let demand : Fin n × Fin n := (⟨binaryWordValue words.1,leftValue⟩,⟨binaryWordValue words.2,rightValue⟩)
    refine ⟨finSteinerBinaryArrivalStepFromSeed G raw same height seed state demand,?_⟩
    exact (finSteinerBinaryArrivalStepFromWords_eq_some_iff G raw same height width seed state _ words).mpr
      ⟨demand,left,right,rfl,rfl,rfl⟩

/-- Written with the finite-label encoding, the new input step agrees
with the existing typed step for every stored history and sampled word. -/
theorem finSteinerBinaryArrivalStepFromWords_refines {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height width : ℕ) (fits : n ≤ 2^width)
    (seed : Vector Bool (steinerBitBudget G height)) (state : FinSteinerBinaryArrivalState n) (demand : Fin n × Fin n) :
    (finSteinerBinaryArrivalStepFromWords G raw same height width seed state
      (binaryFinLabel width demand.1,binaryFinLabel width demand.2)).1 =
        some (finSteinerBinaryArrivalStepFromSeed G raw same height seed state demand) := by
  obtain ⟨leftValue,leftLength⟩ := binaryFinLabel_spec width fits demand.1
  obtain ⟨rightValue,rightLength⟩ := binaryFinLabel_spec width fits demand.2
  exact (finSteinerBinaryArrivalStepFromWords_eq_some_iff G raw same height width seed state _ _).mpr
    ⟨demand,leftLength.le,rightLength.le,leftValue.symm,rightValue.symm,rfl⟩

/-- The input overhead uses the raw bit count and the one-row decoding
budget. This also bounds rejected arrivals. -/
theorem finSteinerBinaryArrivalStepFromWords_work_le {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height width : ℕ)
    (seed : Vector Bool (steinerBitBudget G height)) (state : FinSteinerBinaryArrivalState n)
    (words : List Bool × List Bool) :
    (finSteinerBinaryArrivalStepFromWords G raw same height width seed state words).2 ≤
      binaryEndpointWidthCheckBudget width [words] + binaryFinArcDecodingWorkBudget 1 width + 7 := by
  have decode := decodeCheckedBinaryFinArcRowsWithWork_work_le (n := n) width [words]
  change (decodeCheckedBinaryFinArcRowsWithWork (n := n) width [words]).2 + 4 ≤ _
  simp only [List.length_singleton] at decode
  omega

end OnlineReachabilityPreservers
