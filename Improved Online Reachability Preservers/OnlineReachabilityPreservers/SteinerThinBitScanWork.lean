import OnlineReachabilityPreservers.SteinerThinBitLoadWork
import OnlineReachabilityPreservers.SteinerThinBitRoundingWork
import OnlineReachabilityPreservers.SteinerThinReplay

/-! Thin rounding on a supplied list of binary thresholds and load cells. -/

namespace OnlineReachabilityPreservers

/-- One reference arc and the words used to address its load and test its threshold. -/
structure BinaryThinThresholdRow (n : ℕ) where
  arc : Fin n × Fin n
  labels : List Bool × List Bool
  sample : List Bool

/-- The reference threshold row obtained by decoding the sample. -/
def BinaryThinThresholdRow.reference {n : ℕ} (row : BinaryThinThresholdRow n) : (Fin n × Fin n) × ℕ :=
  (row.arc,binaryWordValue row.sample)

private def thinBinaryRowPassesWithWork {n : ℕ} (base factor : List Bool) (cells : List (List Bool))
    (row : BinaryThinThresholdRow n) : Bool × ℕ :=
  let fetched := thinLoadAccessWithBinaryWork cells base row.labels.1 row.labels.2 none
  let result := thinThresholdTestWithBinaryWork row.sample factor (fetched.1.1.getD [])
  (result.1,fetched.2+result.2+5)

/-- The two costs for one row are fetching its load and comparing its binary threshold. -/
def binaryThinThresholdRowWorkBudget (n base labels sample factor payload : ℕ) : ℕ :=
  thinLoadAccessBinaryWorkBudget (n*n) base labels labels+thinThresholdTestBinaryWorkBudget sample factor payload+5

private theorem thinBinaryRowPassesWithWork_spec {n labelWidth sampleWidth loadWidth : ℕ}
    (table : FinThinLoadTable n) (base factor : List Bool) (cells : List (List Bool))
    (row : BinaryThinThresholdRow n) (encoded : EncodesThinLoadTable table cells loadWidth)
    (size : binaryWordValue base = n) (labels : BinaryThinArcMatches labelWidth row.labels row.arc)
    (sample : row.sample.length ≤ sampleWidth) :
    let out := thinBinaryRowPassesWithWork base factor cells row
    out.1 = decide (binaryWordValue row.sample < binaryWordValue factor*2^(table.read row.arc)) ∧
      out.2 ≤ binaryThinThresholdRowWorkBudget n base.length labelWidth sampleWidth factor.length loadWidth := by
  let fetched := thinLoadAccessWithBinaryWork cells base row.labels.1 row.labels.2 none
  let result := thinThresholdTestWithBinaryWork row.sample factor (fetched.1.1.getD [])
  obtain ⟨⟨load,member,found,decoded⟩,readWork⟩ := thinLoadAccessWithBinaryWork_read_decoded table cells
    binaryWordValue row.arc base row.labels.1 row.labels.2 encoded.1 size labels.1 labels.2.1
  obtain ⟨tested,testWork⟩ := thinThresholdTestWithBinaryWork_spec row.sample factor (fetched.1.1.getD [])
  change fetched.1.1 = some load at found
  change result.1 = _ at tested
  change result.2 ≤ thinThresholdTestBinaryWorkBudget row.sample.length factor.length (fetched.1.1.getD []).length at testWork
  rw [found,Option.getD_some,decoded] at tested
  rw [found,Option.getD_some,encoded.2 load member] at testWork
  have readBound := readWork.trans (thinLoadAccessBinaryWorkBudget_le labels.2.2.1 labels.2.2.2)
  have testBound : result.2 ≤ thinThresholdTestBinaryWorkBudget sampleWidth factor.length loadWidth := by
    apply testWork.trans
    unfold thinThresholdTestBinaryWorkBudget
    gcongr
  exact ⟨tested,Nat.add_le_add_right (Nat.add_le_add readBound testBound) 5⟩

@[specialize] private def collectPassingThinRowsWithWork {n : ℕ} {A : Type}
    (select : BinaryThinThresholdRow n → A) (base factor : List Bool) (cells : List (List Bool)) :
    List (BinaryThinThresholdRow n) → List A × ℕ
  | [] => ([],3)
  | row::rows =>
    let test := thinBinaryRowPassesWithWork base factor cells row
    let tail := collectPassingThinRowsWithWork select base factor cells rows
    (if test.1 then select row::tail.1 else tail.1,test.2+tail.2+5)

private theorem collectPassingThinRowsWithWork_spec {n labelWidth sampleWidth loadWidth : ℕ} {A : Type}
    (select : BinaryThinThresholdRow n → A)
    (table : FinThinLoadTable n) (base factor : List Bool) (cells : List (List Bool))
    (rows : List (BinaryThinThresholdRow n)) (encoded : EncodesThinLoadTable table cells loadWidth)
    (size : binaryWordValue base = n)
    (bounds : ∀ row ∈ rows, BinaryThinArcMatches labelWidth row.labels row.arc ∧ row.sample.length ≤ sampleWidth) :
    let out := collectPassingThinRowsWithWork select base factor cells rows
    out.1 = (rows.filter fun row => decide (binaryWordValue row.sample < binaryWordValue factor*2^(table.read row.arc))).map
      select ∧
    out.2 ≤ 3+rows.length*(binaryThinThresholdRowWorkBudget n base.length labelWidth sampleWidth factor.length loadWidth+5) := by
  induction rows with
  | nil => simp [collectPassingThinRowsWithWork]
  | cons row rows ih =>
    let test := thinBinaryRowPassesWithWork base factor cells row
    let tail := collectPassingThinRowsWithWork select base factor cells rows
    let budget := binaryThinThresholdRowWorkBudget n base.length labelWidth sampleWidth factor.length loadWidth
    obtain ⟨labels,sample⟩ := bounds row List.mem_cons_self
    obtain ⟨selected,rowWork⟩ := thinBinaryRowPassesWithWork_spec table base factor cells row encoded size labels sample
    obtain ⟨remaining,tailWork⟩ := ih (fun r inRows => bounds r (List.mem_cons_of_mem _ inRows))
    change test.1 = _ at selected
    change test.2 ≤ budget at rowWork
    change tail.2 ≤ 3+rows.length*(budget+5) at tailWork
    change (if test.1 then select row::tail.1 else tail.1) = _ ∧
      test.2+tail.2+5 ≤ 3+(rows.length+1)*(budget+5)
    refine ⟨?_,?_⟩
    · rw [selected,remaining,List.filter_cons]
      split <;> rfl
    · rw [Nat.add_mul,Nat.one_mul]
      omega

/-- Read and test each supplied threshold row, retaining the reference arc when it passes. -/
def roundBinaryThinThresholdRowsWithWork {n : ℕ} (base factor : List Bool) (cells : List (List Bool)) :
    List (BinaryThinThresholdRow n) → List (Fin n × Fin n) × ℕ
  | [] => ([],3)
  | row::rows =>
    let test := thinBinaryRowPassesWithWork base factor cells row
    let tail := roundBinaryThinThresholdRowsWithWork base factor cells rows
    (if test.1 then row.arc::tail.1 else tail.1,test.2+tail.2+5)

private theorem roundBinaryThinThresholdRowsWithWork_eq_collect {n : ℕ} (base factor : List Bool)
    (cells : List (List Bool)) (rows : List (BinaryThinThresholdRow n)) :
    roundBinaryThinThresholdRowsWithWork base factor cells rows =
      collectPassingThinRowsWithWork BinaryThinThresholdRow.arc base factor cells rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    rw [roundBinaryThinThresholdRowsWithWork,collectPassingThinRowsWithWork,ih]

/-- The output has the reference passing rows in their supplied order. -/
theorem roundBinaryThinThresholdRowsWithWork_spec {n labelWidth sampleWidth loadWidth : ℕ}
    (table : FinThinLoadTable n) (base factor : List Bool) (cells : List (List Bool))
    (rows : List (BinaryThinThresholdRow n)) (encoded : EncodesThinLoadTable table cells loadWidth)
    (size : binaryWordValue base = n)
    (bounds : ∀ row ∈ rows, BinaryThinArcMatches labelWidth row.labels row.arc ∧ row.sample.length ≤ sampleWidth) :
    let out := roundBinaryThinThresholdRowsWithWork base factor cells rows
    out.1 = (rows.filter fun row => decide (binaryWordValue row.sample < binaryWordValue factor*2^(table.read row.arc))).map
      BinaryThinThresholdRow.arc ∧
    out.2 ≤ 3+rows.length*(binaryThinThresholdRowWorkBudget n base.length labelWidth sampleWidth factor.length loadWidth+5) := by
  dsimp only
  rw [roundBinaryThinThresholdRowsWithWork_eq_collect]
  exact collectPassingThinRowsWithWork_spec BinaryThinThresholdRow.arc table base factor cells rows encoded size bounds

/-- The same scan retaining the supplied labels of each passing row. -/
def roundBinaryThinEncodedRowsWithWork {n : ℕ} (base factor : List Bool) (cells : List (List Bool)) :
    List (BinaryThinThresholdRow n) → List (List Bool × List Bool) × ℕ :=
  collectPassingThinRowsWithWork BinaryThinThresholdRow.labels base factor cells

/-- The passing encoded rows keep their labels, order, and multiplicity. -/
theorem roundBinaryThinEncodedRowsWithWork_spec {n labelWidth sampleWidth loadWidth : ℕ}
    (table : FinThinLoadTable n) (base factor : List Bool) (cells : List (List Bool))
    (rows : List (BinaryThinThresholdRow n)) (encoded : EncodesThinLoadTable table cells loadWidth)
    (size : binaryWordValue base = n)
    (bounds : ∀ row ∈ rows, BinaryThinArcMatches labelWidth row.labels row.arc ∧ row.sample.length ≤ sampleWidth) :
    let out := roundBinaryThinEncodedRowsWithWork base factor cells rows
    out.1 = (rows.filter fun row => decide (binaryWordValue row.sample < binaryWordValue factor*2^(table.read row.arc))).map
      BinaryThinThresholdRow.labels ∧
    out.2 ≤ 3+rows.length*(binaryThinThresholdRowWorkBudget n base.length labelWidth sampleWidth factor.length loadWidth+5) :=
  collectPassingThinRowsWithWork_spec BinaryThinThresholdRow.labels table base factor cells rows encoded size bounds

/-- On supplied encoded rows with distinct arcs, the binary scan returns
exactly the same rounded arc set as the existing thin list evaluator. -/
theorem roundBinaryThinThresholdRowsWithWork_refines {n labelWidth sampleWidth loadWidth : ℕ}
    (table : FinThinLoadTable n) (base factor : List Bool) (cells : List (List Bool))
    (rows : List (BinaryThinThresholdRow n)) (encoded : EncodesThinLoadTable table cells loadWidth)
    (size : binaryWordValue base = n)
    (bounds : ∀ row ∈ rows, BinaryThinArcMatches labelWidth row.labels row.arc ∧ row.sample.length ≤ sampleWidth)
    (unique : ((rows.map BinaryThinThresholdRow.reference).map Prod.fst).Nodup) :
    let out := roundBinaryThinThresholdRowsWithWork base factor cells rows
    out.1.toFinset = (roundThinThresholdListWithWordWork (rows.map BinaryThinThresholdRow.reference) unique
      (binaryWordValue factor) (fun arc => (table.read arc,0))).1 ∧
    out.2 ≤ 3+rows.length*(binaryThinThresholdRowWorkBudget n base.length labelWidth sampleWidth factor.length loadWidth+5) := by
  obtain ⟨selected,work⟩ := roundBinaryThinThresholdRowsWithWork_spec table base factor cells rows encoded size bounds
  refine ⟨?_,work⟩
  rw [roundThinThresholdListWithWordWork_spec]
  apply Finset.ext
  intro arc
  rw [selected]
  simp only [roundedFromThinThresholdRows,Finset.mem_image,Finset.mem_filter,List.mem_toFinset,List.mem_map,
    List.mem_filter,decide_eq_true_eq]
  constructor
  · rintro ⟨row,⟨member,passes⟩,equal⟩
    exact ⟨row.reference,⟨⟨row,member,rfl⟩,passes⟩,equal⟩
  · rintro ⟨_,⟨⟨row,member,rfl⟩,passes⟩,equal⟩
    exact ⟨row,⟨member,passes⟩,equal⟩

end OnlineReachabilityPreservers
