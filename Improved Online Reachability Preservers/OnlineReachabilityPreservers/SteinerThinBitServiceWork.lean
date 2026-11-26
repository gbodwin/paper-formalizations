import OnlineReachabilityPreservers.SteinerBinaryReachWork
import OnlineReachabilityPreservers.SteinerThinBitScanWork

/-! The service decision for one thin rounding trial on supplied binary rows. -/

namespace OnlineReachabilityPreservers

/-- Round the stored rows and test the demand using the labels already in
those rows. The Boolean is true when the rounded arcs miss the demand. -/
def roundBinaryThinServiceWithWork {n : ℕ} (base factor : List Bool) (cells : List (List Bool))
    (rows : List (BinaryThinThresholdRow n)) (source target : List Bool) (depth : ℕ) : Bool × ℕ :=
  let rounded := roundBinaryThinEncodedRowsWithWork base factor cells rows
  let found := binaryReachTestListWithWork rounded.1 source target depth
  (!found.1,rounded.2+found.2+5)

/-- Bit-list work for testing a rounded trial with the given input bounds. -/
def binaryThinServiceWorkBudget
    (n rows base labels samples factor payload depth : ℕ) : ℕ :=
  let keyPart := (5*labels+8)*n
  8+rows*(binaryThinThresholdRowWorkBudget n base labels samples factor payload+5)+
    (2+depth*(5+rows*(14+2*keyPart))+keyPart+5)

/-- The binary trial decides reachability in the rounded graph at any supplied
depth. A single encoding per vertex ensures matching of structural bit lists. -/
theorem roundBinaryThinServiceWithWork_spec {n labelWidth sampleWidth loadWidth : ℕ}
    (table : FinThinLoadTable n) (base factor : List Bool) (cells : List (List Bool))
    (rows : List (BinaryThinThresholdRow n)) (encoded : EncodesThinLoadTable table cells loadWidth)
    (size : binaryWordValue base = n)
    (bounds : ∀ row ∈ rows, BinaryThinArcMatches labelWidth row.labels row.arc ∧ row.sample.length ≤ sampleWidth)
    (code : Fin n → List Bool) (injective : Function.Injective code) (bounded : ∀ v, (code v).length ≤ labelWidth)
    (labels : ∀ row ∈ rows, row.labels = (code row.arc.1,code row.arc.2))
    (source target : Fin n) (depth : ℕ) :
    let passed := roundBinaryThinThresholdRowsWithWork base factor cells rows
    let out := roundBinaryThinServiceWithWork base factor cells rows (code source) (code target) depth
    out.1 = decide (source ∉ reachIn passed.1.toFinset target depth) ∧
      out.2 ≤ binaryThinServiceWorkBudget n rows.length base.length labelWidth sampleWidth factor.length loadWidth depth := by
  let passed := roundBinaryThinThresholdRowsWithWork base factor cells rows
  let rounded := roundBinaryThinEncodedRowsWithWork base factor cells rows
  let selected := rows.filter (fun row => decide (binaryWordValue row.sample < binaryWordValue factor*2^(table.read row.arc)))
  obtain ⟨reference,_⟩ := roundBinaryThinThresholdRowsWithWork_spec table base factor cells rows encoded size bounds
  obtain ⟨binary,spent⟩ := roundBinaryThinEncodedRowsWithWork_spec table base factor cells rows encoded size bounds
  change passed.1 = selected.map BinaryThinThresholdRow.arc at reference
  change rounded.1 = selected.map BinaryThinThresholdRow.labels at binary
  have same : rounded.1 = binaryEncodeArcs code passed.1 := by
    rw [binary,reference,binaryEncodeArcs,List.map_map]
    apply List.map_congr_left
    intro row h
    exact labels row (List.mem_filter.mp h).1
  have count : passed.1.length ≤ rows.length := by
    rw [reference,List.length_map]
    exact List.length_filter_le _ _
  obtain ⟨found,work⟩ := binaryReachTestListWithWork_spec code injective labelWidth bounded passed.1 source target depth
  obtain ⟨serves,_⟩ := reachTestListWithWordWork_spec passed.1 source target depth
  simp only [Fintype.card_fin] at work
  let bitTest := binaryReachTestListWithWork (binaryEncodeArcs code passed.1) (code source) (code target) depth
  change (!((binaryReachTestListWithWork rounded.1 (code source) (code target) depth).1)) = _ ∧
    rounded.2+(binaryReachTestListWithWork rounded.1 (code source) (code target) depth).2+5 ≤ _
  rw [same]
  refine ⟨?_,?_⟩
  · change (!bitTest.1) = _
    rw [show bitTest.1 = _ from found,serves,← decide_not]
  · change bitTest.2 ≤ _ at work
    let keyPart := (5*labelWidth+8)*n
    have cost : bitTest.2 ≤ 2+depth*(5+rows.length*(14+2*keyPart))+keyPart+5 := by
      apply work.trans
      change 2+depth*(5+passed.1.length*(14+2*keyPart))+keyPart+5 ≤ _
      gcongr
    let scanBudget := rows.length*
      (binaryThinThresholdRowWorkBudget n base.length labelWidth sampleWidth factor.length loadWidth+5)
    let reachBudget := 2+depth*(5+rows.length*(14+2*keyPart))+keyPart+5
    have total : (3+scanBudget)+reachBudget+5 =
        binaryThinServiceWorkBudget n rows.length base.length labelWidth sampleWidth factor.length loadWidth depth := by
      change (3+scanBudget)+reachBudget+5 = 8+scanBudget+reachBudget
      omega
    exact (Nat.add_le_add_right (Nat.add_le_add spent cost) 5).trans_eq total

/-- At the reference depth with one row for each encoded arc, the result
agrees with the service flag used by the existing thin replay. -/
theorem roundBinaryThinServiceWithWork_refines {n labelWidth sampleWidth loadWidth : ℕ}
    (table : FinThinLoadTable n) (base factor : List Bool) (cells : List (List Bool))
    (rows : List (BinaryThinThresholdRow n)) (encoded : EncodesThinLoadTable table cells loadWidth)
    (size : binaryWordValue base = n)
    (bounds : ∀ row ∈ rows, BinaryThinArcMatches labelWidth row.labels row.arc ∧ row.sample.length ≤ sampleWidth)
    (code : Fin n → List Bool) (injective : Function.Injective code) (bounded : ∀ v, (code v).length ≤ labelWidth)
    (labels : ∀ row ∈ rows, row.labels = (code row.arc.1,code row.arc.2))
    (unique : ((rows.map BinaryThinThresholdRow.reference).map Prod.fst).Nodup) (demand : Fin n × Fin n) :
    let out := roundBinaryThinServiceWithWork base factor cells rows (code demand.1) (code demand.2) n
    let reference := roundThinServiceWithWordWork (rows.map BinaryThinThresholdRow.reference) unique
      (binaryWordValue factor) (fun arc => (table.read arc,0)) n demand
    out.1 = reference.1.2.1 ∧
      out.2 ≤ binaryThinServiceWorkBudget n rows.length base.length labelWidth sampleWidth factor.length loadWidth n := by
  obtain ⟨correct,work⟩ := roundBinaryThinServiceWithWork_spec table base factor cells rows encoded size bounds
    code injective bounded labels demand.1 demand.2 n
  obtain ⟨graph,_⟩ := roundBinaryThinThresholdRowsWithWork_refines table base factor cells rows encoded size bounds unique
  obtain ⟨value,_⟩ := roundThinServiceWithWordWork_spec (rows.map BinaryThinThresholdRow.reference) unique
    (binaryWordValue factor) (fun arc => (table.read arc,0)) n (by simp) demand
  have same := congrArg (fun result : Arcs (Fin n) × Bool × ℕ => result.2.1) value
  simp only [reachInWithArcInspections_spec] at same
  refine ⟨correct.trans ?_,work⟩
  rw [same,graph]

end OnlineReachabilityPreservers
