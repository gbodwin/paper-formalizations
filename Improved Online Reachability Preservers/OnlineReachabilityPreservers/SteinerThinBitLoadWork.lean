import OnlineReachabilityPreservers.SteinerBinaryIndexedWork

/-! Thin load increments on explicit binary words stored in a list. -/

namespace OnlineReachabilityPreservers

/-- Increment a fixed-width word, discarding a carry beyond its final bit. -/
def incrementFixedBinaryWordWithWork : List Bool → List Bool × ℕ
  | [] => ([],3)
  | false::tail => (true::tail,4)
  | true::tail =>
    let next := incrementFixedBinaryWordWithWork tail
    (false::next.1,next.2+5)

theorem incrementFixedBinaryWordWithWork_spec (word : List Bool) :
    let out := incrementFixedBinaryWordWithWork word
    out.1.length = word.length ∧ out.2 ≤ 5*word.length+3 ∧
      (binaryWordValue word+1 < 2^word.length → binaryWordValue out.1 = binaryWordValue word+1) := by
  induction word with
  | nil =>
    decide
  | cons bit tail ih =>
    cases bit with
    | false =>
      change tail.length+1 = tail.length+1 ∧ 4 ≤ 5*(tail.length+1)+3 ∧
        (_ → 1+2*binaryWordValue tail = 0+2*binaryWordValue tail+1)
      exact ⟨rfl,by omega,fun _ => by omega⟩
    | true =>
      let next := incrementFixedBinaryWordWithWork tail
      obtain ⟨width,work,value⟩ := ih
      change next.1.length = tail.length at width
      change next.2 ≤ 5*tail.length+3 at work
      change next.1.length+1 = tail.length+1 ∧ next.2+5 ≤ 5*(tail.length+1)+3 ∧
        (1+2*binaryWordValue tail+1 < 2^(tail.length+1) →
          0+2*binaryWordValue next.1 = 1+2*binaryWordValue tail+1)
      refine ⟨congrArg (·+1) width,by omega,fun fits => ?_⟩
      rw [pow_succ] at fits
      have incremented : binaryWordValue next.1 = binaryWordValue tail+1 := value (by omega)
      omega

/-- The list stores fixed-width words in the existing table order. -/
def EncodesThinLoadTable {n : ℕ} (table : FinThinLoadTable n) (cells : List (List Bool)) (width : ℕ) : Prop :=
  cells.map binaryWordValue = table.val.toList ∧ ∀ word ∈ cells, word.length = width

/-- Compute the address once, read its word, and replace it by an increment.
An address outside the list leaves the list unchanged. -/
def bumpBinaryThinLoadWithWork (cells : List (List Bool)) (base row column : List Bool) :
    List (List Bool) × ℕ :=
  let address := binaryPairAddressWithWork base row column
  let old := accessBinaryIndexedListWithWork none address.1 cells
  match old.1.1 with
  | none => (cells,address.2+old.2+3)
  | some word =>
    let incremented := incrementFixedBinaryWordWithWork word
    let fresh := accessBinaryIndexedListWithWork (some incremented.1) address.1 cells
    (fresh.1.2,address.2+old.2+incremented.2+fresh.2+7)

/-- Charge the address, two walks of the cell list, and one fixed-width increment. -/
def binaryThinLoadBumpWorkBudget (cells base labels payload : ℕ) : ℕ :=
  binaryPairAddressWorkBudget base labels labels+
    2*(3+cells*(9*(labels+labels*(base+2)+1)+13))+(5*payload+3)+7

/-- Incrementing one load updates the actual thin table at the same arc
when its increment fits within the payload width. -/
theorem bumpBinaryThinLoadWithWork_refines {n width labels : ℕ} (table : FinThinLoadTable n)
    (cells : List (List Bool)) (arc : Fin n × Fin n) (base row column : List Bool)
    (encoded : EncodesThinLoadTable table cells width) (size : binaryWordValue base = n)
    (first : binaryWordValue row = arc.1.val) (second : binaryWordValue column = arc.2.val)
    (rowWidth : row.length ≤ labels) (columnWidth : column.length ≤ labels)
    (fits : table.read arc+1 < 2^width) :
    let out := bumpBinaryThinLoadWithWork cells base row column
    EncodesThinLoadTable (table.write arc (table.read arc+1)) out.1 width ∧
      out.2 ≤ binaryThinLoadBumpWorkBudget (n*n) base.length labels width := by
  let address := binaryPairAddressWithWork base row column
  let read := accessBinaryIndexedListWithWork none address.1 cells
  let pos := binaryWordValue address.1
  let walkBudget := 3+(n*n)*(9*(labels+labels*(base.length+2)+1)+13)
  obtain ⟨addr,addrLength,addrWork⟩ := binaryPairAddressWithWork_spec base row column
  change pos = binaryWordValue column+binaryWordValue base*binaryWordValue row at addr
  rw [size,first,second] at addr
  change address.1.length ≤ column.length+row.length*(base.length+2)+1 at addrLength
  have boundedAddress : address.1.length ≤ labels+labels*(base.length+2)+1 :=
    addrLength.trans (by gcongr)
  have boundedAddressWork : address.2 ≤ binaryPairAddressWorkBudget base.length labels labels := by
    apply addrWork.trans
    unfold binaryPairAddressWorkBudget
    gcongr
    exact binaryMultiplicationWorkBudget_le le_rfl rowWidth
  have cellsSize : cells.length = n*n := by
    simpa only [List.length_map,Array.length_toList,table.property] using congrArg List.length encoded.1
  have walk (work : ℕ) (bound : work ≤ 3+cells.length*(9*address.1.length+13)) : work ≤ walkBudget := by
    apply bound.trans
    unfold walkBudget
    rw [cellsSize]
    gcongr
  obtain ⟨old,_,oldWork⟩ := accessBinaryIndexedListWithWork_spec (none : Option (List Bool)) address.1 cells
  change read.1.1 = cells[pos]? at old
  have inside : arc.2.val+n*arc.1.val < table.val.size := table.property.symm ▸ (finProdFinEquiv arc).isLt
  have oldValue : read.1.1.map binaryWordValue = some (table.read arc) := by
    rw [old,← List.getElem?_map,encoded.1,addr,Array.getElem?_toList,Array.getElem?_eq_getElem inside]
    rfl
  change (let out := match read.1.1 with
    | none => (cells,address.2+read.2+3)
    | some word =>
      let inc := incrementFixedBinaryWordWithWork word
      let updated := accessBinaryIndexedListWithWork (some inc.1) address.1 cells
      (updated.1.2,address.2+read.2+inc.2+updated.2+7)
    EncodesThinLoadTable (table.write arc (table.read arc+1)) out.1 width ∧
      out.2 ≤ binaryThinLoadBumpWorkBudget (n*n) base.length labels width)
  cases found : read.1.1 with
  | none => simp [found] at oldValue
  | some word =>
    rw [found] at oldValue
    have readValue : binaryWordValue word = table.read arc := Option.some.inj oldValue
    have wordWidth := encoded.2 word (List.mem_of_getElem? (old.symm.trans found))
    let inc := incrementFixedBinaryWordWithWork word
    let updated := accessBinaryIndexedListWithWork (some inc.1) address.1 cells
    obtain ⟨incWidth,incWork,incValue⟩ := incrementFixedBinaryWordWithWork_spec word
    change inc.1.length = word.length at incWidth
    change inc.2 ≤ 5*word.length+3 at incWork
    have freshValue : binaryWordValue inc.1 = table.read arc+1 := by
      rw [wordWidth,readValue] at incValue
      exact incValue fits
    obtain ⟨_,modified,newWork⟩ := accessBinaryIndexedListWithWork_spec (some inc.1) address.1 cells
    change updated.1.2 = cells.set pos inc.1 at modified
    change EncodesThinLoadTable (table.write arc (table.read arc+1)) updated.1.2 width ∧
      address.2+read.2+inc.2+updated.2+7 ≤ binaryThinLoadBumpWorkBudget (n*n) base.length labels width
    refine ⟨⟨?_,?_⟩,?_⟩
    · rw [modified,List.map_set,encoded.1,addr,freshValue,FinThinLoadTable.write,Array.toList_set]
      rfl
    · rw [modified]
      intro value member
      rcases List.mem_or_eq_of_mem_set member with old | fresh
      · exact encoded.2 value old
      · rw [fresh,incWidth,wordWidth]
    · have readBound : read.2 ≤ walkBudget := walk _ oldWork
      have updateBound : updated.2 ≤ walkBudget := walk _ newWork
      rw [wordWidth] at incWork
      change address.2+read.2+inc.2+updated.2+7 ≤
        binaryPairAddressWorkBudget base.length labels labels+2*walkBudget+(5*width+3)+7
      omega

/-- Each pair of supplied words has the labels of the corresponding arc. -/
def BinaryThinArcMatches {n : ℕ} (labels : ℕ) (words : List Bool × List Bool) (arc : Fin n × Fin n) : Prop :=
  binaryWordValue words.1 = arc.1.val ∧ binaryWordValue words.2 = arc.2.val ∧
    words.1.length ≤ labels ∧ words.2.length ≤ labels

/-- Apply a load increment for each arc in the supplied cut list. -/
def bumpBinaryThinCutWithWork (base : List Bool) (cells : List (List Bool)) :
    List (List Bool × List Bool) → List (List Bool) × ℕ
  | [] => (cells,3)
  | words::rest =>
    let step := bumpBinaryThinLoadWithWork cells base words.1 words.2
    let after := bumpBinaryThinCutWithWork base step.1 rest
    (after.1,step.2+after.2+5)

/-- Every entry grows by the multiplicity of its arc. The terminal load
bound prevents overflow at every intermediate step. -/
theorem bumpBinaryThinCutWithWork_spec {n width labels : ℕ}
    (table : FinThinLoadTable n) (cells : List (List Bool)) (base : List Bool)
    (words : List (List Bool × List Bool)) (cut : List (Fin n × Fin n))
    (encoded : EncodesThinLoadTable table cells width) (size : binaryWordValue base = n)
    (matching : List.Forall₂ (BinaryThinArcMatches labels) words cut)
    (fits : ∀ arc, table.read arc+cut.count arc < 2^width) :
    let out := bumpBinaryThinCutWithWork base cells words
    (∃ after : FinThinLoadTable n, EncodesThinLoadTable after out.1 width ∧
      ∀ arc, after.read arc = table.read arc+cut.count arc) ∧
      out.2 ≤ 3+cut.length*(binaryThinLoadBumpWorkBudget (n*n) base.length labels width+5) := by
  induction matching generalizing table cells with
  | nil =>
    refine ⟨⟨table,encoded,?_⟩,?_⟩
    · intro arc
      simp
    · simp [bumpBinaryThinCutWithWork]
  | @cons pair arc rest arcs head tail ih =>
    let step := bumpBinaryThinLoadWithWork cells base pair.1 pair.2
    let written := table.write arc (table.read arc+1)
    let after := bumpBinaryThinCutWithWork base step.1 rest
    let budget := binaryThinLoadBumpWorkBudget (n*n) base.length labels width
    have increments (query : Fin n × Fin n) :
        written.read query+arcs.count query = table.read query+(arc::arcs).count query := by
      rw [FinThinLoadTable.read_write,List.count_cons]
      by_cases same : query = arc
      · subst query
        simp only [ite_true,beq_self_eq_true]
        omega
      · simp [same,Ne.symm same]
    have fitsStep : table.read arc+1 < 2^width := by
      have terminal := fits arc
      simp only [List.count_cons,beq_self_eq_true,ite_true] at terminal
      omega
    obtain ⟨encodedStep,stepWork⟩ := bumpBinaryThinLoadWithWork_refines table cells arc base pair.1 pair.2
      encoded size head.1 head.2.1 head.2.2.1 head.2.2.2 fitsStep
    obtain ⟨⟨result,encodedAfter,loads⟩,tailWork⟩ :=
      ih written step.1 encodedStep (fun query => (increments query).symm ▸ fits query)
    change (∃ result : FinThinLoadTable n, EncodesThinLoadTable result after.1 width ∧
      ∀ query, result.read query = table.read query+(arc::arcs).count query) ∧
      step.2+after.2+5 ≤ 3+(arcs.length+1)*(budget+5)
    change after.2 ≤ 3+arcs.length*(budget+5) at tailWork
    change step.2 ≤ budget at stepWork
    refine ⟨⟨result,encodedAfter,fun query => (loads query).trans (increments query)⟩,?_⟩
    rw [Nat.add_mul,Nat.one_mul]
    omega

/-- For a cut without duplicates, the binary list run represents the
load table from the existing indexed implementation. -/
theorem bumpBinaryThinCutWithWork_refines {n width labels : ℕ}
    (table : FinThinLoadTable n) (cells : List (List Bool)) (base : List Bool)
    (words : List (List Bool × List Bool)) (cut : List (Fin n × Fin n))
    (encoded : EncodesThinLoadTable table cells width) (size : binaryWordValue base = n)
    (matching : List.Forall₂ (BinaryThinArcMatches labels) words cut) (unique : cut.Nodup)
    (fits : ∀ arc, table.read arc+cut.count arc < 2^width) :
    let out := bumpBinaryThinCutWithWork base cells words
    (∃ after : FinThinLoadTable n, EncodesThinLoadTable after out.1 width ∧
      after.read = (bumpFinThinLoadsWithWordWork table cut).1.read) ∧
      out.2 ≤ 3+cut.length*(binaryThinLoadBumpWorkBudget (n*n) base.length labels width+5) := by
  obtain ⟨⟨after,representation,loads⟩,work⟩ :=
    bumpBinaryThinCutWithWork_spec table cells base words cut encoded size matching fits
  obtain ⟨reference,_⟩ := bumpFinThinLoadsWithWordWork_spec table cut unique
  refine ⟨⟨after,representation,?_⟩,work⟩
  funext arc
  rw [reference,loads,doubleCut]
  simp only [List.mem_toFinset]
  by_cases member : arc ∈ cut
  · rw [List.count_eq_one_of_mem unique member,ite_eq_left member]
  · rw [List.count_eq_zero_of_not_mem member,Nat.add_zero,ite_eq_right member]

end OnlineReachabilityPreservers
