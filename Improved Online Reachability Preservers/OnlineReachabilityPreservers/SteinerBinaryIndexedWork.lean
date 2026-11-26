import OnlineReachabilityPreservers.SteinerBinaryArithmetic
import OnlineReachabilityPreservers.ThinSearchWork

/-! Count bit and list-cell operations for a concrete indexed table model. -/

namespace OnlineReachabilityPreservers

/-- Read a cell and optionally replace it. The table is represented by a
list, and the index is a least-significant-bit-first word. -/
def accessBinaryIndexedListWithWork {α : Type*} (replacement : Option α) (index : List Bool) :
    List α → (Option α × List α) × ℕ
  | [] => ((none,[]),3)
  | x::tail =>
    let zero := binaryZeroWithWork index
    if zero.1 then ((some x,replacement.getD x::tail),zero.2+5)
    else
      let previous := binaryDecrementWithWork index
      let next := accessBinaryIndexedListWithWork replacement previous.1 tail
      ((next.1.1,x::next.1.2),zero.2+previous.2+next.2+7)

/-- Both returned values agree with indexing by the decoded natural number.
The work bound treats a stored cell as one opaque value. -/
theorem accessBinaryIndexedListWithWork_spec {α : Type*} (replacement : Option α)
    (index : List Bool) (cells : List α) :
    let out := accessBinaryIndexedListWithWork replacement index cells
    let pos := binaryWordValue index
    out.1.1 = cells[pos]? ∧ out.1.2 = (replacement.map (cells.set pos)).getD cells ∧
      out.2 ≤ 3+cells.length*(9*index.length+13) := by
  induction cells generalizing index with
  | nil => cases replacement <;> simp [accessBinaryIndexedListWithWork]
  | cons x tail ih =>
    let zero := binaryZeroWithWork index
    let prior := binaryDecrementWithWork index
    let next := accessBinaryIndexedListWithWork replacement prior.1 tail
    let pos := binaryWordValue index
    obtain ⟨zeroValue,zeroWork⟩ := binaryZeroWithWork_spec index
    change zero.1 = decide (pos = 0) at zeroValue
    change zero.2 ≤ 4*index.length+3 at zeroWork
    change (let out := if zero.1 then ((some x,replacement.getD x::tail),zero.2+5)
      else ((next.1.1,x::next.1.2),zero.2+prior.2+next.2+7)
      out.1.1 = (x::tail)[pos]? ∧ out.1.2 = (replacement.map ((x::tail).set pos)).getD (x::tail) ∧
        out.2 ≤ 3+(tail.length+1)*(9*index.length+13))
    by_cases atZero : zero.1 = true
    · have atFirst := of_decide_eq_true (zeroValue.symm.trans atZero)
      rw [ite_eq_left atZero,atFirst]
      refine ⟨rfl,?_,?_⟩
      · cases replacement <;> rfl
      · rw [Nat.add_mul,Nat.one_mul]
        omega
    · have positive : 0 < pos := Nat.pos_of_ne_zero fun eq => atZero (zeroValue.trans (decide_eq_true eq))
      obtain ⟨size,priorWork,priorValue⟩ := binaryDecrementWithWork_spec index
      obtain ⟨old,new,nextWork⟩ := ih prior.1
      change prior.1.length = index.length at size
      change prior.2 ≤ 5*index.length+3 at priorWork
      change next.2 ≤ 3+tail.length*(9*prior.1.length+13) at nextWork
      have address : binaryWordValue prior.1+1 = pos := priorValue positive
      rw [ite_eq_right atZero,← address]
      change next.1.1 = tail[binaryWordValue prior.1]? ∧ _ ∧
        zero.2+prior.2+next.2+7 ≤ 3+(tail.length+1)*(9*index.length+13)
      refine ⟨old,?_,?_⟩
      · change next.1.2 = (replacement.map (tail.set (binaryWordValue prior.1))).getD tail at new
        rw [new]
        cases replacement <;> rfl
      · rw [size] at nextWork
        rw [Nat.add_mul,Nat.one_mul]
        omega

/-- Form the row-major address for a pair of vertex labels. -/
def binaryPairAddressWithWork (base row column : List Bool) : List Bool × ℕ :=
  let product := mulBinaryWordsWithWork base row
  let sum := addBinaryWordsWithWork column product.1 false
  (sum.1,product.2+sum.2+6)

/-- An upper bound for the work of constructing the address. -/
def binaryPairAddressWorkBudget (base row column : ℕ) : ℕ :=
  binaryMultiplicationWorkBudget base row+(20*(column+row*(base+2))+5)+6

theorem binaryPairAddressWithWork_spec (base row column : List Bool) :
    let out := binaryPairAddressWithWork base row column
    binaryWordValue out.1 = binaryWordValue column+binaryWordValue base*binaryWordValue row ∧
      out.1.length ≤ column.length+row.length*(base.length+2)+1 ∧
      out.2 ≤ binaryPairAddressWorkBudget base.length row.length column.length := by
  let product := mulBinaryWordsWithWork base row
  let sum := addBinaryWordsWithWork column product.1 false
  obtain ⟨productValue,productLength,productWork⟩ := mulBinaryWordsWithWork_spec base row
  obtain ⟨sumValue,sumLength,sumWork⟩ := addBinaryWordsWithWork_spec column product.1 false
  change binaryWordValue product.1 = _ at productValue
  change product.1.length ≤ row.length*(base.length+2) at productLength
  change product.2 ≤ binaryMultiplicationWorkBudget base.length row.length at productWork
  change binaryWordValue sum.1 = binaryWordValue column+binaryWordValue product.1+0 at sumValue
  change sum.1.length ≤ column.length+product.1.length+1 at sumLength
  change sum.2 ≤ 20*(column.length+product.1.length)+5 at sumWork
  refine ⟨by simpa only [binaryPairAddressWithWork,productValue,Nat.add_zero] using sumValue,
    sumLength.trans (by gcongr),?_⟩
  exact Nat.add_le_add_right (Nat.add_le_add productWork (sumWork.trans (by gcongr))) _

/-- Access a dense table using the same row-major address as the indexed
thin load table, with all address operations on explicit bit lists. -/
def thinLoadAccessWithBinaryWork (cells : List ℕ) (base row column : List Bool)
    (replacement : Option ℕ) : (Option ℕ × List ℕ) × ℕ :=
  let address := binaryPairAddressWithWork base row column
  let accessed := accessBinaryIndexedListWithWork replacement address.1 cells
  (accessed.1,address.2+accessed.2+4)

/-- Bound address construction and the list traversal. -/
def thinLoadAccessBinaryWorkBudget (cells base row column : ℕ) : ℕ :=
  binaryPairAddressWorkBudget base row column+
    (3+cells*(9*(column+row*(base+2)+1)+13))+4

/-- Read and optional replacement in the concrete list model agree with
the indexed thin load table, with a polynomial allowance for the access. -/
theorem thinLoadAccessWithBinaryWork_refines {n : ℕ} (table : FinThinLoadTable n)
    (arc : Fin n × Fin n) (base row column : List Bool) (replacement : Option ℕ)
    (size : binaryWordValue base = n) (first : binaryWordValue row = arc.1.val)
    (second : binaryWordValue column = arc.2.val) :
    let out := thinLoadAccessWithBinaryWork table.val.toList base row column replacement
    out.1.1 = some (table.read arc) ∧
      out.1.2 = (replacement.map (fun value => (table.write arc value).val.toList)).getD table.val.toList ∧
      out.2 ≤ thinLoadAccessBinaryWorkBudget (n*n) base.length row.length column.length := by
  let address := binaryPairAddressWithWork base row column
  let accessed := accessBinaryIndexedListWithWork replacement address.1 table.val.toList
  obtain ⟨addr,addrLength,addrWork⟩ := binaryPairAddressWithWork_spec base row column
  obtain ⟨oldValue,newCells,cellWork⟩ := accessBinaryIndexedListWithWork_spec replacement address.1 table.val.toList
  change binaryWordValue address.1 = _ at addr
  rw [size,first,second] at addr
  have inside : arc.2.val+n*arc.1.val < table.val.size := table.property.symm ▸ (finProdFinEquiv arc).isLt
  change accessed.1.1 = some (table.read arc) ∧ _ ∧
    address.2+accessed.2+4 ≤ thinLoadAccessBinaryWorkBudget (n*n) base.length row.length column.length
  refine ⟨?_,?_,?_⟩
  · change accessed.1.1 = table.val.toList[binaryWordValue address.1]? at oldValue
    rw [oldValue,addr,Array.getElem?_toList,Array.getElem?_eq_getElem inside]
    rfl
  · change accessed.1.2 = (replacement.map (table.val.toList.set (binaryWordValue address.1))).getD
      table.val.toList at newCells
    change accessed.1.2 = (replacement.map (fun value => (table.write arc value).val.toList)).getD table.val.toList
    rw [newCells,addr]
    cases replacement with
    | none => rfl
    | some amount =>
      simp only [Option.map_some,Option.getD_some,FinThinLoadTable.write,Array.toList_set]
      rfl
  · change address.1.length ≤ column.length+row.length*(base.length+2)+1 at addrLength
    change accessed.2 ≤ 3+(table.val.toList.length)*(9*address.1.length+13) at cellWork
    rw [Array.length_toList,table.property] at cellWork
    have cap : accessed.2 ≤ 3+(n*n)*(9*(column.length+row.length*(base.length+2)+1)+13) :=
      cellWork.trans (by gcongr)
    exact Nat.add_le_add_right (Nat.add_le_add addrWork cap) 4

end OnlineReachabilityPreservers
