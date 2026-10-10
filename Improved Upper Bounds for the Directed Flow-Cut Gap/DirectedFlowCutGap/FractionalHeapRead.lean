import DirectedFlowCutGap.WordPairTableRead
import DirectedFlowCutGap.RowInputBudgets

/-! Exact stored rational-row alignment for the concrete two-word reference
reader. This returns representations of the same numerator/denominator bits;
it neither adopts the old constant read charge nor substitutes the reader
through the graph algorithm. -/
namespace DirectedFlowCutGap.FractionalHeapRead
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open BinaryFractionalRows

theorem fields_get {n : ℕ} (w : Row n) (i : Fin n)
    (hi : i.val < (RowInputBudgets.fields w).length) :
    (RowInputBudgets.fields w)[i.val]=((get w i).num,(get w i).den) := by
  simp [RowInputBudgets.fields,BinaryFractionalRows.get]

/-- Padding and the exact stored rational pair are retained by the heap
representation. The finite index bound is discharged from the actual row. -/
theorem read_row {n H B : ℕ} (w : Row n) (i : Fin n) (initial : BitState 7)
    (bounded : initial.Bounded H B) (pc0 : initial.pc=0)
    (table : WordPairTableRead.Table (eraseState initial).heap
      (eraseState initial).registers.a (RowInputBudgets.fields w))
    (index : IndexSpine (eraseState initial).heap (eraseState initial).registers.b i.val) :
    ∃ charge out, Run WordPairTableRead.program (3*i.val+4) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.a (get w i).num ∧
      BoolList (eraseState out).heap (eraseState out).registers.b (get w i).den ∧
      (eraseState out).heap=(eraseState initial).heap ∧ out.source=initial.source ∧ out.pc=6 ∧
      out.Bounded (H+(3*i.val+4)) (B+(3*i.val+4)) ∧
      (attempt WordPairTableRead.program out).result=none ∧
      charge+(attempt WordPairTableRead.program out).operations ≤ completeBound 7 H B (3*i.val+4) := by
  have hi : i.val < (RowInputBudgets.fields w).length := by
    rw [RowInputBudgets.fields_length]
    exact i.isLt
  have h := WordPairTableRead.read_bit initial bounded pc0 table index hi
  simpa only [fields_get w i hi] using h

end DirectedFlowCutGap.FractionalHeapRead
