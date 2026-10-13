import DirectedFlowCutGap.ActualPackingZeroMask
import DirectedFlowCutGap.BinaryFractionalDispatch

namespace DirectedFlowCutGap.PackingZeroMask
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

theorem mask_eq_original {n : ℕ} (c : BinaryFractionalRows.Row n) :
    mask (IndexedRationalRead.fields c.toList)=(BinaryFractionalDispatch.zeroMask c).1.toList := by
  simp [mask,IndexedRationalRead.fields,BinaryFractionalDispatch.zeroMask,
    EncodedRoundingInput.tabulate_value,ScalarQuotientRow.row_toList,Vector.toList_ofFn,List.map_ofFn,
    Function.comp_def,BinaryFractionalGraphOracle.read,BinaryFractionalRows.get,
    EncodedArrayStorage.readCallback,BinaryRational.isZero]

/-- The literal scan returns the original zero-cost mask, including padded
numerators, on the same physical run that preserves the stored input fields. -/
theorem zeroMask_bit {n H A : ℕ} (c : BinaryFractionalRows.Row n)
    (initial : BitState 32) (bounded : initial.Bounded H A) (pc0 : initial.pc=30)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (table : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.a
      (IndexedRationalRead.fields c.toList)) :
    ∃ charge out, Run program (steps (IndexedRationalRead.fields c.toList)+1) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (BinaryFractionalDispatch.zeroMask c).1.toList ∧
      WordPairTableRead.Table (eraseState out).heap (eraseState initial).registers.a
        (IndexedRationalRead.fields c.toList) ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=31 ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 32 H A
        (4*SourceRowTableProgram.bits (IndexedRationalRead.fields c.toList)+16*n+4) := by
  obtain ⟨charge,out,run,rep,kept,src,stack,pc,_,halt,bound⟩ := mask_bit initial bounded pc0 dense empty table
  refine ⟨charge,out,run,?_,kept,src,stack,pc,halt,?_⟩
  · rwa [mask_eq_original] at rep
  · have hs := steps_bound (IndexedRationalRead.fields c.toList)
    have len : (IndexedRationalRead.fields c.toList).length=n := by simp [IndexedRationalRead.fields]
    exact bound.trans (SupportSearchEncoding.complete_mono 32 H A _ _ (by omega))
end DirectedFlowCutGap.PackingZeroMask
