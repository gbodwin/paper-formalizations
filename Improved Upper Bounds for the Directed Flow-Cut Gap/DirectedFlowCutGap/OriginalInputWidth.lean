import DirectedFlowCutGap.ActualInputWidth

namespace DirectedFlowCutGap.InputWidthProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

/-- The original typed row supplies no width result or width certificate. The
literal returned word is the old inputWidth output, including padded inputs. -/
theorem original_width_bit {n H A : ℕ} (c : BinaryFractionalRows.Row n)
    (initial : BitState 208) (bounded : initial.Bounded H A) (pc0 : initial.pc=206)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.a
      (IndexedRationalRead.fields c.toList)) :
    ∃ charge out,Run program (steps c.toList+1) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (BinaryFractionalGuesses.inputWidth c).1 ∧
      WordPairTableRead.Table (eraseState out).heap (eraseState initial).registers.a (IndexedRationalRead.fields c.toList) ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=207 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells c.toList) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 208 H A (inputSteps c.toList) := by
  exact width_bit initial bounded pc0 dense empty input
end DirectedFlowCutGap.InputWidthProgram
