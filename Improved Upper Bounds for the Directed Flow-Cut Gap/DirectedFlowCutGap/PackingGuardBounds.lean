import DirectedFlowCutGap.PackingGuardState

namespace DirectedFlowCutGap.PackingGuard
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram

def objectiveWidth (n B : ℕ) : ℕ := n*(B+B+2)+1
def instructionBound (n B : ℕ) : ℕ :=
  ObjectiveRow.instructionBound n B+400*(2*objectiveWidth n B+3)^2+12

theorem objective_width (xs ys : List Fraction) (B : ℕ) (aligned : xs.length=ys.length)
    (hx : ∀ x∈xs,StoredBounded x B) (hy : ∀ y∈ys,StoredBounded y B) :
    StoredBounded (ObjectiveRow.result xs ys) (objectiveWidth xs.length B) := by
  have hp := ObjectiveProductList.products_width xs ys B hx hy
  have hs := BinaryFractionalRows.sum_stored_bound (ObjectiveProductList.products xs ys) (B+B+1)
    (fun x hx => BinaryFractionalRows.stored_raw_bound (hp x hx))
  rw [ObjectiveProductList.products_length xs ys aligned] at hs
  simpa [ObjectiveRow.result,objectiveWidth,Nat.add_assoc] using hs

theorem steps_bound (xs ys : List Fraction) (B : ℕ) (aligned : xs.length=ys.length)
    (hx : ∀ x∈xs,StoredBounded x B) (hy : ∀ y∈ys,StoredBounded y B) :
    steps xs ys ≤ instructionBound xs.length B := by
  have ho := ObjectiveRow.steps_bound xs ys B aligned hx hy
  have hw := objective_width xs ys B aligned hx hy
  have hwNum := hw.1
  have hwDen := hw.2
  have hc := RationalComparisonProgram.instructions_bound one (ObjectiveRow.result xs ys)
  have hs : RationalComparisonProgram.inputSize one (ObjectiveRow.result xs ys) ≤
      2*objectiveWidth xs.length B+3 := by
    unfold RationalComparisonProgram.inputSize one
    simp only [List.length_cons,List.length_nil]
    omega
  have hm : 400*RationalComparisonProgram.inputSize one (ObjectiveRow.result xs ys)^2 ≤
      400*(2*objectiveWidth xs.length B+3)^2 := by gcongr
  dsimp only [steps,instructionBound]
  omega
end DirectedFlowCutGap.PackingGuard
