import DirectedFlowCutGap.AdaptivePackingStepExecution

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram

def normalizedWidth (n B : ℕ) : ℕ := NormalizedRow.scalarWidth n B+NormalizedRow.scalarWidth n B+1

def instructionBound (d n B : ℕ) : ℕ :=
  PackingGuard.instructionBound n B+GraphOracleMachine.instructionBound d n B+6*n+10*B+
    NormalizedRow.instructionBound n B+ObjectiveRow.instructionBound n (normalizedWidth n B)+
    400*(2*B+2*PackingGuard.objectiveWidth n (normalizedWidth n B)+2)^2+
    PackingUpdateRow.instructionBound n B+20000*(4*B+2)^2+PackingLoadRow.instructionBound n B+300

theorem work_bound {n : ℕ} (demands : ℕ) (capacity : Row n) (s : BinaryFractionalCore.State n)
    (q : BinaryFractionalCore.Choice n) (label : Fin n → Bits) (numeric : ∀ i,value (label i)=i.val)
    (B : ℕ) (labels : ∀ i,(label i).length≤B)
    (caps : ∀ x∈capacity.toList,StoredBounded x B)
    (weights : ∀ x∈s.weights.toList,StoredBounded x B)
    (cost : StoredBounded s.bestCost B) (total : StoredBounded s.total B)
    (loads : ∀ x∈s.loads.toList,StoredBounded x B) :
    workBound demands B capacity s q label ≤ instructionBound demands n B := by
  let w := (normalized s.weights q.mask).1
  let candidate := (objective capacity w).1
  have small : B≤normalizedWidth n B := by unfold normalizedWidth NormalizedRow.scalarWidth;nlinarith
  have capBig : ∀ x∈capacity.toList,StoredBounded x (normalizedWidth n B) :=
    fun x hx => ⟨(caps x hx).1.trans small,(caps x hx).2.trans small⟩
  have normBig : ∀ x∈w.toList,StoredBounded x (normalizedWidth n B) :=
    PackingStart.best_width s.weights q.mask B weights
  have candidateWidth : StoredBounded candidate (PackingGuard.objectiveWidth n (normalizedWidth n B)) := by
    have hh := PackingGuard.objective_width capacity.toList w.toList (normalizedWidth n B) (by simp) capBig normBig
    rw [ObjectiveRow.result_eq_objective] at hh
    simpa only [Vector.length_toList] using hh
  have amount : StoredBounded (get capacity q.bottleneck) B := by
    apply caps
    rw [ScalarQuotientRow.row_toList]
    exact List.mem_ofFn.mpr ⟨q.bottleneck,rfl⟩
  have hg := PackingGuard.steps_bound capacity.toList s.weights.toList B (by simp) caps weights
  have hi := BinaryIndexedPairRead.steps_bound (label q.bottleneck)
  rw [numeric] at hi
  have hlabel := labels q.bottleneck
  have hj := q.bottleneck.isLt
  have hnrm := NormalizedRow.steps_bound s.weights.toList q.mask.toList B (by simp) weights
  have hobj := ObjectiveRow.steps_bound capacity.toList w.toList (normalizedWidth n B) (by simp) capBig normBig
  have hcmp := RationalComparisonProgram.instructions_bound s.bestCost candidate
  have c1:=cost.1;have c2:=cost.2;have d1:=candidateWidth.1;have d2:=candidateWidth.2
  have isize : RationalComparisonProgram.inputSize s.bestCost candidate ≤
      2*B+2*PackingGuard.objectiveWidth n (normalizedWidth n B)+2 := by
    unfold RationalComparisonProgram.inputSize
    omega
  have hcmp' := hcmp.trans (Nat.mul_le_mul_left 400 (Nat.pow_le_pow_left isize 2))
  have hselect : selectionSteps (BinaryRational.le s.bestCost candidate).1 ≤ 18 := by
    unfold selectionSteps
    split <;> omega
  have hweights := PackingUpdateRow.steps_bound (get capacity q.bottleneck) capacity.toList s.weights.toList
    q.mask.toList B amount caps weights
  have hload := PackingLoadRow.steps_bound (get capacity q.bottleneck) s.loads.toList q.mask.toList B amount loads
  have hadd := CanonicalRationalAddition.instructions_bound s.total (get capacity q.bottleneck)
  have t1:=total.1;have t2:=total.2;have a1:=amount.1;have a2:=amount.2
  have asize : CanonicalRationalAddition.inputSize s.total (get capacity q.bottleneck)≤4*B+2 := by
    unfold CanonicalRationalAddition.inputSize
    omega
  have hadd' := hadd.trans (Nat.mul_le_mul_left 20000 (Nat.pow_le_pow_left asize 2))
  simp only [Vector.length_toList] at hg hnrm hobj hweights hload
  dsimp only [workBound,selectionWork,tailSteps,instructionBound]
  dsimp only [candidate,w] at hcmp' hselect hobj
  omega
end DirectedFlowCutGap.AdaptivePackingState
