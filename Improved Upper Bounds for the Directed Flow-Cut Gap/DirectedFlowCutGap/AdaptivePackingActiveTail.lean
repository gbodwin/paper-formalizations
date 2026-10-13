import DirectedFlowCutGap.AdaptivePackingActualTotalLoads

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram

theorem state_eta (s : NaturalState 4800) :
    state s.heap s.next s.registers.a s.registers.b s.registers.c s.registers.d s.stack s.source s.pc=s := by
  cases s with
  | mk heap next registers stack pc source => cases registers; rfl

def tailSteps {n : ℕ} (capacity : Row n) (s : BinaryFractionalCore.State n)
    (q : BinaryFractionalCore.Choice n) : ℕ :=
  (28+(1+(PackingUpdateRow.steps (get capacity q.bottleneck) capacity.toList s.weights.toList q.mask.toList+2+18)))+
  (1+(CanonicalRationalAddition.instructions s.total (get capacity q.bottleneck)+2+
    (30+(PackingLoadRow.steps (get capacity q.bottleneck) s.loads.toList q.mask.toList+57))))

theorem active_tail {n : ℕ} {heap : NaturalHeap} {frame cap original input : ℕ}
    {label : Fin n → Bits} {capacity : Row n} {s : BinaryFractionalCore.State n} {q : BinaryFractionalCore.Choice n}
    (data : SelectedData heap frame cap original input label capacity s q)
    (next flag : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext, ∃ out : NaturalState 4800,
      NaturalRun program (tailSteps capacity s q)
        (state heap next data.best data.cost frame flag stack source 4472) [] out ∧
      out.heap=heap++ext ∧ out.next=next+ext.length ∧ out.stack=stack ∧ out.source=source ∧ out.pc=4605 ∧
      PackingStart.StateRecord out.heap out.registers.d label (updatedState capacity s q) := by
  obtain ⟨e₁,middle,weighted,r₁,h₁,n₁,st₁,src₁,pc₁,a₁,b₁,d₁⟩ := actual_weights data next flag dense stack source
  have dense₁ : middle.next=middle.heap.length := by simp [h₁,n₁,List.length_append,dense]
  obtain ⟨e₂,out,r₂,h₂,n₂,st₂,src₂,pc₂,rep⟩ := actual_total_loads weighted middle.next dense₁ stack source
  have shape : state middle.heap middle.next weighted.selected.old.total weighted.selected.amount
      middle.registers.c weighted.bestFrame stack source 4519=middle := by
    rw [←a₁,←b₁,←d₁,←st₁,←src₁,←pc₁]
    exact state_eta middle
  rw [shape] at r₂
  refine ⟨e₁++e₂,out,run_append r₁ r₂,?_,?_,st₂,src₂,pc₂,rep⟩
  · simp [h₂,h₁,List.append_assoc]
  · simp [n₂,n₁,List.length_append,Nat.add_assoc]
end DirectedFlowCutGap.AdaptivePackingState
