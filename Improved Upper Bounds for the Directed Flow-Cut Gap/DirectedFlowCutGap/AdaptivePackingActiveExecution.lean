import DirectedFlowCutGap.AdaptivePackingActiveTail
import DirectedFlowCutGap.AdaptivePackingActiveSelection

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem active_execution {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (s : BinaryFractionalCore.State n) (label : Fin n → Bits)
    (numeric : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    {heap : NaturalHeap} {cap original input d : ℕ}
    (capRep : StoredList heap cap capacity.toList) (stateRep : PackingStart.StateRecord heap original label s)
    (inputRep : PackingStart.Input heap input label adjacency capacity xs)
    (next : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ steps ext, ∃ out : NaturalState 4800,
      NaturalRun program steps (state heap next cap original input d stack source 4402) [] out ∧
      out.heap=heap++ext ∧ out.next=next+ext.length ∧ out.stack=stack ∧ out.source=source ∧ out.pc=4605 ∧
      PackingStart.StateRecord out.heap out.registers.d label
        (updatedState capacity s (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn s.weights).1) ∧
      (∀ W,1≤W → (∀ i,(label i).length≤W) →
        (∀ x∈s.weights.toList,StoredBounded x W) → (∀ i,StoredBounded (get capacity i) W) →
        steps ≤ GraphOracleMachine.instructionBound ds.length n W+29+
          selectionWork capacity s (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn s.weights).1 label+
          tailSteps capacity s (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn s.weights).1) := by
  obtain ⟨k,e₁,middle,data,r₁,h₁,n₁,st₁,src₁,pc₁,a₁,b₁,bound⟩ := active_selection adjacency capacity s label numeric hn
    encoded (d:=d) capRep stateRep inputRep next dense stack source
  have dense₁ : middle.next=middle.heap.length := by simp [h₁,n₁,List.length_append,dense]
  obtain ⟨e₂,out,r₂,h₂,n₂,st₂,src₂,pc₂,rep⟩ := active_tail data middle.next middle.registers.d dense₁ stack source
  have shape : state middle.heap middle.next data.best data.cost middle.registers.c middle.registers.d
      stack source 4472=middle := by
    rw [←a₁,←b₁,←st₁,←src₁,←pc₁]
    exact state_eta middle
  rw [shape] at r₂
  refine ⟨k+tailSteps capacity s (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn s.weights).1,
    e₁++e₂,out,run_append r₁ r₂,?_,?_,st₂,src₂,pc₂,rep,?_⟩
  · simp [h₂,h₁,List.append_assoc]
  · simp [n₂,n₁,List.length_append,Nat.add_assoc]
  · intro W hW labels weights capacities
    exact Nat.add_le_add_right (bound W hW labels weights capacities) _
end DirectedFlowCutGap.AdaptivePackingState
