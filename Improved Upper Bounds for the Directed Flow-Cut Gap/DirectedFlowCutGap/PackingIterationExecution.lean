import DirectedFlowCutGap.PackingIterationLoop
import DirectedFlowCutGap.PackingIterationFuel

namespace DirectedFlowCutGap.PackingIteration
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open CanonicalRationalSum (StoredList list_extend)

theorem full_execution {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (s : BinaryFractionalCore.State n) (label : Fin n → Bits)
    (numeric : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    {heap : NaturalHeap} {cap original context input fuelRoot d : ℕ} (fuel : Bits)
    (capRep : StoredList heap cap capacity.toList) (stateRep : PackingStart.StateRecord heap original label s)
    (inputRep : PackingStart.Input heap input label adjacency capacity xs)
    (contextRep : heap[context]?=some (.pair input fuelRoot)) (fuelRep : BoolList heap fuelRoot fuel)
    (next : ℕ) (dense : next=heap.length) (source : Bits) :
    ∃ steps ext, ∃ out : NaturalState 4860,
      NaturalRun program steps (state heap next cap original context d [] source 4820) [] out ∧
      out.heap=heap++ext ∧ out.next=next+ext.length ∧ out.stack=[] ∧ out.source=source ∧ out.pc=4859 ∧
      PackingStart.StateRecord out.heap out.registers.d label
        (BinaryFractionalCore.runFrom capacity (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn) fuel s).state := by
  obtain ⟨e₁,cursor,_,preRun,spine⟩ := fuel_prefix contextRep fuelRep next cap original d dense source
  obtain ⟨k,e₂,out,run,h₂,n₂,st,src,pc,rep⟩ := loop_run adjacency capacity label numeric hn encoded (value fuel) s
    (list_extend capRep e₁) (PackingStart.state_extend stateRep e₁) (PackingStart.input_extend inputRep e₁)
    spine (next+e₁.length) (by simp [dense]) source
  refine ⟨BinaryCounterProgram.steps fuel+8+k,e₁++e₂,out,run_append preRun run,?_,?_,st,src,pc,?_⟩
  · simpa only [List.append_assoc] using h₂
  · simpa only [List.length_append,Nat.add_assoc] using n₂
  · rw [repeated_runFrom]
    exact rep
end DirectedFlowCutGap.PackingIteration
