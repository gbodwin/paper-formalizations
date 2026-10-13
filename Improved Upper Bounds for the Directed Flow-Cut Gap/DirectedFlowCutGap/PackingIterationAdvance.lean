import DirectedFlowCutGap.PackingIterationStepCall

namespace DirectedFlowCutGap.PackingIteration
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open CanonicalRationalSum (StoredList list_extend)

set_option maxRecDepth 10000 in
theorem advance {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (s : BinaryFractionalCore.State n) (label : Fin n → Bits)
    (numeric : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    {heap : NaturalHeap} {cap original input cursor payload tail : ℕ}
    (capRep : StoredList heap cap capacity.toList) (stateRep : PackingStart.StateRecord heap original label s)
    (inputRep : PackingStart.Input heap input label adjacency capacity xs)
    (cursorRep : heap[cursor]?=some (.pair payload tail))
    (next : ℕ) (dense : next=heap.length) (source : Bits) :
    ∃ k ext root,
      NaturalRun program k (state heap next cap original cursor input [] source 4830) []
        (state (heap++ext) (next+ext.length) cap root tail input [] source 4830) ∧
      PackingStart.StateRecord (heap++ext) root label
        (BinaryFractionalCore.step capacity (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn) s).1 ∧
      (∀ W,1≤W → (∀ i,(label i).length≤W) →
        (∀ x∈capacity.toList,StoredBounded x W) → (∀ x∈s.weights.toList,StoredBounded x W) →
        StoredBounded s.bestCost W → StoredBounded s.total W →
        (∀ x∈s.loads.toList,StoredBounded x W) →
        k≤AdaptivePackingState.instructionBound ds.length n W+9) := by
  let heap₁ := heap++[.pair tail input]
  have frame : heap₁[next]?=some (.pair tail input) := by simp [heap₁,dense]
  obtain ⟨k,ext,root,body,rep,bound⟩ := step_return adjacency capacity s label numeric hn encoded (d:=next)
    (list_extend capRep [.pair tail input]) (PackingStart.state_extend stateRep [.pair tail input])
    (PackingStart.input_extend inputRep [.pair tail input]) (next+1) (by simp [dense]) source
    ⟨cap,original,input,next⟩ 4836 []
  have frame' := lookup_extend frame ext
  have t0 : tickNatural program (state heap next cap original cursor input [] source 4830)=
      some ⟨state heap next cap original cursor input [] source 4831,[],0⟩ := by
    have slot : program 4830=.branch .r2 4858 4859 4859 4831 := rfl
    simp [tickNatural,state,slot,Registers.get,cursorRep,tagBranch]
  have t1 : tickNatural program (state heap next cap original cursor input [] source 4831)=
      some ⟨state heap next cap original tail input [] source 4832,[],0⟩ := by
    have slot : program 4831=.field .r2 .r2 true 4832 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,cursorRep]
  have t2 : tickNatural program (state heap next cap original tail input [] source 4832)=
      some ⟨state heap₁ (next+1) cap original next input [] source 4833,[],0⟩ := by
    have slot : program 4832=.make .r2 (.pair .r2 .r3) 4833 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,allocateNatural,Recipe.cell,heap₁]
  have t3 : tickNatural program (state heap₁ (next+1) cap original next input [] source 4833)=
      some ⟨state heap₁ (next+1) cap original next next [] source 4834,[],0⟩ := by
    have slot : program 4833=.move .r3 .r2 4834 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set]
  have t4 : tickNatural program (state heap₁ (next+1) cap original next next [] source 4834)=
      some ⟨state heap₁ (next+1) cap original input next [] source 4835,[],0⟩ := by
    have slot : program 4834=.field .r2 .r3 true 4835 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,frame]
  have t5 : tickNatural program (state heap₁ (next+1) cap original input next [] source 4835)=
      some ⟨state heap₁ (next+1) cap original input next [⟨4836,.r1,⟨cap,original,input,next⟩⟩] source 4400,[],0⟩ := by
    have slot : program 4835=.call 4400 4836 .r1 := rfl
    simp [tickNatural,state,slot]
  have t6 : tickNatural program (state (heap₁++ext) (next+1+ext.length) cap root input next [] source 4836)=
      some ⟨state (heap₁++ext) (next+1+ext.length) cap root tail next [] source 4837,[],0⟩ := by
    have slot : program 4836=.field .r2 .r3 false 4837 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,frame']
  have t7 : tickNatural program (state (heap₁++ext) (next+1+ext.length) cap root tail next [] source 4837)=
      some ⟨state (heap₁++ext) (next+1+ext.length) cap root tail input [] source 4830,[],0⟩ := by
    have slot : program 4837=.field .r3 .r3 true 4830 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,frame']
  refine ⟨k+9,[.pair tail input]++ext,root,?_,?_,?_⟩
  · have finish := run_append body (.step t6 (.step t7 (.done _)))
    simpa [heap₁,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using NaturalRun.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 finish)))))
  · simpa only [List.append_assoc] using rep
  · intro W hW labels caps weights cost total loads
    exact Nat.add_le_add_right (bound W hW labels caps weights cost total loads) 9
end DirectedFlowCutGap.PackingIteration
