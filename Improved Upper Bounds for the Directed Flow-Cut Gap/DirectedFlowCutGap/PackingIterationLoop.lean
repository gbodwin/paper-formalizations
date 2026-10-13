import DirectedFlowCutGap.PackingIterationAdvance

namespace DirectedFlowCutGap.PackingIteration
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open CanonicalRationalSum (StoredList list_extend)

set_option maxRecDepth 10000 in
theorem loop_run {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (label : Fin n → Bits)
    (numeric : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    (fuel : ℕ) (s : BinaryFractionalCore.State n)
    {heap : NaturalHeap} {cap original input cursor : ℕ}
    (capRep : StoredList heap cap capacity.toList) (stateRep : PackingStart.StateRecord heap original label s)
    (inputRep : PackingStart.Input heap input label adjacency capacity xs)
    (cursorRep : IndexSpine heap cursor fuel)
    (next : ℕ) (dense : next=heap.length) (source : Bits) :
    ∃ steps ext, ∃ out : NaturalState 4860,
      NaturalRun program steps (state heap next cap original cursor input [] source 4830) [] out ∧
      out.heap=heap++ext ∧ out.next=next+ext.length ∧ out.stack=[] ∧ out.source=source ∧ out.pc=4859 ∧
      PackingStart.StateRecord out.heap out.registers.d label
        (repeated capacity (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn) fuel s) := by
  induction fuel generalizing heap cap original input cursor s next with
  | zero =>
    cases cursorRep with
    | nil hc =>
      have t0 : tickNatural program (state heap next cap original cursor input [] source 4830)=
          some ⟨state heap next cap original cursor input [] source 4858,[],0⟩ := by
        have slot : program 4830=.branch .r2 4858 4859 4859 4831 := rfl
        simp [tickNatural,state,slot,Registers.get,hc,tagBranch]
      have t1 : tickNatural program (state heap next cap original cursor input [] source 4858)=
          some ⟨state heap next cap original cursor original [] source 4859,[],0⟩ := by
        have slot : program 4858=.move .r3 .r1 4859 := rfl
        simp [tickNatural,state,slot,Registers.get,Registers.set]
      refine ⟨2,[],state heap next cap original cursor original [] source 4859,
        .step t0 (.step t1 (.done _)),by simp [state],by simp [state],rfl,rfl,rfl,?_⟩
      exact stateRep
  | succ fuel ih =>
    cases cursorRep with
    | @cons cursor payload tail fuel hc ht =>
      obtain ⟨k,e₁,root,run,rep,_⟩ := advance adjacency capacity s label numeric hn encoded
        capRep stateRep inputRep hc next dense source
      obtain ⟨l,e₂,out,run₂,h₂,n₂,st₂,src₂,pc₂,rep₂⟩ := ih
        (BinaryFractionalCore.step capacity (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn) s).1
        (list_extend capRep e₁) rep (PackingStart.input_extend inputRep e₁) (indexSpine_extend ht e₁)
        (next+e₁.length) (by simp [dense])
      refine ⟨k+l,e₁++e₂,out,run_append run run₂,?_,?_,st₂,src₂,pc₂,rep₂⟩
      · simpa only [List.append_assoc] using h₂
      · simpa only [List.length_append,Nat.add_assoc] using n₂
end DirectedFlowCutGap.PackingIteration
