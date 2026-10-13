import DirectedFlowCutGap.PackingIterationLoop
import DirectedFlowCutGap.PackingIterationStateSize

namespace DirectedFlowCutGap.PackingIteration
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open CanonicalRationalSum (StoredList list_extend)

theorem base_le_common (n B t : ℕ) : B≤commonWidth n B t := by
  unfold commonWidth smallWidth
  omega

set_option maxRecDepth 10000 in
theorem loop_bounded {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (label : Fin n → Bits)
    (numeric : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    (B : ℕ) (hB : 1≤B) (labels : ∀ i,(label i).length≤B)
    (caps : ∀ x∈capacity.toList,StoredBounded x B) (limit fuel elapsed : ℕ)
    (s : BinaryFractionalCore.State n) (size : StateSized B elapsed s) (remaining : elapsed+fuel≤limit)
    {heap : NaturalHeap} {cap original input cursor : ℕ}
    (capRep : StoredList heap cap capacity.toList) (stateRep : PackingStart.StateRecord heap original label s)
    (inputRep : PackingStart.Input heap input label adjacency capacity xs)
    (cursorRep : IndexSpine heap cursor fuel)
    (next : ℕ) (dense : next=heap.length) (source : Bits) :
    ∃ steps ext, ∃ out : NaturalState 4860,
      NaturalRun program steps (state heap next cap original cursor input [] source 4830) [] out ∧
      out.heap=heap++ext ∧ out.next=next+ext.length ∧ out.stack=[] ∧ out.source=source ∧ out.pc=4859 ∧
      PackingStart.StateRecord out.heap out.registers.d label
        (repeated capacity (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn) fuel s) ∧
      steps≤fuel*(AdaptivePackingState.instructionBound ds.length n (commonWidth n B limit)+9)+2 := by
  induction fuel generalizing elapsed heap cap original input cursor s next with
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
      exact ⟨2,[],state heap next cap original cursor original [] source 4859,
        .step t0 (.step t1 (.done _)),by simp [state],by simp [state],rfl,rfl,rfl,stateRep,by simp⟩
  | succ fuel ih =>
    cases cursorRep with
    | @cons cursor payload tail fuel hc ht =>
      obtain ⟨k,e₁,root,run,rep,bound⟩ := advance adjacency capacity s label numeric hn encoded
        capRep stateRep inputRep hc next dense source
      have small := small_le_common n B limit
      have sizeN := sized_mono size (by omega : elapsed≤limit)
      have base := base_le_common n B limit
      have hk := bound (commonWidth n B limit) (hB.trans base) (fun i => (labels i).trans base)
        (fun x hx => bounded_mono (caps x hx) base) (fun x hx => bounded_mono (sizeN.weights x hx) small)
        sizeN.cost (bounded_mono sizeN.total small) (fun x hx => bounded_mono (sizeN.loads x hx) small)
      obtain ⟨l,e₂,out,run₂,h₂,n₂,st₂,src₂,pc₂,rep₂,hl⟩ := ih (elapsed+1)
        (BinaryFractionalCore.step capacity (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn) s).1
        (step_size capacity _ s B elapsed caps size) (by omega)
        (list_extend capRep e₁) rep (PackingStart.input_extend inputRep e₁) (indexSpine_extend ht e₁)
        (next+e₁.length) (by simp [dense])
      refine ⟨k+l,e₁++e₂,out,run_append run run₂,?_,?_,st₂,src₂,pc₂,rep₂,?_⟩
      · simpa only [List.append_assoc] using h₂
      · simpa only [List.length_append,Nat.add_assoc] using n₂
      · nlinarith
end DirectedFlowCutGap.PackingIteration
