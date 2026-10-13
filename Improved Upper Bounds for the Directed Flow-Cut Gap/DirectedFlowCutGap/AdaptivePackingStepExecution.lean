import DirectedFlowCutGap.AdaptivePackingActiveExecution
import DirectedFlowCutGap.AdaptivePackingGuardCall

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem active_step_eq {n : ℕ} (capacity : Row n) (oracle : BinaryFractionalCore.Oracle n)
    (s : BinaryFractionalCore.State n)
    (active : (BinaryRational.le one (objective capacity s.weights).1).1=false) :
    (BinaryFractionalCore.step capacity oracle s).1=updatedState capacity s (oracle s.weights).1 := by
  simp only [BinaryFractionalCore.step,active,Bool.false_eq_true,↓reduceIte,updatedState,selectedRow,selectedCost]
  cases (BinaryRational.le s.bestCost (objective capacity (normalized s.weights (oracle s.weights).1.mask).1).1).1 <;> rfl

def workBound {n : ℕ} (demands W : ℕ) (capacity : Row n) (s : BinaryFractionalCore.State n)
    (q : BinaryFractionalCore.Choice n) (label : Fin n → Bits) : ℕ :=
  PackingGuard.steps capacity.toList s.weights.toList+4+
    (GraphOracleMachine.instructionBound demands n W+29+selectionWork capacity s q label+tailSteps capacity s q)

theorem step_execution {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (s : BinaryFractionalCore.State n) (label : Fin n → Bits)
    (numeric : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    {heap : NaturalHeap} {cap original input d : ℕ}
    (capRep : StoredList heap cap capacity.toList) (stateRep : PackingStart.StateRecord heap original label s)
    (inputRep : PackingStart.Input heap input label adjacency capacity xs)
    (next : ℕ) (dense : next=heap.length) (source : Bits) :
    ∃ steps ext, ∃ out : NaturalState 4800,
      NaturalRun program steps (state heap next cap original input d [] source 4400) [] out ∧
      out.heap=heap++ext ∧ out.next=next+ext.length ∧ out.stack=[] ∧ out.source=source ∧
      tickNatural program out=none ∧
      PackingStart.StateRecord out.heap out.registers.d label
        (BinaryFractionalCore.step capacity (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn) s).1 ∧
      (∀ W,1≤W → (∀ i,(label i).length≤W) →
        (∀ x∈s.weights.toList,StoredBounded x W) → (∀ i,StoredBounded (get capacity i) W) →
        steps ≤ workBound ds.length W capacity s
          (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn s.weights).1 label) := by
  cases stop : (BinaryRational.le one (objective capacity s.weights).1).1 with
  | true =>
    obtain ⟨ext,_,run,rep⟩ := stopped_high capacity s label stop capRep stateRep next input d dense source
    refine ⟨PackingGuard.steps capacity.toList s.weights.toList+4,ext,
      state (heap++ext) (next+ext.length) cap original input original [] source 4799,
      run,rfl,rfl,rfl,rfl,?_,?_,?_⟩
    · have slot : program 4799=.halt := rfl
      simp [tickNatural,state,slot]
    · simpa only [BinaryFractionalCore.step,stop,↓reduceIte,state] using rep
    · intro W _ _ _ _
      unfold workBound
      omega
  | false =>
    obtain ⟨e₁,flag,_,r₁,bit,rep⟩ := guard_return capacity s label capRep stateRep next input d dense
      ⟨cap,original,input,d⟩ 4401 [] source
    rw [stop] at bit
    have call : tickNatural program (state heap next cap original input d [] source 4400)=
        some ⟨state heap next cap original input d [⟨4401,.r3,⟨cap,original,input,d⟩⟩] source 470,[],0⟩ := by
      have slot : program 4400=.call 470 4401 .r3 := rfl
      simp [tickNatural,state,slot]
    have branch : tickNatural program (state (heap++e₁) (next+e₁.length) cap original input flag [] source 4401)=
        some ⟨state (heap++e₁) (next+e₁.length) cap original input flag [] source 4402,[],0⟩ := by
      have slot : program 4401=.branch .r3 4799 4402 4798 4799 := rfl
      simp [tickNatural,state,slot,Registers.get,tagBranch,bit]
    obtain ⟨k,e₂,out,r₂,h₂,n₂,st₂,src₂,pc₂,rep₂,bound⟩ := active_execution adjacency capacity s label numeric hn
      encoded (d:=flag) (list_extend capRep e₁) rep (PackingStart.input_extend inputRep e₁)
      (next+e₁.length) (by simp [List.length_append,dense]) [] source
    refine ⟨(PackingGuard.steps capacity.toList s.weights.toList+1+(k+1))+1,e₁++e₂,out,
      .step call (run_append r₁ (.step branch r₂)),?_,?_,st₂,src₂,?_,?_,?_⟩
    · simpa [List.append_assoc] using h₂
    · simpa [List.length_append,Nat.add_assoc] using n₂
    · have slot : program 4605=.halt := rfl
      simp only [tickNatural,pc₂,slot]
    · rw [active_step_eq capacity _ s stop]
      exact rep₂
    · intro W hW labels weights capacities
      have hb := bound W hW labels weights capacities
      unfold workBound
      omega
end DirectedFlowCutGap.AdaptivePackingState
