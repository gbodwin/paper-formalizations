import DirectedFlowCutGap.PackingCompleteRunCall

namespace DirectedFlowCutGap.PackingComplete
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation
open BooleanTableRead (BoolList)
open CanonicalRationalSum (StoredList list_extend)
open RationalComparisonProgram (Stored stored_extend)
open PackedBooleanConstructor (lookup_extend)

def parameterWidth (n B : ℕ) : ℕ := B+3*n+9
def instructionBound (d n B : ℕ) : ℕ := PackingParameters.instructionBound n+
  PackingRun.instructionBound d n (parameterWidth n B) (3*n^2) (3*n+6)+8

set_option maxRecDepth 10000 in
theorem solve_input {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (label : Fin n → Bits)
    (numeric : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    {heap : NaturalHeap} {cap input c d : ℕ}
    (capRep : StoredList heap cap capacity.toList)
    (inputRep : PackingStart.Input heap input label adjacency capacity xs)
    (next : ℕ) (dense : next=heap.length) (source : Bits)
    (B : ℕ) (labels : ∀ i,(label i).length≤B)
    (caps : ∀ x∈capacity.toList,StoredBounded x B) :
    ∃ k ext, ∃ out : NaturalState 8340,
      NaturalRun program k (state heap next cap input c d [] source 8320) [] out ∧
      out.heap=heap++ext ∧ out.next=next+ext.length ∧ out.stack=[] ∧ out.source=source ∧ out.pc=8326 ∧
      PackingStart.StateRecord out.heap out.registers.d label
        (BinaryFractionalCore.solveInput capacity (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn)).state ∧
      k ≤ instructionBound ds.length n B := by
  obtain ⟨eP,params,scalar,fuel,paramRun,pair,deltaRep,fuelRep⟩ :=
    parameters_return capRep next input c d dense source ⟨cap,input,c,d⟩ 8321 []
  simp only [Vector.length_toList] at paramRun deltaRep fuelRep
  let hP := heap++eP
  let nP := next+eP.length
  have context : (hP++[.pair input fuel])[nP]?=some (.pair input fuel) := by simp [hP,nP,dense]
  have small : B≤parameterWidth n B := by unfold parameterWidth;omega
  have scalarBound : StoredBounded (PackingParameters.deltaValue n) (parameterWidth n B) :=
    PackingIteration.bounded_mono (PackingParameters.delta_width n) (by unfold parameterWidth;omega)
  obtain ⟨k,eR,last,run,rep,bound⟩ := run_return adjacency capacity (PackingParameters.deltaValue n) label numeric hn encoded
    (PackingParameters.fuelWord n) (list_extend (list_extend capRep eP) [.pair input fuel])
    (stored_extend deltaRep [.pair input fuel])
    (PackingStart.input_extend (PackingStart.input_extend inputRep eP) [.pair input fuel])
    context (PackedBooleanConstructor.boolList_extend fuelRep [.pair input fuel])
    (nP+1) (by simp [nP,dense,Nat.add_assoc]) source (parameterWidth n B)
    (by unfold parameterWidth;omega) (fun i => (labels i).trans small)
    (fun x hx => PackingIteration.bounded_mono (caps x hx) small) scalarBound
    ⟨cap,scalar,nP,scalar⟩ 8326 []
  have t0 : tickNatural program (state heap next cap input c d [] source 8320)=
      some ⟨state heap next cap input c d [⟨8321,.r2,⟨cap,input,c,d⟩⟩] source 310,[],0⟩ := by
    simp [program,tickNatural,state]
  have t1 : tickNatural program (state hP nP cap input params d [] source 8321)=
      some ⟨state hP nP cap input params scalar [] source 8322,[],0⟩ := by
    simp [program,tickNatural,state,Registers.get,Registers.set,hP,pair]
  have t2 : tickNatural program (state hP nP cap input params scalar [] source 8322)=
      some ⟨state hP nP cap input fuel scalar [] source 8323,[],0⟩ := by
    simp [program,tickNatural,state,Registers.get,Registers.set,hP,pair]
  have t3 : tickNatural program (state hP nP cap input fuel scalar [] source 8323)=
      some ⟨state (hP++[.pair input fuel]) (nP+1) cap input nP scalar [] source 8324,[],0⟩ := by
    simp [program,tickNatural,state,Registers.get,Registers.set,allocateNatural,Recipe.cell]
  have t4 : tickNatural program (state (hP++[.pair input fuel]) (nP+1) cap input nP scalar [] source 8324)=
      some ⟨state (hP++[.pair input fuel]) (nP+1) cap scalar nP scalar [] source 8325,[],0⟩ := by
    simp [program,tickNatural,state,Registers.get,Registers.set]
  have t5 : tickNatural program (state (hP++[.pair input fuel]) (nP+1) cap scalar nP scalar [] source 8325)=
      some ⟨state (hP++[.pair input fuel]) (nP+1) cap scalar nP scalar
        [⟨8326,.r3,⟨cap,scalar,nP,scalar⟩⟩] source 8300,[],0⟩ := by
    simp [program,tickNatural,state]
  refine ⟨PackingParameters.steps n+k+8,eP++[.pair input fuel]++eR,
    state ((hP++[.pair input fuel])++eR) (nP+1+eR.length) cap scalar nP last [] source 8326,
    ?_,?_,?_,rfl,rfl,rfl,?_,?_⟩
  · have joined := run_append paramRun (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 run)))))
    convert NaturalRun.step t0 joined using 1 <;> simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    omega
  · simp [state,hP,List.append_assoc]
  · simp only [state,nP,List.length_append,List.length_cons,List.length_nil]
    omega
  · have exactParams := PackingParameters.input_parameters_exact capacity
    simpa only [state,BinaryFractionalCore.solveInput,BinaryFractionalCore.solve,
      ←exactParams.1,←exactParams.2] using rep
  · have hp := PackingParameters.steps_bound n
    have hf := PackingParameters.fuel_width n
    rw [(PackingParameters.parameter_values n).1] at bound
    have hb : PackingRun.instructionBound ds.length n (parameterWidth n B) (3*n^2)
        (PackingParameters.fuelWord n).length ≤
        PackingRun.instructionBound ds.length n (parameterWidth n B) (3*n^2) (3*n+6) := by
      unfold PackingRun.instructionBound PackingIteration.instructionBound
      omega
    unfold instructionBound
    omega
end DirectedFlowCutGap.PackingComplete
