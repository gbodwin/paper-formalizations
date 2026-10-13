import DirectedFlowCutGap.PackingRunIterationCall

namespace DirectedFlowCutGap.PackingRun
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open CanonicalRationalSum (StoredList list_extend)
open RationalComparisonProgram

def instructionBound (d n B fuel bits : ℕ) : ℕ :=
  PackingStart.instructionBound d n B+PackingIteration.instructionBound d n (startWidth n B) fuel bits+7

set_option maxRecDepth 10000 in
theorem full_run {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (delta : Fraction) (label : Fin n → Bits)
    (numeric : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    {heap : NaturalHeap} {cap scalar context input fuelRoot d : ℕ} (fuel : Bits)
    (capRep : StoredList heap cap capacity.toList) (deltaRep : Stored heap scalar delta)
    (inputRep : PackingStart.Input heap input label adjacency capacity xs)
    (contextRep : heap[context]?=some (.pair input fuelRoot)) (fuelRep : BoolList heap fuelRoot fuel)
    (next : ℕ) (dense : next=heap.length) (source : Bits)
    (B : ℕ) (hB : 1≤B) (labels : ∀ i,(label i).length≤B)
    (caps : ∀ x∈capacity.toList,StoredBounded x B) (scalarWidth : StoredBounded delta B) :
    ∃ k ext first root,
      NaturalRun program k (state heap next cap scalar context d [] source 7940) []
        (state (heap++ext) (next+ext.length) cap first context root [] source 7945) ∧
      PackingStart.StateRecord (heap++ext) root label
        (BinaryFractionalCore.run capacity delta (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn) fuel).state ∧
      k ≤ instructionBound ds.length n B (value fuel) fuel.length := by
  let heap₁ := heap++[.pair cap context]
  have base : heap₁[next]?=some (.pair cap context) := by simp [heap₁,dense]
  have context₁ : heap₁[context]?=some (.pair input fuelRoot) := lookup_extend contextRep [.pair cap context]
  obtain ⟨k₁,e₁,first,startRun,startRep,startBound⟩ := start_return adjacency capacity delta label numeric hn encoded
    (list_extend capRep [.pair cap context]) (stored_extend deltaRep [.pair cap context])
    (PackingStart.input_extend inputRep [.pair cap context]) (next+1) (by simp [dense]) source
    ⟨cap,scalar,input,next⟩ 7943 []
  have base₂ := lookup_extend base e₁
  have context₂ := lookup_extend context₁ e₁
  have widths := start_widths capacity delta (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn) B scalarWidth caps
  have small := base_le_start n B
  obtain ⟨k₂,e₂,last,iterRun,iterRep,iterBound⟩ := iteration_return adjacency capacity
    (BinaryFractionalCore.start capacity delta (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn)).1
    label numeric hn encoded fuel (list_extend (list_extend capRep [.pair cap context]) e₁) startRep
    (PackingStart.input_extend (PackingStart.input_extend inputRep [.pair cap context]) e₁) context₂
    (boolList_extend (boolList_extend fuelRep [.pair cap context]) e₁)
    (next+1+e₁.length) (by simp [dense,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]) source (startWidth n B) (by omega)
    (fun i => (labels i).trans small) (fun x hx => PackingIteration.bounded_mono (caps x hx) small)
    widths.1 widths.2.2.2 widths.2.2.1 widths.2.1 ⟨cap,first,context,next⟩ 7945 []
  have t0 : tickNatural program (state heap next cap scalar context d [] source 7940)=
      some ⟨state heap₁ (next+1) cap scalar context next [] source 7941,[],0⟩ := by
    have slot : program 7940=.make .r3 (.pair .r0 .r2) 7941 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,allocateNatural,Recipe.cell,heap₁]
  have t1 : tickNatural program (state heap₁ (next+1) cap scalar context next [] source 7941)=
      some ⟨state heap₁ (next+1) cap scalar input next [] source 7942,[],0⟩ := by
    have slot : program 7941=.field .r2 .r2 false 7942 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,context₁]
  have t2 : tickNatural program (state heap₁ (next+1) cap scalar input next [] source 7942)=
      some ⟨state heap₁ (next+1) cap scalar input next [⟨7943,.r1,⟨cap,scalar,input,next⟩⟩] source 3020,[],0⟩ := by
    have slot : program 7942=.call 3020 7943 .r1 := rfl
    simp [tickNatural,state,slot]
  have t3 : tickNatural program (state (heap₁++e₁) (next+1+e₁.length) cap first input next [] source 7943)=
      some ⟨state (heap₁++e₁) (next+1+e₁.length) cap first context next [] source 7944,[],0⟩ := by
    have slot : program 7943=.field .r2 .r3 true 7944 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,base₂]
  have t4 : tickNatural program (state (heap₁++e₁) (next+1+e₁.length) cap first context next [] source 7944)=
      some ⟨state (heap₁++e₁) (next+1+e₁.length) cap first context next [⟨7945,.r3,⟨cap,first,context,next⟩⟩] source 7880,[],0⟩ := by
    have slot : program 7944=.call 7880 7945 .r3 := rfl
    simp [tickNatural,state,slot]
  refine ⟨k₁+k₂+7,[.pair cap context]++e₁++e₂,first,last,?_,?_,?_⟩
  · have finish := run_append startRun (.step t3 (.step t4 iterRun))
    convert NaturalRun.step t0 (.step t1 (.step t2 finish)) using 1 <;>
      simp [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  · simpa only [heap₁,List.append_assoc,BinaryFractionalCore.run] using iterRep
  · have bound₁ := startBound B hB labels scalarWidth caps
    unfold instructionBound
    omega
end DirectedFlowCutGap.PackingRun
