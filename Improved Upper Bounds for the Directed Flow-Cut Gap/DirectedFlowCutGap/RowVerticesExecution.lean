import DirectedFlowCutGap.RowVerticesCallLift

namespace DirectedFlowCutGap.RowVertices
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation PackedBooleanConstructor
open CanonicalRationalSum (StoredList list_extend)
open GraphDiscoveryProgram (Vertices vertices_extend)

def instructionBound (n : ℕ) : ℕ := (8*n+19)*n+10

set_option maxRecDepth 10000 in
/-- Actual counter-generated labels are reversed on the same heap before return. -/
theorem enumerate {xs : List Fraction} {heap : NaturalHeap} {cap : ℕ}
    (input : StoredList heap cap xs) (next b c d : ℕ) (dense : next=heap.length) (source : Bits) :
    ∃ k ext scratch root,
      NaturalRun program k (state heap next cap b c d [] source 40) []
        (state (heap++ext) (next+ext.length) scratch b c root [] source 43) ∧
      Vertices (heap++ext) root (RowVertexScan.words xs.length []) ∧
      k ≤ instructionBound xs.length := by
  obtain ⟨outS,eS,scanRun,scanRep,hs,ns,ss,srcs,pcs⟩ := RowVertexScan.enumerate_reverse
    (RowVertexScan.state heap next cap b c d source 16) rfl dense input rfl
  have scanTerminal : RowVertexScan.program outS.pc=.halt := by rw [pcs];rfl
  have scanCall := child_return scanLabel RowVertexScan.program scan_slots scanRun rfl ss
    .r3 .r3 ⟨cap,b,c,d⟩ 41 [] (scan_halt outS.pc scanTerminal)
  have sn : outS.next=next+eS.length := by rw [ns,hs];simp [dense,RowVertexScan.state]
  have sh : outS.heap=heap++eS := hs
  have se : scanLabel 16=(16 : Fin 44) := rfl
  have scanCall' : NaturalRun program (RowVertexScan.steps xs.length []+3)
      (state heap next cap b c d [⟨41,.r3,⟨cap,b,c,d⟩⟩] source 16) []
      (state (heap++eS) (next+eS.length) cap b c outS.registers.d [] source 41) := by
    simpa [RowVertexScan.state,se,state,sh,sn,srcs,Registers.set,Registers.get,Nat.add_assoc] using scanCall
  have sr : Vertices (heap++eS) outS.registers.d (RowVertexScan.words xs.length []).reverse := by
    simpa only [sh,RowVertexScan.state] using scanRep
  obtain ⟨outR,reverseRun,reverseRep,⟨eR,hr,lr⟩,nr,str,srcr,pcr,halt⟩ := VertexListReverse.reverse_high
    (HeapWordReverse.state (heap++eS) (next+eS.length) outS.registers.d b c outS.registers.d [] source 0)
    rfl (by simp [dense,HeapWordReverse.state]) sr
  have reverseTerminal : HeapWordReverse.program outR.pc=.halt := by rw [pcr];rfl
  have reverseCall := child_return reverseLabel HeapWordReverse.program reverse_slots reverseRun rfl str
    .r1 .r3 ⟨outS.registers.d,b,c,outS.registers.d⟩ 43 [] (reverse_halt outR.pc reverseTerminal)
  have rn : outR.next=next+eS.length+eR.length := by rw [nr,hr];simp [HeapWordReverse.state,dense,Nat.add_assoc]
  have rh : outR.heap=(heap++eS)++eR := hr
  have re : reverseLabel 0=(32 : Fin 44) := rfl
  have reverseCall' : NaturalRun program (4*xs.length+3)
      (state (heap++eS) (next+eS.length) outS.registers.d b c outS.registers.d
        [⟨43,.r3,⟨outS.registers.d,b,c,outS.registers.d⟩⟩] source 32) []
      (state ((heap++eS)++eR) (next+eS.length+eR.length) outS.registers.d b c outR.registers.b [] source 43) := by
    simpa [HeapWordReverse.state,re,state,rh,rn,srcr,Registers.set,Registers.get,
      RowVertexScan.words_length,Nat.add_assoc] using reverseCall
  have t40 : tickNatural program (state heap next cap b c d [] source 40)=
      some ⟨state heap next cap b c d [⟨41,.r3,⟨cap,b,c,d⟩⟩] source 16,[],0⟩ := by
    simp [program,tickNatural,state]
  have t41 : tickNatural program (state (heap++eS) (next+eS.length) cap b c outS.registers.d [] source 41)=
      some ⟨state (heap++eS) (next+eS.length) outS.registers.d b c outS.registers.d [] source 42,[],0⟩ := by
    simp [program,tickNatural,state,Registers.get,Registers.set]
  have t42 : tickNatural program (state (heap++eS) (next+eS.length) outS.registers.d b c outS.registers.d [] source 42)=
      some ⟨state (heap++eS) (next+eS.length) outS.registers.d b c outS.registers.d
        [⟨43,.r3,⟨outS.registers.d,b,c,outS.registers.d⟩⟩] source 32,[],0⟩ := by
    simp [program,tickNatural,state]
  refine ⟨RowVertexScan.steps xs.length []+4*xs.length+9,eS++eR,outS.registers.d,outR.registers.b,?_,?_,?_⟩
  · have joined := run_append scanCall' (.step t41 (.step t42 reverseCall'))
    convert NaturalRun.step t40 joined using 1 <;>
      simp [state,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    omega
  · simpa only [rh,HeapWordReverse.state,List.reverse_reverse,List.append_assoc] using reverseRep
  · have h := RowVertexScan.steps_bound xs.length []
    unfold instructionBound
    simp only [List.length_nil,Nat.zero_add] at h
    nlinarith
end DirectedFlowCutGap.RowVertices
