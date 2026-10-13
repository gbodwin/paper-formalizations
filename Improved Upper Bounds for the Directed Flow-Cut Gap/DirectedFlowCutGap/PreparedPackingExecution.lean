import DirectedFlowCutGap.PreparedPackingCallLift

namespace DirectedFlowCutGap.PreparedPacking
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation
open CanonicalRationalSum (StoredList list_extend)

def instructionBound (d n B : ℕ) : ℕ := PackingComplete.instructionBound d n B+8

set_option maxRecDepth 10000 in
theorem solve_primitives {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (label : Fin n → Bits) (numeric : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    {heap : NaturalHeap} {cap vertices matrix demands : ℕ}
    (caps : StoredList heap cap capacity.toList)
    (verts : GraphDiscoveryProgram.Vertices heap vertices ((List.finRange n).map label))
    (graph : GraphAdjacencyProgram.Matrix heap matrix (GraphRelaxationRefinement.matrix adjacency))
    (pairs : DemandCollection.DemandList heap demands xs)
    (next : ℕ) (dense : next=heap.length) (source : Bits)
    (B : ℕ) (labels : ∀ i,(label i).length≤B)
    (widths : ∀ x∈capacity.toList,StoredBounded x B) :
    ∃ k ext root,
      NaturalRun program k (state heap next cap vertices matrix demands [] source 8348) []
        (state (heap++ext) (next+ext.length) cap (next+3) matrix root [] source 8350) ∧
      PackingStart.StateRecord (heap++ext) root label
        (BinaryFractionalCore.solveInput capacity (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn)).state ∧
      k ≤ instructionBound ds.length n B := by
  obtain ⟨eI,len,inputRun,inputRep⟩ := PackingInput.construct adjacency capacity label xs caps verts graph pairs next dense source
  have inputTerminal : PackingInput.program 4=.halt := rfl
  have inputCall := child_return inputLabel PackingInput.program input_slots inputRun rfl rfl
    .r3 .r1 ⟨cap,vertices,matrix,demands⟩ 8349 [] (input_halt 4 inputTerminal)
  have inputEntry : inputLabel (0 : Fin 6)=(0 : Fin 8360) := rfl
  have inputCall' : NaturalRun program 5
      (state heap next cap vertices matrix demands [⟨8349,.r1,⟨cap,vertices,matrix,demands⟩⟩] source 0) []
      (state (heap++eI) (next+4) cap (next+3) matrix demands [] source 8349) := by
    simpa only [PackingInput.state,inputEntry,state,Registers.set,Registers.get] using inputCall
  obtain ⟨k,eR,out,solveRun,he,nd,st,src,pc,rep,bound⟩ := PackingComplete.solve_input adjacency capacity label numeric hn encoded
    (list_extend caps eI) inputRep (next+4) (by simp [dense,len]) source B labels widths
  have terminal : PackingComplete.program out.pc=.halt := by rw [pc];rfl
  have solveCall := child_return runLabel PackingComplete.program run_slots solveRun rfl st
    .r3 .r3 ⟨cap,next+3,matrix,demands⟩ 8350 [] (run_halt out.pc terminal)
  have entry : runLabel 8320=(8326 : Fin 8360) := rfl
  have solveCall' : NaturalRun program (k+1)
      (state (heap++eI) (next+4) cap (next+3) matrix demands
        [⟨8350,.r3,⟨cap,next+3,matrix,demands⟩⟩] source 8326) []
      (state ((heap++eI)++eR) (next+4+eR.length) cap (next+3) matrix out.registers.d [] source 8350) := by
    simpa only [PackingComplete.state,entry,state,he,nd,src,Registers.set,Registers.get] using solveCall
  have t0 : tickNatural program (state heap next cap vertices matrix demands [] source 8348)=
      some ⟨state heap next cap vertices matrix demands [⟨8349,.r1,⟨cap,vertices,matrix,demands⟩⟩] source 0,[],0⟩ := by
    simp [program,tickNatural,state]
  have t1 : tickNatural program (state (heap++eI) (next+4) cap (next+3) matrix demands [] source 8349)=
      some ⟨state (heap++eI) (next+4) cap (next+3) matrix demands
        [⟨8350,.r3,⟨cap,next+3,matrix,demands⟩⟩] source 8326,[],0⟩ := by
    simp [program,tickNatural,state]
  refine ⟨k+8,eI++eR,out.registers.d,?_,?_,by unfold instructionBound;omega⟩
  · have joined := run_append inputCall' (.step t1 solveCall')
    convert NaturalRun.step t0 joined using 1 <;> simp [state,List.append_assoc,len,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  · simpa only [he,List.append_assoc] using rep
end DirectedFlowCutGap.PreparedPacking
