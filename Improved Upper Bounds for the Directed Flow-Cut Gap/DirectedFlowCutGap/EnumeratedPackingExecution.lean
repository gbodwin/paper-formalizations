import DirectedFlowCutGap.EnumeratedPackingCallLift

namespace DirectedFlowCutGap.EnumeratedPacking
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation
open CanonicalRationalSum (StoredList list_extend)

def instructionBound (d n B : ℕ) : ℕ :=
  RowVertices.instructionBound n+PreparedPacking.instructionBound d n (B+n)+4

set_option maxRecDepth 10000 in
theorem solve_rows {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    {heap : NaturalHeap} {cap matrix demands : ℕ}
    (caps : StoredList heap cap capacity.toList)
    (graph : GraphAdjacencyProgram.Matrix heap matrix (GraphRelaxationRefinement.matrix adjacency))
    (pairs : DemandCollection.DemandList heap demands xs)
    (next spare : ℕ) (dense : next=heap.length) (source : Bits)
    (B : ℕ) (widths : ∀ x∈capacity.toList,StoredBounded x B) :
    ∃ k ext vertexRoot root,
      NaturalRun program k (state heap next cap spare matrix demands [] source 8410) []
        (state (heap++ext) (next+ext.length) cap vertexRoot matrix root [] source 8412) ∧
      PackingStart.StateRecord (heap++ext) root RowVertices.vertexLabel
        (BinaryFractionalCore.solveInput capacity (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn)).state ∧
      k ≤ instructionBound ds.length n B := by
  obtain ⟨kV,eV,scratch,vertexRoot,vertexRun,vertexRep,vertexBound⟩ :=
    RowVertices.enumerate caps next spare matrix demands dense source
  have vertexTerminal : RowVertices.program 43=.halt := rfl
  have vertexCall := child_return inputLabel RowVertices.program input_slots vertexRun rfl rfl
    .r3 .r1 ⟨cap,spare,matrix,demands⟩ 8411 [] (input_halt 43 vertexTerminal)
  have ve : inputLabel 40=(40 : Fin 8420) := rfl
  have vertexCall' : NaturalRun program (kV+1)
      (state heap next cap spare matrix demands [⟨8411,.r1,⟨cap,spare,matrix,demands⟩⟩] source 40) []
      (state (heap++eV) (next+eV.length) cap vertexRoot matrix demands [] source 8411) := by
    simpa only [RowVertices.state,ve,state,Registers.set,Registers.get] using vertexCall
  have verts : GraphDiscoveryProgram.Vertices (heap++eV) vertexRoot
      ((List.finRange n).map RowVertices.vertexLabel) := by
    simpa [RowVertices.labels_exact] using vertexRep
  have labels : ∀ i : Fin n,(RowVertices.vertexLabel i).length≤B+n := by
    intro i;have h := RowVertices.label_width i;omega
  have wider : ∀ x∈capacity.toList,StoredBounded x (B+n) := by
    intro x hx;obtain ⟨h1,h2⟩ := widths x hx;constructor <;> omega
  obtain ⟨kS,eS,root,solveRun,rep,bound⟩ := PreparedPacking.solve_primitives adjacency capacity
    RowVertices.vertexLabel RowVertices.label_numeric hn encoded (list_extend caps eV) verts
    (GraphAdjacencyProgram.matrix_extend graph eV) (DemandCollection.demands_extend pairs eV)
    (next+eV.length) (by simp [dense]) source (B+n) labels wider
  have solveTerminal : PreparedPacking.program 8350=.halt := rfl
  have solveCall := child_return runLabel PreparedPacking.program run_slots solveRun rfl rfl
    .r3 .r3 ⟨cap,vertexRoot,matrix,demands⟩ 8412 [] (run_halt 8350 solveTerminal)
  have se : runLabel 8348=(8392 : Fin 8420) := rfl
  have solveCall' : NaturalRun program (kS+1)
      (state (heap++eV) (next+eV.length) cap vertexRoot matrix demands
        [⟨8412,.r3,⟨cap,vertexRoot,matrix,demands⟩⟩] source 8392) []
      (state ((heap++eV)++eS) (next+eV.length+eS.length) cap vertexRoot matrix root [] source 8412) := by
    simpa only [PreparedPacking.state,se,state,Registers.set,Registers.get] using solveCall
  have t0 : tickNatural program (state heap next cap spare matrix demands [] source 8410)=
      some ⟨state heap next cap spare matrix demands [⟨8411,.r1,⟨cap,spare,matrix,demands⟩⟩] source 40,[],0⟩ := by
    simp [program,tickNatural,state]
  have t1 : tickNatural program (state (heap++eV) (next+eV.length) cap vertexRoot matrix demands [] source 8411)=
      some ⟨state (heap++eV) (next+eV.length) cap vertexRoot matrix demands
        [⟨8412,.r3,⟨cap,vertexRoot,matrix,demands⟩⟩] source 8392,[],0⟩ := by
    simp [program,tickNatural,state]
  refine ⟨kV+kS+4,eV++eS,vertexRoot,root,?_,?_,?_⟩
  · have joined := run_append vertexCall' (.step t1 solveCall')
    convert NaturalRun.step t0 joined using 1 <;>
      simp [state,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  · simpa only [List.append_assoc] using rep
  · have hv : kV≤RowVertices.instructionBound n := by simpa using vertexBound
    unfold instructionBound
    omega
end DirectedFlowCutGap.EnumeratedPacking
