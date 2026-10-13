import DirectedFlowCutGap.SourcePackingEncoding

namespace DirectedFlowCutGap.SourcePacking
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation

set_option maxRecDepth 10000 in
/-- A single actual run reads the entire encoded primitive input, retains the
decoded registers at the program boundary, and invokes the complete solver. -/
theorem solve_source {n : ℕ} (capacity : Row n) (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (ds : List (BinaryFractionalWalkOracle.Pair n)) (hn : 0<n) (suffix : Bits)
    (heap : NaturalHeap) (next a b c d : ℕ) (dense : next=heap.length) :
    ∃ k ext cap mat root,
      NaturalRun program k (state heap next a b c d [] (encode capacity adjacency ds++suffix) 48)
        ((encode capacity adjacency ds).map Event.request)
        (state (heap++ext) (next+ext.length) cap mat mat root [] suffix 8485) ∧
      PackingStart.StateRecord (heap++ext) root RowVertices.vertexLabel
        (BinaryFractionalCore.solveInput capacity (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn)).state ∧
      k ≤ instructionBound capacity adjacency ds := by
  obtain ⟨ei,cap,mat,dem,inputRun,capTable,graph,pairTable⟩ := PackingSourceInput.prepare
    (capacityFields capacity) (matrixFields adjacency) (demandFields ds) suffix heap next a b c d dense
  have caps := PackingSource.capacity capTable
  have graph' : GraphAdjacencyProgram.Matrix (heap++ei) mat (GraphRelaxationRefinement.matrix adjacency) := by
    simpa [matrixFields,List.map_map,Function.comp_def] using graph
  obtain ⟨xs,pairs,encoded⟩ := PackingSource.encoded_demands RowVertices.vertexLabel ds pairTable
  have dense' : next+ei.length=(heap++ei).length := by simp [dense]
  obtain ⟨ks,es,vertexRoot,root,solveRun,rep,bound⟩ := EnumeratedPacking.solve_rows adjacency capacity hn
    encoded caps graph' pairs (next+ei.length) mat dense' suffix
    (SourceRowTableProgram.bits (capacityFields capacity)) (fields_width capacity.toList)
  have inputLift := ReferenceProgramLabels.run inputLabel PackingSourceInput.program program input_slots inputRun
  have inputLift' : NaturalRun program
      (PackingSourceInput.instructions (capacityFields capacity) (matrixFields adjacency) (demandFields ds))
      (state heap next a b c d [] (encode capacity adjacency ds++suffix) 48)
      ((encode capacity adjacency ds).map Event.request)
      (state (heap++ei) (next+ei.length) cap mat mat dem [] suffix 56) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,PackingSourceInput.state,
      inputLabel,state,encode] using inputLift
  have terminal : EnumeratedPacking.program 8412=.halt := rfl
  have solveCall := child_return runLabel EnumeratedPacking.program run_slots solveRun rfl rfl
    .r3 .r3 ⟨cap,mat,mat,dem⟩ 8485 [] (run_halt 8412 terminal)
  have solveCall' : NaturalRun program (ks+1)
      (state (heap++ei) (next+ei.length) cap mat mat dem [⟨8485,.r3,⟨cap,mat,mat,dem⟩⟩] suffix 8474) []
      (state ((heap++ei)++es) (next+ei.length+es.length) cap mat mat root [] suffix 8485) := by
    simpa [EnumeratedPacking.state,runLabel,state,Registers.set,Registers.get] using solveCall
  have call : tickNatural program (state (heap++ei) (next+ei.length) cap mat mat dem [] suffix 56)=
      some ⟨state (heap++ei) (next+ei.length) cap mat mat dem
        [⟨8485,.r3,⟨cap,mat,mat,dem⟩⟩] suffix 8474,[],0⟩ := by rfl
  refine ⟨PackingSourceInput.instructions (capacityFields capacity) (matrixFields adjacency) (demandFields ds)+ks+2,
    ei++es,cap,mat,root,?_,?_,?_⟩
  · simpa [state,List.append_assoc,Nat.add_assoc] using run_append inputLift' (.step call solveCall')
  · simpa [List.append_assoc] using rep
  · unfold instructionBound
    omega

end DirectedFlowCutGap.SourcePacking
