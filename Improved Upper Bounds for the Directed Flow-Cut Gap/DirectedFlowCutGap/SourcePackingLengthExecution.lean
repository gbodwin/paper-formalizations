import DirectedFlowCutGap.SourcePackingInputLength

namespace DirectedFlowCutGap.SourcePacking
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation ImmutableReferenceTerminal

/-- A single encoded-length bound for the same physical source-to-solver run,
including every request, allocation, child call, return and terminal halt. -/
theorem solve_source_length_bit {n : ℕ} (capacity : Row n) (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (ds : List (BinaryFractionalWalkOracle.Pair n)) (hn : 0<n) (suffix : Bits) :
    ∃ k charge out, Run program k charge (initial (encode capacity adjacency ds++suffix))
      ((encode capacity adjacency ds).map Event.request) out ∧
      PackingStart.StateRecord (eraseState out).heap (eraseState out).registers.d RowVertices.vertexLabel
        (BinaryFractionalCore.solveInput capacity (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn)).state ∧
      out.source=suffix ∧ out.stack=[] ∧ out.pc=8485 ∧ value out.next=out.heap.length ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 8490 1 0
        (sourceBound (encode capacity adjacency ds).length) := by
  obtain ⟨k,charge,out,run,rep,source,stack,pc,dense,stop,bound⟩ :=
    solve_source_bit capacity adjacency ds hn suffix
  exact ⟨k,charge,out,run,rep,source,stack,pc,dense,stop,bound.trans
    (SupportSearchEncoding.complete_mono 8490 1 0 _ _ (source_bound capacity adjacency ds))⟩

end DirectedFlowCutGap.SourcePacking
