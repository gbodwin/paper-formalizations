import DirectedFlowCutGap.OriginalRowMinimumCallLift

namespace DirectedFlowCutGap.OriginalRowMinimum
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open CanonicalRationalSum GraphDiscoveryProgram

theorem vertex_call {rows : List Fraction} {heap : NaturalHeap} {a : ℕ}
    (input : StoredList heap a rows) (next b c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 320) (stack : List (Frame ℕ 320)) (source : Bits) :
    ∃ k ext root,k≤RowVertices.instructionBound rows.length+1 ∧
      NaturalRun program k (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 40) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Vertices (heap++ext) root (RowVertexScan.words rows.length []) := by
  obtain ⟨k,ext,scratch,root,run,rep,bound⟩ := RowVertices.enumerate input next b c d dense source
  have lift := child_return vertexLabel RowVertices.program vertex_slots run rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨k+1,ext,root,by omega,by simpa [RowVertices.state,vertexLabel,state,Registers.get,Registers.set] using lift,rep⟩

theorem minimum_call {rows : List Fraction} {heap : NaturalHeap} {a b : ℕ}
    (verts : Vertices heap a (RowVertexScan.words rows.length []))
    (table : WordPairTableRead.Table heap b (IndexedRationalRead.fields rows))
    (next c d : ℕ) (dense : next=heap.length) (saved : Registers ℕ) (pc : Fin 320)
    (stack : List (Frame ℕ 320)) (source : Bits) :
    ∃ k ext root,k≤PositiveMinimum.inputSteps rows (SourceRowTableProgram.bits (IndexedRationalRead.fields rows))+1 ∧
      NaturalRun program k (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 298) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      PositiveMinimum.Result (heap++ext) root (result rows) := by
  obtain ⟨k,ext,root,bound,run,rep⟩ := PositiveMinimum.minimum rows (RowVertexScan.words rows.length [])
    (by simp [RowVertexScan.words_length]) verts table next c d dense [] source
    (SourceRowTableProgram.bits (IndexedRationalRead.fields rows)) (PositiveMinimum.original_size rows)
  have lift := child_return minimumLabel PositiveMinimum.program minimum_slots run rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨k+1,ext,root,by omega,by simpa [PositiveMinimum.state,minimumLabel,state,Registers.get,Registers.set] using lift,rep⟩
end DirectedFlowCutGap.OriginalRowMinimum
