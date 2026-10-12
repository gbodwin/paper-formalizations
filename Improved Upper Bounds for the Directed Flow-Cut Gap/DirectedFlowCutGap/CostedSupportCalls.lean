import DirectedFlowCutGap.CostedSupportProgram

namespace DirectedFlowCutGap.CostedSupportProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open GraphWalkExtension RationalComparisonProgram

theorem search_call {heap : NaturalHeap} {a b c : ℕ} {vs adjacency : List Bits}
    {es : List (Bits×Bits)} {sw target : Bits} (N : ℕ)
    (vertices : SupportRecoveryProgram.Vertices heap a vs)
    (context : SupportRecoveryProgram.StoredGlobalContext heap b vs adjacency es target)
    (word : BoolList heap c sw) (rows : N ≤ adjacency.length)
    (cols : ∀ (i : ℕ) (hi : i<N),N ≤ (adjacency[i]'(lt_of_lt_of_le hi rows)).length)
    (hv : ∀ u∈vs,value u<N) (ht : value target<N)
    (next d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 592)
    (stack : List (Frame ℕ 592)) (source : Bits) :
    ∃ ext root,ext.length=SupportRecoveryProgram.searchCells vs adjacency es sw target ∧
      NaturalRun program (SupportRecoveryProgram.searchSteps vs adjacency es sw target+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 270) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      EdgeList (heap++ext) root (edges vs adjacency es sw target) := by
  obtain ⟨ext,root,len,high,rep⟩ := SupportRecoveryProgram.search_high N
    (SupportRecoveryProgram.state heap next a b c d [] source 270) rfl hn rfl vertices context word rows cols hv ht
  let frames := (⟨pc,.r3,saved⟩::stack)
  have mapped := ReferenceProgramLabels.run searchLabel SupportRecoveryProgram.program program search_slots high
  have lifted := ReferenceProgramStack.run program frames mapped
  have body : NaturalRun program (SupportRecoveryProgram.searchSteps vs adjacency es sw target+1)
      (state heap next a b c d frames source 270) []
      (state (heap++ext) (next+ext.length) a b c root frames source 279) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      SupportRecoveryProgram.state,searchLabel,state] using lifted
  have ret : tickNatural program (state (heap++ext) (next+ext.length) a b c root frames source 279)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  exact ⟨ext,root,len,by simpa [Nat.add_assoc] using run_append body (.step ret (.done _)),rep⟩

theorem project_call {heap : NaturalHeap} {a : ℕ} {es : List (Bits×Bits)}
    (input : EdgeList heap a es) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 592) (stack : List (Frame ℕ 592)) (source : Bits) :
    ∃ ext root,ext.length=es.length ∧ NaturalRun program (7*es.length+5)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 290) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      PathCostMaterialization.WordList (heap++ext) root (es.map Prod.fst) := by
  obtain ⟨ext,root,len,high,rep⟩ := RecoveredEdgeProjection.project_high input next b c d hn source
  let frames := (⟨pc,.r3,saved⟩::stack)
  have mapped := ReferenceProgramLabels.run projectLabel RecoveredEdgeProjection.program program project_slots high
  have lifted := ReferenceProgramStack.run program frames mapped
  have body : NaturalRun program (7*es.length+4)
      (state heap next a b c d frames source 290) []
      (state (heap++ext) (next+ext.length) a b c root frames source 291) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      RecoveredEdgeProjection.state,projectLabel,state] using lifted
  have ret : tickNatural program (state (heap++ext) (next+ext.length) a b c root frames source 291)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  exact ⟨ext,root,len,by simpa [Nat.add_assoc] using run_append body (.step ret (.done _)),rep⟩

theorem sum_call {heap : NaturalHeap} {a b : ℕ} {words : List Bits} {rows : List Fraction} {sw : Bits}
    (input : PathCostMaterialization.WordList heap a words) (context : OutgoingCostProgram.Context heap b rows sw)
    (valid : ∀ w∈words,value w<rows.length) (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 592) (stack : List (Frame ℕ 592)) (source : Bits) :
    ∃ ext root,ext.length=MaterializedPathSum.cells rows sw words ∧
      NaturalRun program (MaterializedPathSum.steps rows sw words+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 574) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (MaterializedPathSum.result rows sw words) := by
  obtain ⟨ext,root,len,high,rep,_⟩ := MaterializedPathSum.sum_high
    (MaterializedPathSum.state heap next a b c d [] source 282) rfl hn rfl input context valid
  let frames := (⟨pc,.r3,saved⟩::stack)
  have mapped := ReferenceProgramLabels.run sumLabel MaterializedPathSum.program program sum_slots high
  have lifted := ReferenceProgramStack.run program frames mapped
  have body : NaturalRun program (MaterializedPathSum.steps rows sw words+1)
      (state heap next a b c d frames source 574) []
      (state (heap++ext) (next+ext.length) a b c root frames source 575) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      MaterializedPathSum.state,sumLabel,state] using lifted
  have ret : tickNatural program (state (heap++ext) (next+ext.length) a b c root frames source 575)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  exact ⟨ext,root,len,by simpa [Nat.add_assoc] using run_append body (.step ret (.done _)),rep⟩

end DirectedFlowCutGap.CostedSupportProgram
