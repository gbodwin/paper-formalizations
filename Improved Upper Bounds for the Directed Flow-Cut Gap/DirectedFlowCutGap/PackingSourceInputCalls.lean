import DirectedFlowCutGap.PackingSourceInputCallLift

namespace DirectedFlowCutGap.PackingSourceInput
open BinaryArithmetic ImmutableReferenceSimulation WordPairTableRead

theorem read_table (rows : List (Bits × Bits)) (suffix : Bits) (heap : NaturalHeap)
    (next a b c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (destination : Reg) (pc : Fin 64) (stack : List (Frame ℕ 64)) :
    ∃ ext root, ext.length=SourceRowTableProgram.cells rows ∧
      NaturalRun program (SourceRowTableProgram.steps rows+2)
        (state heap next a b c d (⟨pc,destination,saved⟩::stack)
          (SourceRowTableProgram.encode rows++suffix) 30)
        ((SourceRowTableProgram.encode rows).map Event.request)
        ⟨heap++ext,next+ext.length,saved.set destination root,stack,pc,suffix⟩ ∧
      Table (heap++ext) root rows := by
  obtain ⟨ext,root,len,run,rep⟩ := SourceRowTableProgram.read_return rows suffix heap
    next a b c d hn ⟨a,b,c,d⟩ 31 []
  have call : tickNatural SourceRowTableProgram.program
      (SourceRowTableProgram.state heap next a b c d [] (SourceRowTableProgram.encode rows++suffix) 30)=
      some ⟨SourceRowTableProgram.state heap next a b c d [⟨31,.r3,⟨a,b,c,d⟩⟩]
        (SourceRowTableProgram.encode rows++suffix) 0,[],0⟩ := by rfl
  have core := NaturalRun.step call run
  have terminal : SourceRowTableProgram.program 31=.halt := by rfl
  have lifted := child_return inputLabel SourceRowTableProgram.program input_slots core rfl rfl
    .r3 destination saved pc stack (input_halt 31 terminal)
  refine ⟨ext,root,len,?_,rep⟩
  simpa [SourceRowTableProgram.state,inputLabel,state,len,Nat.add_assoc,Registers.get] using lifted

theorem project_matrix {heap : NaturalHeap} {a : ℕ} {rows : List (Bits × Bits)}
    (table : Table heap a rows) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (destination : Reg) (pc : Fin 64)
    (stack : List (Frame ℕ 64)) (source : Bits) :
    ∃ ext root, ext.length=rows.length+1 ∧
      NaturalRun program (7*rows.length+5)
        (state heap next a b c d (⟨pc,destination,saved⟩::stack) source 46) []
        ⟨heap++ext,next+ext.length,saved.set destination root,stack,pc,source⟩ ∧
      GraphAdjacencyProgram.Matrix (heap++ext) root (rows.map Prod.fst) := by
  obtain ⟨ext,root,len,core,rep⟩ := SourceMatrixProjection.project table next b c d hn [] source
  have terminal : SourceMatrixProjection.program 15=.halt := by rfl
  have lifted := child_return runLabel SourceMatrixProjection.program run_slots core rfl rfl
    .r3 destination saved pc stack (run_halt 15 terminal)
  refine ⟨ext,root,len,?_,rep⟩
  simpa [SourceMatrixProjection.state,runLabel,state,Nat.add_assoc,Registers.get] using lifted

end DirectedFlowCutGap.PackingSourceInput
