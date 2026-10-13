import DirectedFlowCutGap.AdaptivePackingCallLift

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem call_run {C : ℕ} (label : Fin C → Fin 4800) (p : Program C)
    (slots : ∀ pc,p pc≠.halt → program (label pc)=ReferenceProgramLabels.instruction label (p pc))
    {heap ext : NaturalHeap} {next t : ℕ} {regs final : Registers ℕ} {start finish : Fin C}
    {source : Bits}
    (high : NaturalRun p t ⟨heap,next,regs,[],start,source⟩ []
      ⟨heap++ext,next+ext.length,final,[],finish,source⟩)
    (stop : program (label finish)=.ret .r3)
    (saved : Registers ℕ) (pc : Fin 4800) (stack : List (Frame ℕ 4800)) :
    NaturalRun program (t+1)
      ⟨heap,next,regs,⟨pc,.r3,saved⟩::stack,label start,source⟩ []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c final.d stack source pc) := by
  have lifted := ReferenceProgramLabels.run label p program slots high
  have lifted := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lifted
  have body : NaturalRun program t
      ⟨heap,next,regs,⟨pc,.r3,saved⟩::stack,label start,source⟩ []
      ⟨heap++ext,next+ext.length,final,⟨pc,.r3,saved⟩::stack,label finish,source⟩ := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program
      ⟨heap++ext,next+ext.length,final,⟨pc,.r3,saved⟩::stack,label finish,source⟩ =
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c final.d stack source pc,[],0⟩ := by
    simp [tickNatural,stop,state,Registers.get,Registers.set]
  simpa using run_append body (.step ret (.done _))

theorem normalized_return {xs : List Fraction} {mask : List Bool} {heap : NaturalHeap} {a b : ℕ}
    (row : StoredList heap a xs) (flags : BoolList heap b mask) (aligned : xs.length=mask.length)
    (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 4800) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext root,ext.length=NormalizedRow.cells xs mask ∧
      NaturalRun program (NormalizedRow.steps xs mask+1)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 3022) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredList (heap++ext) root (NormalizedRow.result xs mask) := by
  obtain ⟨ext,_,_,root,len,high,rep,_,_⟩ := NormalizedRow.normalized_high
    (NormalizedRow.state heap next a b c d [] source 364) rfl hn row flags aligned rfl
  have run := call_run normalizedLabel NormalizedRow.program normalized_slots high
    (by simp [program,normalizedLabel,NormalizedRow.program,callable]) saved pc stack
  refine ⟨ext,root,len,?_,rep⟩
  simpa [state,NormalizedRow.state,normalizedLabel] using run

theorem objective_return {xs ys : List Fraction} {heap : NaturalHeap} {a b : ℕ}
    (left : StoredList heap a xs) (right : StoredList heap b ys) (aligned : xs.length=ys.length)
    (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 4800) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext root,ext.length=ObjectiveRow.cells xs ys ∧
      NaturalRun program (ObjectiveRow.steps xs ys+1)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 3338) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (ObjectiveRow.result xs ys) := by
  obtain ⟨ext,_,root,len,high,rep,_⟩ := ObjectiveRow.objective_high
    (ObjectiveRow.state heap next a b c d [] source 308) rfl hn left right aligned rfl
  have run := call_run objectiveLabel ObjectiveRow.program objective_slots high
    (by simp [program,objectiveLabel,ObjectiveRow.program,callable]) saved pc stack
  refine ⟨ext,root,len,?_,rep⟩
  simpa [state,ObjectiveRow.state,objectiveLabel] using run
end DirectedFlowCutGap.AdaptivePackingState
