import DirectedFlowCutGap.AdaptivePackingArithmeticCalls

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem call0_run {C : ℕ} (label : Fin C → Fin 4800) (p : Program C)
    (slots : ∀ pc,p pc≠.halt → program (label pc)=ReferenceProgramLabels.instruction label (p pc))
    {heap ext : NaturalHeap} {next t : ℕ} {regs final : Registers ℕ} {start finish : Fin C}
    {source : Bits}
    (high : NaturalRun p t ⟨heap,next,regs,[],start,source⟩ []
      ⟨heap++ext,next+ext.length,final,[],finish,source⟩)
    (stop : program (label finish)=.ret .r0)
    (saved : Registers ℕ) (pc : Fin 4800) (stack : List (Frame ℕ 4800)) :
    NaturalRun program (t+1)
      ⟨heap,next,regs,⟨pc,.r0,saved⟩::stack,label start,source⟩ []
      (state (heap++ext) (next+ext.length) final.a saved.b saved.c saved.d stack source pc) := by
  have h := child_return label p slots high rfl rfl .r0 .r0 saved pc stack stop
  cases regs;cases final
  simpa [state,Registers.set,Registers.get] using h

theorem weights_return (amount : Fraction) {cs ys : List Fraction} {mask : List Bool}
    {heap : NaturalHeap} {a b ctx mr ar : ℕ}
    (capacity : StoredList heap a cs) (weights : StoredList heap b ys)
    (flags : BoolList heap mr mask) (amt : Stored heap ar amount)
    (context : heap[ctx]?=some (.pair mr ar))
    (aligned : cs.length=ys.length) (maskAligned : cs.length=mask.length)
    (next d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 4800) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext root,ext.length=PackingUpdateRow.cells amount cs ys mask ∧
      NaturalRun program (PackingUpdateRow.steps amount cs ys mask+2)
        (state heap next a b ctx d (⟨pc,.r0,saved⟩::stack) source 4018) []
        (state (heap++ext) (next+ext.length) root saved.b saved.c saved.d stack source pc) ∧
      StoredList (heap++ext) root (PackingUpdateRow.result amount cs ys mask) := by
  obtain ⟨ext,root,len,high,rep⟩ := PackingUpdateRow.row_high amount
    (PackingUpdateRow.state heap next a b ctx d [] source 518) rfl hn capacity weights flags amt
    context aligned maskAligned rfl
  have run := call0_run weightsLabel PackingUpdateRow.program weights_slots high
    (by simp [program,weightsLabel,PackingUpdateRow.program,callable]) saved pc stack
  refine ⟨ext,root,len,?_,rep⟩
  convert run using 1 <;> simp [state,weightsLabel,Nat.add_assoc]
  omega

theorem loads_return (amount : Fraction) {ys : List Fraction} {mask : List Bool}
    {heap : NaturalHeap} {a ctx mr ar : ℕ}
    (loads : StoredList heap a ys) (flags : BoolList heap mr mask) (amt : Stored heap ar amount)
    (context : heap[ctx]?=some (.pair mr ar)) (aligned : ys.length=mask.length)
    (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 4800) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext root,ext.length=PackingLoadRow.cells amount ys mask ∧
      NaturalRun program (PackingLoadRow.steps amount ys mask+2)
        (state heap next a ctx c d (⟨pc,.r0,saved⟩::stack) source 4352) []
        (state (heap++ext) (next+ext.length) root saved.b saved.c saved.d stack source pc) ∧
      StoredList (heap++ext) root (PackingLoadRow.result amount ys mask) := by
  obtain ⟨ext,root,len,high,rep⟩ := PackingLoadRow.row_high amount
    (PackingLoadRow.state heap next a ctx c d [] source 190) rfl hn loads flags amt context aligned rfl
  have run := call0_run loadsLabel PackingLoadRow.program loads_slots high
    (by simp [program,loadsLabel,PackingLoadRow.program,callable]) saved pc stack
  refine ⟨ext,root,len,?_,rep⟩
  convert run using 1 <;> simp [state,loadsLabel,Nat.add_assoc]
  omega
end DirectedFlowCutGap.AdaptivePackingState
