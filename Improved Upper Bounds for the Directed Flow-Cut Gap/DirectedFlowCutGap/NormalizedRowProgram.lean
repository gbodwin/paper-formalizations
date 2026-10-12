import DirectedFlowCutGap.MaskedRationalRowBounds
import DirectedFlowCutGap.ScalarQuotientRowRefinement

/-! The same heap constructs the entire masked row, sums that exact new list,
then divides the original row by the freshly computed scalar. -/
namespace DirectedFlowCutGap.NormalizedRow
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def maskLabel (pc : Fin 24) : Fin 372 := ⟨pc.val,by omega⟩
def sumLabel (pc : Fin 158) : Fin 372 := ⟨pc.val+24,by omega⟩
def rowLabel (pc : Fin 182) : Fin 372 := ⟨pc.val+182,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 372) : Instruction C → Instruction 372
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

theorem callable_eq {C : ℕ} (label : Fin C → Fin 372) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

def program : Program 372 := fun pc =>
  if h : pc.val<24 then callable maskLabel (MaskedRationalRow.program ⟨pc.val,h⟩)
  else if h : pc.val<182 then callable sumLabel (CanonicalRationalSum.program ⟨pc.val-24,by omega⟩)
  else if h : pc.val<364 then callable rowLabel (ScalarQuotientRow.program false ⟨pc.val-182,by omega⟩)
  else match pc.val with
  | 364 => .make .r2 (.pair .r0 .r1) 365
  | 365 => .call 22 366 .r3
  | 366 => .move .r0 .r3 367
  | 367 => .call 180 368 .r3
  | 368 => .move .r1 .r3 369
  | 369 => .field .r0 .r2 false 370
  | 370 => .call 362 371 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 372)) (source : Bits) (pc : Fin 372) : NaturalState 372 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem mask_slots (pc : Fin 24) (h : MaskedRationalRow.program pc≠.halt) :
    program (maskLabel pc)=ReferenceProgramLabels.instruction maskLabel (MaskedRationalRow.program pc) := by
  simpa [program,maskLabel,pc.isLt] using callable_eq maskLabel (MaskedRationalRow.program pc) h

theorem sum_slots (pc : Fin 158) (h : CanonicalRationalSum.program pc≠.halt) :
    program (sumLabel pc)=ReferenceProgramLabels.instruction sumLabel (CanonicalRationalSum.program pc) := by
  simpa [program,sumLabel,show ¬pc.val+24<24 by omega,show pc.val+24<182 by omega] using
    callable_eq sumLabel (CanonicalRationalSum.program pc) h

theorem row_slots (pc : Fin 182) (h : ScalarQuotientRow.program false pc≠.halt) :
    program (rowLabel pc)=ReferenceProgramLabels.instruction rowLabel (ScalarQuotientRow.program false pc) := by
  simpa [program,rowLabel,show ¬pc.val+182<24 by omega,show ¬pc.val+182<182 by omega,
    show pc.val+182<364 by omega] using callable_eq rowLabel (ScalarQuotientRow.program false pc) h

theorem run_append {s u v : NaturalState 372} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

 theorem mask_return {xs : List Fraction} {mask : List Bool} {heap : NaturalHeap} {a b : ℕ}
    (row : StoredList heap a xs) (flags : BoolList heap b mask) (aligned : xs.length=mask.length) (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 372) (stack : List (Frame ℕ 372)) (source : Bits) :
    ∃ ext root,ext.length=MaskedRationalRow.cells mask ∧
      NaturalRun program (MaskedRationalRow.steps mask+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 22) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredList (heap++ext) root (MaskedRationalRow.result xs mask) := by
  obtain ⟨ext,root,len,core,rep⟩ := MaskedRationalRow.row_high
    (MaskedRationalRow.state heap next a b c d [] source 22) rfl hn row flags aligned rfl
  have lift := ReferenceProgramLabels.run maskLabel MaskedRationalRow.program program mask_slots core
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have body : NaturalRun program (1+MaskedRationalRow.steps mask)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 22) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 23) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      MaskedRationalRow.state,maskLabel,state] using lift
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 23)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,MaskedRationalRow.program,callable,state,Registers.get,Registers.set]
  refine ⟨ext,root,len,?_,rep⟩
  convert run_append body (.step ret (.done _)) using 1 <;> simp
  omega

 theorem sum_return {xs : List Fraction} {heap : NaturalHeap} {a b : ℕ}
    (row : StoredList heap a xs) (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 372) (stack : List (Frame ℕ 372)) (source : Bits) :
    ∃ ext root,ext.length=CanonicalRationalSum.cells xs ∧
      NaturalRun program (CanonicalRationalSum.steps xs+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 180) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root ((BinaryFractionalRows.sum xs).1) := by
  obtain ⟨ext,root,len,core,rep⟩ := CanonicalRationalSum.sum_high
    (CanonicalRationalSum.state heap next a b c d [] source 156) rfl hn row rfl
  have lift := ReferenceProgramLabels.run sumLabel CanonicalRationalSum.program program sum_slots core
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have body : NaturalRun program (1+CanonicalRationalSum.steps xs)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 180) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 181) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      CanonicalRationalSum.state,sumLabel,state] using lift
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 181)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,CanonicalRationalSum.program,callable,state,Registers.get,Registers.set]
  refine ⟨ext,root,len,?_,rep⟩
  convert run_append body (.step ret (.done _)) using 1 <;> simp
  omega

 theorem divide_return (scalar : Fraction) {xs : List Fraction} {heap : NaturalHeap} {a b : ℕ}
    (row : StoredList heap a xs) (sc : Stored heap b scalar) (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 372) (stack : List (Frame ℕ 372)) (source : Bits) :
    ∃ ext root,ext.length=ScalarQuotientRow.cells false scalar xs ∧
      NaturalRun program (ScalarQuotientRow.steps false scalar xs+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 362) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredList (heap++ext) root (ScalarQuotientRow.result false scalar xs) := by
  obtain ⟨ext,root,len,core,rep⟩ := ScalarQuotientRow.row_high false scalar
    (ScalarQuotientRow.state heap next a b c d [] source 180) rfl hn row sc rfl
  have lift := ReferenceProgramLabels.run rowLabel (ScalarQuotientRow.program false) program row_slots core
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have body : NaturalRun program (1+ScalarQuotientRow.steps false scalar xs)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 362) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 363) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      ScalarQuotientRow.state,rowLabel,state] using lift
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 363)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,ScalarQuotientRow.program,callable,state,Registers.get,Registers.set]
  refine ⟨ext,root,len,?_,rep⟩
  convert run_append body (.step ret (.done _)) using 1 <;> simp
  omega
end DirectedFlowCutGap.NormalizedRow
