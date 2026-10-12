import DirectedFlowCutGap.ActualObjectiveRow
import DirectedFlowCutGap.PackingStateRecord

/-! The adaptive guard recomputes the objective on the actual current state,
constructs the literal one record, then calls the real rational comparison.
Its retained context keeps the original state, capacity and input pointers. -/
namespace DirectedFlowCutGap.PackingGuard
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def objectiveLabel (pc : Fin 312) : Fin 484 := ⟨pc.val,by omega⟩
def comparisonLabel (pc : Fin 158) : Fin 484 := ⟨pc.val+312,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 484) : Instruction C → Instruction 484
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

theorem callable_eq {C : ℕ} (label : Fin C → Fin 484) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

def program : Program 484 := fun pc =>
  if h : pc.val<312 then callable objectiveLabel (ObjectiveRow.program ⟨pc.val,h⟩)
  else if h : pc.val<470 then callable comparisonLabel (RationalComparisonProgram.program ⟨pc.val-312,by omega⟩)
  else match pc.val with
  | 470 => .make .r2 (.pair .r0 .r2) 471
  | 471 => .make .r2 (.pair .r1 .r2) 472
  | 472 => .field .r1 .r1 false 473
  | 473 => .call 308 474 .r3
  | 474 => .move .r1 .r3 475
  | 475 => .make .r0 .nil 476
  | 476 => .make .r3 (.flag true) 477
  | 477 => .make .r0 (.pair .r3 .r0) 478
  | 478 => .make .r0 (.pair .r0 .r0) 479
  | 479 => .call 456 480 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 484)) (source : Bits) (pc : Fin 484) : NaturalState 484 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem objective_slots (pc : Fin 312) (h : ObjectiveRow.program pc≠.halt) :
    program (objectiveLabel pc)=ReferenceProgramLabels.instruction objectiveLabel (ObjectiveRow.program pc) := by
  simpa [program,objectiveLabel,pc.isLt] using callable_eq objectiveLabel (ObjectiveRow.program pc) h

theorem comparison_slots (pc : Fin 158) (h : RationalComparisonProgram.program pc≠.halt) :
    program (comparisonLabel pc)=ReferenceProgramLabels.instruction comparisonLabel (RationalComparisonProgram.program pc) := by
  simpa [program,comparisonLabel,show ¬pc.val+312<312 by omega,show pc.val+312<470 by omega]
    using callable_eq comparisonLabel (RationalComparisonProgram.program pc) h

theorem run_append {s u v : NaturalState 484} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

theorem call_run {C : ℕ} (label : Fin C → Fin 484) (p : Program C)
    (slots : ∀ pc,p pc≠.halt → program (label pc)=ReferenceProgramLabels.instruction label (p pc))
    {heap ext : NaturalHeap} {next t : ℕ} {regs final : Registers ℕ} {start finish : Fin C}
    {source : Bits}
    (high : NaturalRun p t ⟨heap,next,regs,[],start,source⟩ []
      ⟨heap++ext,next+ext.length,final,[],finish,source⟩)
    (stop : program (label finish)=.ret .r3)
    (saved : Registers ℕ) (pc : Fin 484) (stack : List (Frame ℕ 484)) :
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

theorem objective_return {xs ys : List Fraction} {heap : NaturalHeap} {a b : ℕ}
    (left : StoredList heap a xs) (right : StoredList heap b ys) (aligned : xs.length=ys.length)
    (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 484) (stack : List (Frame ℕ 484)) (source : Bits) :
    ∃ ext root,ext.length=ObjectiveRow.cells xs ys ∧
      NaturalRun program (ObjectiveRow.steps xs ys+1)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 308) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (ObjectiveRow.result xs ys) := by
  obtain ⟨ext,_,root,len,high,rep,_⟩ := ObjectiveRow.objective_high
    (ObjectiveRow.state heap next a b c d [] source 308) rfl hn left right aligned rfl
  have run := call_run objectiveLabel ObjectiveRow.program objective_slots high
    (by simp [program,objectiveLabel,ObjectiveRow.program,callable]) saved pc stack
  refine ⟨ext,root,len,?_,rep⟩
  simpa [state,ObjectiveRow.state,objectiveLabel] using run
end DirectedFlowCutGap.PackingGuard
