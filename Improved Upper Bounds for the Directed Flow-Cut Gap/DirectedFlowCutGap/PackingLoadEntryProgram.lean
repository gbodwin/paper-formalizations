import DirectedFlowCutGap.CanonicalRationalAddition
import DirectedFlowCutGap.ActualPackingUpdateRow

namespace DirectedFlowCutGap.PackingLoadEntry
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram

def label (pc : Fin 142) : Fin 160 := ⟨pc.val,by omega⟩
def callable : Instruction 142 → Instruction 160
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

def program : Program 160 := fun pc =>
  if h : pc.val<142 then callable (CanonicalRationalAddition.program ⟨pc.val,h⟩)
  else match pc.val with
  | 142 => .branch .r2 159 143 148 159
  | 143 => .make .r1 .nil 144
  | 144 => .make .r2 (.flag true) 145
  | 145 => .make .r2 (.pair .r2 .r1) 146
  | 146 => .make .r1 (.pair .r1 .r2) 148
  | 148 => .call 140 149 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 160)) (source : Bits) (pc : Fin 160) : NaturalState 160 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

def operand (enabled : Bool) (amount : Fraction) : Fraction := if enabled then amount else zero

def result (enabled : Bool) (amount y : Fraction) : Fraction :=
  (BinaryRational.add y (operand enabled amount)).1

def steps (enabled : Bool) (amount y : Fraction) : ℕ :=
  CanonicalRationalAddition.instructions y (operand enabled amount)+(if enabled then 4 else 8)
def cells (enabled : Bool) (amount y : Fraction) : ℕ :=
  CanonicalRationalAddition.cells y (operand enabled amount)+(if enabled then 0 else 4)

theorem slots (pc : Fin 142) (h : CanonicalRationalAddition.program pc≠.halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (CanonicalRationalAddition.program pc) := by
  have he : callable (CanonicalRationalAddition.program pc)=ReferenceProgramLabels.instruction label (CanonicalRationalAddition.program pc) := by
    cases hh : CanonicalRationalAddition.program pc <;> simp_all [callable]
  simpa [program,label,pc.isLt] using he
theorem run_append {s u v : NaturalState 160} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

theorem call_run {C : ℕ} (label : Fin C → Fin 160) (p : Program C)
    (slots : ∀ pc,p pc≠.halt → program (label pc)=ReferenceProgramLabels.instruction label (p pc))
    {heap ext : NaturalHeap} {next t : ℕ} {regs final : Registers ℕ} {start finish : Fin C}
    {source : Bits}
    (high : NaturalRun p t ⟨heap,next,regs,[],start,source⟩ []
      ⟨heap++ext,next+ext.length,final,[],finish,source⟩)
    (stop : program (label finish)=.ret .r3)
    (saved : Registers ℕ) (pc : Fin 160) (stack : List (Frame ℕ 160)) :
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

end DirectedFlowCutGap.PackingLoadEntry
