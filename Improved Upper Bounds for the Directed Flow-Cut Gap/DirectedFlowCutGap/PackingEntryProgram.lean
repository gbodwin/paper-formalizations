import DirectedFlowCutGap.ActualRationalQuotient
import DirectedFlowCutGap.CanonicalRationalAddition
import DirectedFlowCutGap.BinaryFractionalRows

/-! One selected weight update constructs two and one, then executes the
literal multiplication, quotient, addition and final multiplication. -/
namespace DirectedFlowCutGap.PackingEntry
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram

def productLabel (pc : Fin 132) : Fin 480 := ⟨pc.val,by omega⟩
def quotientLabel (pc : Fin 164) : Fin 480 := ⟨pc.val+132,by omega⟩
def additionLabel (pc : Fin 142) : Fin 480 := ⟨pc.val+296,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 480) : Instruction C → Instruction 480
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

theorem callable_eq {C : ℕ} (label : Fin C → Fin 480) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

def program : Program 480 := fun pc =>
  if h : pc.val<132 then callable productLabel (CanonicalRationalProduct.program ⟨pc.val,h⟩)
  else if h : pc.val<296 then callable quotientLabel (CanonicalRationalQuotient.program ⟨pc.val-132,by omega⟩)
  else if h : pc.val<438 then callable additionLabel (CanonicalRationalAddition.program ⟨pc.val-296,by omega⟩)
  else match pc.val with
  | 440 => .make .r2 (.pair .r1 .r2) 441
  | 441 => .make .r2 (.pair .r0 .r2) 442
  | 442 => .make .r0 .nil 443
  | 443 => .make .r1 (.flag true) 444
  | 444 => .make .r0 (.pair .r1 .r0) 445
  | 445 => .make .r1 (.pair .r0 .r0) 446
  | 446 => .make .r3 (.flag false) 447
  | 447 => .make .r0 (.pair .r3 .r0) 448
  | 448 => .field .r3 .r1 true 449
  | 449 => .make .r0 (.pair .r0 .r3) 450
  | 450 => .make .r2 (.pair .r1 .r2) 451
  | 451 => .field .r1 .r2 true 452
  | 452 => .field .r1 .r1 false 453
  | 453 => .call 130 454 .r3
  | 454 => .move .r1 .r3 455
  | 455 => .field .r0 .r2 true 456
  | 456 => .field .r0 .r0 true 457
  | 457 => .field .r0 .r0 false 458
  | 458 => .call 293 459 .r3
  | 459 => .move .r1 .r3 460
  | 460 => .field .r0 .r2 false 461
  | 461 => .call 436 462 .r3
  | 462 => .move .r1 .r3 463
  | 463 => .field .r0 .r2 true 464
  | 464 => .field .r0 .r0 true 465
  | 465 => .field .r0 .r0 true 466
  | 466 => .call 130 467 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 480)) (source : Bits) (pc : Fin 480) : NaturalState 480 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

def doubled (ci : Fraction) : Fraction := (BinaryRational.mul two ci).1
def quotient (ci amount : Fraction) : Fraction := (BinaryRational.div amount (doubled ci)).1
def factor (ci amount : Fraction) : Fraction := (BinaryRational.add one (quotient ci amount)).1
def result (ci amount y : Fraction) : Fraction := (BinaryRational.mul y (factor ci amount)).1

def steps (ci amount y : Fraction) : ℕ :=
  CanonicalRationalProduct.instructions two ci+CanonicalRationalQuotient.steps amount (doubled ci)+
    CanonicalRationalAddition.instructions one (quotient ci amount)+
    CanonicalRationalProduct.instructions y (factor ci amount)+35

def cells (ci amount y : Fraction) : ℕ :=
  CanonicalRationalProduct.cells two ci+CanonicalRationalQuotient.cells amount (doubled ci)+
    CanonicalRationalAddition.cells one (quotient ci amount)+
    CanonicalRationalProduct.cells y (factor ci amount)+10

theorem product_slots (pc : Fin 132) (h : CanonicalRationalProduct.program pc≠.halt) :
    program (productLabel pc)=ReferenceProgramLabels.instruction productLabel (CanonicalRationalProduct.program pc) := by
  simpa [program,productLabel,pc.isLt] using callable_eq productLabel (CanonicalRationalProduct.program pc) h

theorem quotient_slots (pc : Fin 164) (h : CanonicalRationalQuotient.program pc≠.halt) :
    program (quotientLabel pc)=ReferenceProgramLabels.instruction quotientLabel (CanonicalRationalQuotient.program pc) := by
  simpa [program,quotientLabel,show ¬pc.val+132<132 by omega,show pc.val+132<296 by omega] using callable_eq quotientLabel (CanonicalRationalQuotient.program pc) h

theorem addition_slots (pc : Fin 142) (h : CanonicalRationalAddition.program pc≠.halt) :
    program (additionLabel pc)=ReferenceProgramLabels.instruction additionLabel (CanonicalRationalAddition.program pc) := by
  simpa [program,additionLabel,show ¬pc.val+296<132 by omega,show ¬pc.val+296<296 by omega,show pc.val+296<438 by omega] using callable_eq additionLabel (CanonicalRationalAddition.program pc) h

theorem run_append {s u v : NaturalState 480} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

theorem call_run {C : ℕ} (label : Fin C → Fin 480) (p : Program C)
    (slots : ∀ pc,p pc≠.halt → program (label pc)=ReferenceProgramLabels.instruction label (p pc))
    {heap ext : NaturalHeap} {next t : ℕ} {regs final : Registers ℕ} {start finish : Fin C}
    {source : Bits}
    (high : NaturalRun p t ⟨heap,next,regs,[],start,source⟩ []
      ⟨heap++ext,next+ext.length,final,[],finish,source⟩)
    (stop : program (label finish)=.ret .r3)
    (saved : Registers ℕ) (pc : Fin 480) (stack : List (Frame ℕ 480)) :
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

end DirectedFlowCutGap.PackingEntry
