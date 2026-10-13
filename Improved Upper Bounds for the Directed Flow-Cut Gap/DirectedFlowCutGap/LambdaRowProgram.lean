import DirectedFlowCutGap.ActualLambdaCore
import DirectedFlowCutGap.IndexedRationalRead

namespace DirectedFlowCutGap.LambdaRowProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

def readLabel (pc : Fin 30) : Fin 480 := ⟨pc.val,by omega⟩
def coreLabel (pc : Fin 432) : Fin 480 := ⟨30+pc.val,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 480) : Instruction C → Instruction 480
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

theorem callable_eq {C : ℕ} (label : Fin C → Fin 480) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

def program : Program 480 := fun pc =>
  if h : pc.val<30 then callable readLabel (IndexedRationalRead.program ⟨pc.val,h⟩)
  else if h : pc.val<462 then callable coreLabel (LambdaCoreProgram.program ⟨pc.val-30,by omega⟩)
  else match pc.val with
  | 462 => .make .r3 (.pair .r0 .r3) 463
  | 463 => .make .r2 (.pair .r2 .r3) 464
  | 464 => .move .r0 .r1 465
  | 465 => .field .r1 .r2 true 466
  | 466 => .field .r1 .r1 false 467
  | 467 => .call 28 468 .r3
  | 468 => .move .r0 .r3 469
  | 469 => .field .r1 .r2 false 470
  | 470 => .field .r2 .r2 true 471
  | 471 => .field .r2 .r2 true 472
  | 472 => .call 460 473 .r3
  | 473 => .ret .r3
  | 478 => .call 462 479 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 480)) (source : Bits) (pc : Fin 480) : NaturalState 480 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem read_slots (pc : Fin 30) (h : IndexedRationalRead.program pc≠.halt) :
    program (readLabel pc)=ReferenceProgramLabels.instruction readLabel (IndexedRationalRead.program pc) := by
  simpa [program,readLabel,pc.isLt] using callable_eq readLabel (IndexedRationalRead.program pc) h

theorem core_slots (pc : Fin 432) (h : LambdaCoreProgram.program pc≠.halt) :
    program (coreLabel pc)=ReferenceProgramLabels.instruction coreLabel (LambdaCoreProgram.program pc) := by
  simpa [program,coreLabel,show ¬30+pc.val<30 by omega,show 30+pc.val<462 by omega] using
    callable_eq coreLabel (LambdaCoreProgram.program pc) h

def result (rows : List Fraction) (index dimension exponent : Bits) : Fraction :=
  LambdaCoreProgram.result (IndexedRationalRead.lookup rows index) dimension exponent

def steps (rows : List Fraction) (index dimension exponent : Bits) : ℕ :=
  BinaryIndexedPairRead.steps index+
  LambdaCoreProgram.steps (IndexedRationalRead.lookup rows index) dimension exponent+18

def cells (rows : List Fraction) (index dimension exponent : Bits) : ℕ :=
  value index+4+LambdaCoreProgram.cells (IndexedRationalRead.lookup rows index) dimension exponent
end DirectedFlowCutGap.LambdaRowProgram
