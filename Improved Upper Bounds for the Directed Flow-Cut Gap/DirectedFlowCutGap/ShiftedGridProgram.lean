import DirectedFlowCutGap.LambdaGridRangeBound
import DirectedFlowCutGap.ScalarAdditionRowEncoding

namespace DirectedFlowCutGap.ShiftedGridProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

def gridLabel (pc : Fin 1040) : Fin 1220 := ⟨pc.val,by omega⟩
def rowLabel (pc : Fin 160) : Fin 1220 := ⟨1040+pc.val,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 1220) : Instruction C → Instruction 1220
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

theorem callable_eq {C : ℕ} (label : Fin C → Fin 1220) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

def program : Program 1220 := fun pc =>
  if h : pc.val<1040 then callable gridLabel (LambdaGridProgram.program ⟨pc.val,h⟩)
  else if h : pc.val<1200 then callable rowLabel (ScalarAdditionRow.program ⟨pc.val-1040,by omega⟩)
  else match pc.val with
  | 1200 => .call 1038 1201 .r3
  | 1201 => .move .r1 .r3 1202
  | 1202 => .call 1198 1203 .r3
  | 1203 => .ret .r3
  | 1218 => .call 1200 1219 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 1220)) (source : Bits) (pc : Fin 1220) : NaturalState 1220 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem grid_slots (pc : Fin 1040) (h : LambdaGridProgram.program pc≠.halt) :
    program (gridLabel pc)=ReferenceProgramLabels.instruction gridLabel (LambdaGridProgram.program pc) := by
  simpa [program,gridLabel,pc.isLt] using callable_eq gridLabel (LambdaGridProgram.program pc) h

theorem row_slots (pc : Fin 160) (h : ScalarAdditionRow.program pc≠.halt) :
    program (rowLabel pc)=ReferenceProgramLabels.instruction rowLabel (ScalarAdditionRow.program pc) := by
  simpa [program,rowLabel,show ¬1040+pc.val<1040 by omega,show 1040+pc.val<1200 by omega] using
    callable_eq rowLabel (ScalarAdditionRow.program pc) h

def scalar (rows : List Fraction) (index exponent : Bits) : Fraction :=
  LambdaGridProgram.result rows index exponent

def result (rows : List Fraction) (index exponent : Bits) : List Fraction :=
  ScalarAdditionRow.result (scalar rows index exponent) rows

def steps (rows : List Fraction) (index exponent : Bits) : ℕ :=
  LambdaGridProgram.steps rows index exponent+
  ScalarAdditionRow.steps (scalar rows index exponent) rows+8

def cells (rows : List Fraction) (index exponent : Bits) : ℕ :=
  LambdaGridProgram.cells rows index exponent+
  ScalarAdditionRow.cells (scalar rows index exponent) rows
end DirectedFlowCutGap.ShiftedGridProgram
