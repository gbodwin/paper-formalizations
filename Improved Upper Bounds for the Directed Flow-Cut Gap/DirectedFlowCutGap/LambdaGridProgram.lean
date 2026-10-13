import DirectedFlowCutGap.ActualLambdaRow
import DirectedFlowCutGap.OriginalGridInput

namespace DirectedFlowCutGap.LambdaGridProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

def gridLabel (pc : Fin 544) : Fin 1040 := ⟨pc.val,by omega⟩
def rowLabel (pc : Fin 480) : Fin 1040 := ⟨544+pc.val,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 1040) : Instruction C → Instruction 1040
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

theorem callable_eq {C : ℕ} (label : Fin C → Fin 1040) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

def program : Program 1040 := fun pc =>
  if h : pc.val<544 then callable gridLabel (GridInputProgram.program ⟨pc.val,h⟩)
  else if h : pc.val<1024 then callable rowLabel (LambdaRowProgram.program ⟨pc.val-544,by omega⟩)
  else match pc.val with
  | 1024 => .call 542 1025 .r3
  | 1025 => .make .r3 (.pair .r2 .r3) 1026
  | 1026 => .field .r2 .r3 true 1027
  | 1027 => .field .r2 .r2 false 1028
  | 1028 => .field .r2 .r2 false 1029
  | 1029 => .field .r3 .r3 false 1030
  | 1030 => .call 1022 1031 .r3
  | 1031 => .ret .r3
  | 1038 => .call 1024 1039 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 1040)) (source : Bits) (pc : Fin 1040) : NaturalState 1040 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem grid_slots (pc : Fin 544) (h : GridInputProgram.program pc≠.halt) :
    program (gridLabel pc)=ReferenceProgramLabels.instruction gridLabel (GridInputProgram.program pc) := by
  simpa [program,gridLabel,pc.isLt] using callable_eq gridLabel (GridInputProgram.program pc) h

theorem row_slots (pc : Fin 480) (h : LambdaRowProgram.program pc≠.halt) :
    program (rowLabel pc)=ReferenceProgramLabels.instruction rowLabel (LambdaRowProgram.program pc) := by
  simpa [program,rowLabel,show ¬544+pc.val<544 by omega,show 544+pc.val<1024 by omega] using
    callable_eq rowLabel (LambdaRowProgram.program pc) h

def result (rows : List Fraction) (index exponent : Bits) : Fraction :=
  LambdaRowProgram.result rows index (GridInputProgram.dimension rows) exponent

def steps (rows : List Fraction) (index exponent : Bits) : ℕ :=
  GridInputProgram.steps rows+LambdaRowProgram.steps rows index (GridInputProgram.dimension rows) exponent+12

def cells (rows : List Fraction) (index exponent : Bits) : ℕ :=
  GridInputProgram.cells rows+LambdaRowProgram.cells rows index (GridInputProgram.dimension rows) exponent+1
end DirectedFlowCutGap.LambdaGridProgram
