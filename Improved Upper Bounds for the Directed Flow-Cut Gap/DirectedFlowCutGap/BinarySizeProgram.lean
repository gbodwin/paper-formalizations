import DirectedFlowCutGap.BinaryTrimProgram
import DirectedFlowCutGap.BinarySizeValue

/-! The literal high-zero trimmer feeds its returned spine into the actual
binary length counter. No natural denotation or supplied size is executed. -/
namespace DirectedFlowCutGap.BinarySizeProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

def trimLabel (pc : Fin 13) : Fin 48 := ⟨pc.val,by omega⟩
def lengthLabel (pc : Fin 24) : Fin 48 := ⟨pc.val+13,by omega⟩
def program : Program 48 := fun pc =>
  if pc.val=12 then .ret .r3
  else if pc.val=35 then .ret .r1
  else if h : pc.val<13 then
    ReferenceProgramLabels.instruction trimLabel (BinaryTrimProgram.program ⟨pc.val,h⟩)
  else if h : pc.val<37 then
    ReferenceProgramLabels.instruction lengthLabel (BinaryLengthProgram.program ⟨pc.val-13,by omega⟩)
  else match pc.val with
  | 38 => .call 11 39 .r3
  | 39 => .move .r0 .r3 40
  | 40 => .call 29 41 .r3
  | 41 => .ret .r3
  | 46 => .call 38 47 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 48)) (source : Bits) (pc : Fin 48) : NaturalState 48 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem trim_slots (pc : Fin 13) (h : BinaryTrimProgram.program pc≠.halt) :
    program (trimLabel pc)=ReferenceProgramLabels.instruction trimLabel (BinaryTrimProgram.program pc) := by
  fin_cases pc <;> simp_all [program,trimLabel,BinaryTrimProgram.program]

theorem length_slots (pc : Fin 24) (h : BinaryLengthProgram.program pc≠.halt) :
    program (lengthLabel pc)=ReferenceProgramLabels.instruction lengthLabel (BinaryLengthProgram.program pc) := by
  fin_cases pc <;> simp_all [program,lengthLabel,BinaryLengthProgram.program]

def steps (word : Bits) : ℕ :=
  BinaryTrimProgram.steps word+BinaryLengthProgram.scanSteps (trim word).1.length []+8

def cells (word : Bits) : ℕ :=
  (trim word).1.length+1+BinaryLengthProgram.scanCells (trim word).1.length []

end DirectedFlowCutGap.BinarySizeProgram
