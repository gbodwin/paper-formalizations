import DirectedFlowCutGap.ActualBinaryPredecessor
import DirectedFlowCutGap.BinaryCounters
namespace DirectedFlowCutGap.BinaryPowerProgram
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

def predLabel (pc : Fin 64) : Fin 96 := ⟨pc.val,by omega⟩
def zeroLabel (pc : Fin 9) : Fin 96 := ⟨64+pc.val,by omega⟩
def program : Program 96 := fun pc =>
  if pc.val=63 then .ret .r3
  else if pc.val=72 then .ret .r3
  else if h : pc.val<64 then ReferenceProgramLabels.instruction predLabel (BinaryPredecessorProgram.program ⟨pc.val,h⟩)
  else if h : pc.val<73 then ReferenceProgramLabels.instruction zeroLabel (BinaryZeroProgram.program ⟨pc.val-64,by omega⟩)
  else match pc.val with
  | 76 => .call 71 77 .r3
  | 77 => .branch .r3 95 81 78 95
  | 78 => .make .r2 (.flag true) 79
  | 79 => .make .r3 .nil 80
  | 80 => .make .r3 (.pair .r2 .r3) 90
  | 81 => .call 62 82 .r3
  | 82 => .move .r0 .r3 83
  | 83 => .call 76 84 .r3
  | 84 => .make .r2 (.flag false) 85
  | 85 => .make .r3 (.pair .r2 .r3) 90
  | 90 => .ret .r3
  | 94 => .call 76 95 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 96)) (source : Bits) (pc : Fin 96) : NaturalState 96 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem pred_slots (pc : Fin 64) (h : BinaryPredecessorProgram.program pc≠.halt) :
    program (predLabel pc)=ReferenceProgramLabels.instruction predLabel (BinaryPredecessorProgram.program pc) := by
  by_cases hp : pc.val=63
  · have he : pc=63 := Fin.ext hp
    subst pc;simp [BinaryPredecessorProgram.program] at h
  · simp [program,predLabel,pc.isLt,hp,show ¬pc.val=72 by omega]

theorem zero_slots (pc : Fin 9) (h : BinaryZeroProgram.program pc≠.halt) :
    program (zeroLabel pc)=ReferenceProgramLabels.instruction zeroLabel (BinaryZeroProgram.program pc) := by
  by_cases hp : pc.val=8
  · have he : pc=8 := Fin.ext hp
    subst pc;simp [BinaryZeroProgram.program] at h
  · simp [program,zeroLabel,show ¬64+pc.val=63 by omega,show ¬64+pc.val=72 by omega,
      show ¬64+pc.val<64 by omega,show 64+pc.val<73 by omega]

def steps (word : Bits) : ℕ :=
  if hz : (isZero word).1=true then BinaryZeroProgram.steps word+8 else
    BinaryZeroProgram.steps word+BinaryPredecessorProgram.steps word+steps (predecessor word).1+12
termination_by value word
decreasing_by
  have hv : 0<value word := Nat.pos_of_ne_zero (fun h => hz ((isZero_spec word).1.mpr h))
  rw [(predecessor_spec word).1]
  omega

def cells (word : Bits) : ℕ :=
  if hz : (isZero word).1=true then 4 else
    BinaryPredecessorProgram.cells word+cells (predecessor word).1+3
termination_by value word
decreasing_by
  have hv : 0<value word := Nat.pos_of_ne_zero (fun h => hz ((isZero_spec word).1.mpr h))
  rw [(predecessor_spec word).1]
  omega
end DirectedFlowCutGap.BinaryPowerProgram
