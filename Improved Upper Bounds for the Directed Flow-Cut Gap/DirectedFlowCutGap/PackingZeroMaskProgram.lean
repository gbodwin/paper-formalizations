import DirectedFlowCutGap.ActualSourcePacking

namespace DirectedFlowCutGap.PackingZeroMask
open BinaryArithmetic ImmutableReferenceSimulation

def zeroLabel (pc : Fin 9) : Fin 32 := ⟨pc.val,by omega⟩
def callable : Instruction 9 → Instruction 32
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction zeroLabel op

def program : Program 32 := fun pc =>
  if h : pc.val<9 then callable (BinaryZeroProgram.program ⟨pc.val,by omega⟩)
  else match pc.val with
  | 10 => .branch .r0 11 31 31 14
  | 11 => .make .r3 .nil 12
  | 12 => .ret .r3
  | 14 => .field .r1 .r0 false 15
  | 15 => .field .r1 .r1 false 16
  | 16 => .move .r2 .r0 17
  | 17 => .move .r0 .r1 18
  | 18 => .call 7 19 .r3
  | 19 => .move .r1 .r3 20
  | 20 => .field .r0 .r2 true 21
  | 21 => .call 10 22 .r3
  | 22 => .make .r3 (.pair .r1 .r3) 23
  | 23 => .ret .r3
  | 30 => .call 10 31 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 32)) (source : Bits) (pc : Fin 32) : NaturalState 32 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem zero_slots (pc : Fin 9) (h : BinaryZeroProgram.program pc≠.halt) :
    program (zeroLabel pc)=ReferenceProgramLabels.instruction zeroLabel (BinaryZeroProgram.program pc) := by
  simp only [program,zeroLabel,show pc.val<9 from pc.isLt]
  generalize he : BinaryZeroProgram.program pc=op at *
  cases op <;> simp_all [callable]

theorem zero_halt (pc : Fin 9) (h : BinaryZeroProgram.program pc=.halt) :
    program (zeroLabel pc)=.ret .r3 := by
  simp [program,zeroLabel,pc.isLt,h,callable]
end DirectedFlowCutGap.PackingZeroMask
