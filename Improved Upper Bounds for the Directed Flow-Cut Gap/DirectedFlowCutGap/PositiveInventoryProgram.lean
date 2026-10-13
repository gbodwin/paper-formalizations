import DirectedFlowCutGap.PackingZeroMaskCall
import DirectedFlowCutGap.RetainedGraphArgmin
import DirectedFlowCutGap.GraphDiscoveryProgram

namespace DirectedFlowCutGap.PositiveInventory
open BinaryArithmetic ImmutableReferenceSimulation

def zeroLabel (pc : Fin 9) : Fin 48 := ⟨pc.val,by omega⟩
def callable : Instruction 9 → Instruction 48
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction zeroLabel op

/-- The two original aligned cursors are retained in an allocated pair. Each
numerator is tested by the real bit scanner; a positive record retains the
original rational pointer and original index-word pointer. -/
def program : Program 48 := fun pc =>
  if h : pc.val<9 then callable (BinaryZeroProgram.program ⟨pc.val,by omega⟩)
  else match pc.val with
  | 10 => .branch .r0 11 47 47 14
  | 11 => .make .r3 .nil 12
  | 12 => .ret .r3
  | 14 => .make .r2 (.pair .r0 .r1) 15
  | 15 => .field .r0 .r1 false 16
  | 16 => .field .r0 .r0 false 17
  | 17 => .call 7 18 .r3
  | 18 => .branch .r3 47 30 20 47
  | 20 => .field .r0 .r2 false 21
  | 21 => .field .r0 .r0 true 22
  | 22 => .field .r1 .r2 true 23
  | 23 => .field .r1 .r1 true 24
  | 24 => .call 10 25 .r3
  | 25 => .ret .r3
  | 30 => .field .r0 .r2 false 31
  | 31 => .field .r0 .r0 false 32
  | 32 => .field .r1 .r2 true 33
  | 33 => .field .r1 .r1 false 34
  | 34 => .make .r3 (.pair .r1 .r0) 35
  | 35 => .field .r0 .r2 false 36
  | 36 => .field .r0 .r0 true 37
  | 37 => .field .r1 .r2 true 38
  | 38 => .field .r1 .r1 true 39
  | 39 => .move .r2 .r3 40
  | 40 => .call 10 41 .r3
  | 41 => .make .r3 (.pair .r2 .r3) 42
  | 42 => .ret .r3
  | 46 => .call 10 47 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 48)) (source : Bits) (pc : Fin 48) : NaturalState 48 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem zero_slots (pc : Fin 9) (h : BinaryZeroProgram.program pc≠.halt) :
    program (zeroLabel pc)=ReferenceProgramLabels.instruction zeroLabel (BinaryZeroProgram.program pc) := by
  simp only [program,zeroLabel,show pc.val<9 from pc.isLt]
  generalize he : BinaryZeroProgram.program pc=op at *
  cases op <;> simp_all [callable]

theorem zero_halt (pc : Fin 9) (h : BinaryZeroProgram.program pc=.halt) :
    program (zeroLabel pc)=.ret .r3 := by
  simp [program,zeroLabel,pc.isLt,h,callable]
end DirectedFlowCutGap.PositiveInventory
