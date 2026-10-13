import DirectedFlowCutGap.BinaryZeroProgram
import DirectedFlowCutGap.BinaryBorrowProgram
import DirectedFlowCutGap.BinaryTrimProgram
import DirectedFlowCutGap.ReferenceProgramLabels

namespace DirectedFlowCutGap.BinaryPredecessorProgram
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

def zeroLabel (pc : Fin 9) : Fin 64 := ⟨pc.val,by omega⟩
def borrowLabel (pc : Fin 16) : Fin 64 := ⟨9+pc.val,by omega⟩
def trimLabel (pc : Fin 13) : Fin 64 := ⟨25+pc.val,by omega⟩
def program : Program 64 := fun pc =>
  if pc.val=8 then .ret .r3
  else if pc.val=23 then .ret .r3
  else if pc.val=37 then .ret .r3
  else if h : pc.val<9 then ReferenceProgramLabels.instruction zeroLabel (BinaryZeroProgram.program ⟨pc.val,h⟩)
  else if h : pc.val<25 then ReferenceProgramLabels.instruction borrowLabel (BinaryBorrowProgram.program ⟨pc.val-9,by omega⟩)
  else if h : pc.val<38 then ReferenceProgramLabels.instruction trimLabel (BinaryTrimProgram.program ⟨pc.val-25,by omega⟩)
  else match pc.val with
  | 40 => .call 7 41 .r3
  | 41 => .branch .r3 63 44 42 63
  | 42 => .make .r3 .nil 43
  | 43 => .ret .r3
  | 44 => .call 24 45 .r3
  | 45 => .move .r0 .r3 46
  | 46 => .call 36 47 .r3
  | 47 => .ret .r3
  | 62 => .call 40 63 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 64)) (source : Bits) (pc : Fin 64) : NaturalState 64 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem zero_slots (pc : Fin 9) (h : BinaryZeroProgram.program pc≠.halt) :
    program (zeroLabel pc)=ReferenceProgramLabels.instruction zeroLabel (BinaryZeroProgram.program pc) := by
  by_cases hp : pc.val=8
  · have he : pc=8 := Fin.ext hp
    subst pc;simp [BinaryZeroProgram.program] at h
  · simp [program,zeroLabel,pc.isLt,hp,show ¬pc.val=23 by omega,show ¬pc.val=37 by omega]

theorem borrow_slots (pc : Fin 16) (h : BinaryBorrowProgram.program pc≠.halt) :
    program (borrowLabel pc)=ReferenceProgramLabels.instruction borrowLabel (BinaryBorrowProgram.program pc) := by
  by_cases hp : pc.val=14
  · have he : pc=14 := Fin.ext hp
    subst pc;simp [BinaryBorrowProgram.program] at h
  · simp [program,borrowLabel,show ¬9+pc.val=8 by omega,show ¬9+pc.val=23 by omega,
      show ¬9+pc.val=37 by omega,show ¬9+pc.val<9 by omega,show 9+pc.val<25 by omega]

theorem trim_slots (pc : Fin 13) (h : BinaryTrimProgram.program pc≠.halt) :
    program (trimLabel pc)=ReferenceProgramLabels.instruction trimLabel (BinaryTrimProgram.program pc) := by
  by_cases hp : pc.val=12
  · have he : pc=12 := Fin.ext hp
    subst pc;simp [BinaryTrimProgram.program] at h
  · simp [program,trimLabel,show ¬25+pc.val=8 by omega,show ¬25+pc.val=23 by omega,
      show ¬25+pc.val=37 by omega,show ¬25+pc.val<9 by omega,show ¬25+pc.val<25 by omega,
      show 25+pc.val<38 by omega]

def steps (word : Bits) : ℕ := BinaryZeroProgram.steps word+
  if (isZero word).1 then 6 else BinaryBorrowProgram.steps word+BinaryTrimProgram.steps (predCore word).1+12

def cells (word : Bits) : ℕ :=
  if (isZero word).1 then 2 else 1+BinaryBorrowProgram.cells word+(trim (predCore word).1).1.length
end DirectedFlowCutGap.BinaryPredecessorProgram
