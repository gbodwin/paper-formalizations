import DirectedFlowCutGap.BinaryComparisonProgram
import DirectedFlowCutGap.BinaryFractionalGuesses

namespace DirectedFlowCutGap.BinaryMaximumProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

def label (pc : Fin 48) : Fin 56 := ⟨pc.val,by omega⟩
def program : Program 56 := fun pc =>
  if pc.val=46 then .ret .r3
  else if h : pc.val<48 then
    ReferenceProgramLabels.instruction label (BinaryComparisonProgram.program ⟨pc.val,h⟩)
  else match pc.val with
  | 48 => .call 30 49 .r3
  | 49 => .branch .r3 55 50 51 55
  | 50 => .ret .r0
  | 51 => .ret .r1
  | 54 => .call 48 55 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 56)) (source : Bits) (pc : Fin 56) : NaturalState 56 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem slots (pc : Fin 48) (h : BinaryComparisonProgram.program pc≠.halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (BinaryComparisonProgram.program pc) := by
  by_cases hp : pc.val=46
  · have he : pc=46 := Fin.ext hp
    subst pc;simp [BinaryComparisonProgram.program] at h
  · simp [program,label,pc.isLt,hp]

def steps (xs ys : Bits) : ℕ := BinaryComparisonProgram.steps xs ys+7

def pointer (xs ys : Bits) (a b : ℕ) : ℕ := if (lessEqual xs ys).1 then b else a
end DirectedFlowCutGap.BinaryMaximumProgram
