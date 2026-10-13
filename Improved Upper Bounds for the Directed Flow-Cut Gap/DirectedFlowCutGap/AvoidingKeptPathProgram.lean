import DirectedFlowCutGap.ActualAvoidingShortest
import DirectedFlowCutGap.ActualKeptAdjacencyInput

namespace DirectedFlowCutGap.AvoidingKeptPath
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

def matrixLabel (pc : Fin 320) : Fin 1800 := ⟨pc.val,by omega⟩
def shortestLabel (pc : Fin 1440) : Fin 1800 := ⟨pc.val+320,by omega⟩
def program : Program 1800 := fun pc =>
  if pc.val=319 ∨ pc.val=1759 then .ret .r3
  else if h : pc.val<320 then
    ReferenceProgramLabels.instruction matrixLabel (KeptAdjacencyInput.program ⟨pc.val,h⟩)
  else if h : pc.val<1760 then
    ReferenceProgramLabels.instruction shortestLabel (AvoidingShortest.program ⟨pc.val-320,by omega⟩)
  else match pc.val with
  | 1770 => .make .r2 (.pair .r0 .r1) 1771
  | 1771 => .call 318 1772 .r3
  | 1772 => .field .r1 .r1 false 1773
  | 1773 => .field .r1 .r1 false 1774
  | 1774 => .make .r1 (.pair .r3 .r1) 1775
  | 1775 => .field .r0 .r2 false 1776
  | 1776 => .call 1758 1777 .r3
  | 1777 => .ret .r3
  | 1798 => .call 1770 1799 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 1800)) (source : Bits) (pc : Fin 1800) : NaturalState 1800 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem matrix_slots (pc : Fin 320) (h : KeptAdjacencyInput.program pc≠.halt) :
    program (matrixLabel pc)=ReferenceProgramLabels.instruction matrixLabel (KeptAdjacencyInput.program pc) := by
  by_cases hp : pc.val=319
  · have he : pc=319 := Fin.ext hp
    subst pc;simp [KeptAdjacencyInput.program] at h
  · simp [program,matrixLabel,pc.isLt,hp,show ¬pc.val=1759 by omega]

theorem shortest_slots (pc : Fin 1440) (h : AvoidingShortest.program pc≠.halt) :
    program (shortestLabel pc)=ReferenceProgramLabels.instruction shortestLabel (AvoidingShortest.program pc) := by
  by_cases hp : pc.val=1439
  · have he : pc=1439 := Fin.ext hp
    subst pc;simp [AvoidingShortest.program] at h
  · simp [program,shortestLabel,show ¬pc.val+320=319 by omega,show ¬pc.val+320=1759 by omega,
      show ¬pc.val+320<320 by omega,show pc.val+320<1760 by omega]
end DirectedFlowCutGap.AvoidingKeptPath
