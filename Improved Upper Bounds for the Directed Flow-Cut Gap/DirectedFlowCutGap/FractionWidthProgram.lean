import DirectedFlowCutGap.ActualBinarySize
import DirectedFlowCutGap.ActualBinaryMaximum
import DirectedFlowCutGap.RationalComparisonProgram

namespace DirectedFlowCutGap.FractionWidthProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

def sizeLabel (pc : Fin 48) : Fin 128 := ⟨pc.val,by omega⟩
def maxLabel (pc : Fin 56) : Fin 128 := ⟨48+pc.val,by omega⟩
def program : Program 128 := fun pc =>
  if pc.val=47 then .ret .r3
  else if pc.val=103 then .ret .r3
  else if h : pc.val<48 then
    ReferenceProgramLabels.instruction sizeLabel (BinarySizeProgram.program ⟨pc.val,h⟩)
  else if h : pc.val<104 then
    ReferenceProgramLabels.instruction maxLabel (BinaryMaximumProgram.program ⟨pc.val-48,by omega⟩)
  else match pc.val with
  | 110 => .move .r2 .r0 111
  | 111 => .field .r0 .r0 false 112
  | 112 => .call 46 113 .r3
  | 113 => .move .r1 .r3 114
  | 114 => .field .r0 .r2 true 115
  | 115 => .call 46 116 .r3
  | 116 => .move .r0 .r1 117
  | 117 => .move .r1 .r3 118
  | 118 => .call 102 119 .r3
  | 119 => .ret .r3
  | 126 => .call 110 127 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 128)) (source : Bits) (pc : Fin 128) : NaturalState 128 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem size_slots (pc : Fin 48) (h : BinarySizeProgram.program pc≠.halt) :
    program (sizeLabel pc)=ReferenceProgramLabels.instruction sizeLabel (BinarySizeProgram.program pc) := by
  by_cases hp : pc.val=47
  · have he : pc=47 := Fin.ext hp
    subst pc;simp [BinarySizeProgram.program] at h
  · simp [program,sizeLabel,pc.isLt,hp,show ¬pc.val=103 by omega]

theorem max_slots (pc : Fin 56) (h : BinaryMaximumProgram.program pc≠.halt) :
    program (maxLabel pc)=ReferenceProgramLabels.instruction maxLabel (BinaryMaximumProgram.program pc) := by
  by_cases hp : pc.val=55
  · have he : pc=55 := Fin.ext hp
    subst pc;simp [BinaryMaximumProgram.program] at h
  · simp [program,maxLabel,show ¬48+pc.val=47 by omega,show ¬48+pc.val=103 by omega,
      show ¬48+pc.val<48 by omega,show 48+pc.val<104 by omega]

def steps (q : BinaryRational.Fraction) : ℕ :=
  BinarySizeProgram.steps q.num+BinarySizeProgram.steps q.den+
    BinaryMaximumProgram.steps (BinaryCounters.sizeBits q.num).1 (BinaryCounters.sizeBits q.den).1+16

def cells (q : BinaryRational.Fraction) : ℕ :=
  BinarySizeProgram.cells q.num+BinarySizeProgram.cells q.den+
    BinaryComparisonProgram.cells (BinaryCounters.sizeBits q.num).1 (BinaryCounters.sizeBits q.den).1+1
end DirectedFlowCutGap.FractionWidthProgram
