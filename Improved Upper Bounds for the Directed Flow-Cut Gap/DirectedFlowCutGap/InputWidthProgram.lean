import DirectedFlowCutGap.ActualFractionWidth
import DirectedFlowCutGap.IndexedRationalRead

namespace DirectedFlowCutGap.InputWidthProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

def widthLabel (pc : Fin 128) : Fin 208 := ⟨pc.val,by omega⟩
def maxLabel (pc : Fin 56) : Fin 208 := ⟨128+pc.val,by omega⟩
def program : Program 208 := fun pc =>
  if pc.val=127 then .ret .r3
  else if pc.val=183 then .ret .r3
  else if h : pc.val<128 then
    ReferenceProgramLabels.instruction widthLabel (FractionWidthProgram.program ⟨pc.val,h⟩)
  else if h : pc.val<184 then
    ReferenceProgramLabels.instruction maxLabel (BinaryMaximumProgram.program ⟨pc.val-128,by omega⟩)
  else match pc.val with
  | 190 => .branch .r0 191 207 207 194
  | 191 => .make .r3 .nil 192
  | 192 => .ret .r3
  | 194 => .move .r2 .r0 195
  | 195 => .field .r0 .r0 false 196
  | 196 => .call 126 197 .r3
  | 197 => .move .r1 .r3 198
  | 198 => .field .r0 .r2 true 199
  | 199 => .call 190 200 .r3
  | 200 => .move .r0 .r1 201
  | 201 => .move .r1 .r3 202
  | 202 => .call 182 203 .r3
  | 203 => .ret .r3
  | 206 => .call 190 207 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 208)) (source : Bits) (pc : Fin 208) : NaturalState 208 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem width_slots (pc : Fin 128) (h : FractionWidthProgram.program pc≠.halt) :
    program (widthLabel pc)=ReferenceProgramLabels.instruction widthLabel (FractionWidthProgram.program pc) := by
  by_cases hp : pc.val=127
  · have he : pc=127 := Fin.ext hp
    subst pc;simp [FractionWidthProgram.program] at h
  · simp [program,widthLabel,pc.isLt,hp,show ¬pc.val=183 by omega]

theorem max_slots (pc : Fin 56) (h : BinaryMaximumProgram.program pc≠.halt) :
    program (maxLabel pc)=ReferenceProgramLabels.instruction maxLabel (BinaryMaximumProgram.program pc) := by
  by_cases hp : pc.val=55
  · have he : pc=55 := Fin.ext hp
    subst pc;simp [BinaryMaximumProgram.program] at h
  · simp [program,maxLabel,show ¬128+pc.val=127 by omega,show ¬128+pc.val=183 by omega,
      show ¬128+pc.val<128 by omega,show 128+pc.val<184 by omega]

def steps : List BinaryRational.Fraction → ℕ
  | [] => 3
  | q::qs => FractionWidthProgram.steps q+steps qs+
      BinaryMaximumProgram.steps (BinaryFractionalGuesses.fractionWidth q).1 (BinaryFractionalGuesses.widthList qs).1+15

def cells : List BinaryRational.Fraction → ℕ
  | [] => 1
  | q::qs => FractionWidthProgram.cells q+cells qs+
      BinaryComparisonProgram.cells (BinaryFractionalGuesses.fractionWidth q).1 (BinaryFractionalGuesses.widthList qs).1+1
end DirectedFlowCutGap.InputWidthProgram
