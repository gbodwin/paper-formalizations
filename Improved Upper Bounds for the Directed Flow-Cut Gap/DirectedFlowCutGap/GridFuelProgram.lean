import DirectedFlowCutGap.ActualBinarySize
import DirectedFlowCutGap.CanonicalArithmeticProgram
import DirectedFlowCutGap.BinaryFractionalGuesses

namespace DirectedFlowCutGap.GridFuelProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

def arithmeticLabel (pc : Fin 116) : Fin 256 := ⟨pc.val,by omega⟩
def sizeLabel (pc : Fin 48) : Fin 256 := ⟨116+pc.val,by omega⟩
def program : Program 256 := fun pc =>
  if pc.val=115 then .ret .r3
  else if pc.val=163 then .ret .r3
  else if h : pc.val<116 then
    ReferenceProgramLabels.instruction arithmeticLabel (CanonicalArithmeticProgram.program ⟨pc.val,h⟩)
  else if h : pc.val<164 then
    ReferenceProgramLabels.instruction sizeLabel (BinarySizeProgram.program ⟨pc.val-116,by omega⟩)
  else match pc.val with
  | 200 => .move .r2 .r0 201
  | 201 => .call 162 202 .r3
  | 202 => .move .r2 .r3 203
  | 203 => .make .r0 .nil 204
  | 204 => .make .r3 (.flag true) 205
  | 205 => .make .r0 (.pair .r3 .r0) 206
  | 206 => .make .r3 (.flag false) 207
  | 207 => .make .r0 (.pair .r3 .r0) 208
  | 208 => .call 110 209 .r3
  | 209 => .move .r1 .r2 210
  | 210 => .move .r2 .r3 211
  | 211 => .call 110 212 .r3
  | 212 => .move .r0 .r2 213
  | 213 => .move .r1 .r3 214
  | 214 => .call 114 215 .r3
  | 215 => .move .r0 .r3 216
  | 216 => .make .r1 .nil 217
  | 217 => .make .r3 (.flag true) 218
  | 218 => .make .r1 (.pair .r3 .r1) 219
  | 219 => .make .r1 (.pair .r3 .r1) 220
  | 220 => .call 114 221 .r3
  | 221 => .ret .r3
  | 254 => .call 200 255 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 256)) (source : Bits) (pc : Fin 256) : NaturalState 256 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem arithmetic_slots (pc : Fin 116) (h : CanonicalArithmeticProgram.program pc≠.halt) :
    program (arithmeticLabel pc)=ReferenceProgramLabels.instruction arithmeticLabel (CanonicalArithmeticProgram.program pc) := by
  by_cases hp : pc.val=115
  · have he : pc=115 := Fin.ext hp
    subst pc;simp [CanonicalArithmeticProgram.program] at h
  · simp [program,arithmeticLabel,pc.isLt,hp,show ¬pc.val=163 by omega]

theorem size_slots (pc : Fin 48) (h : BinarySizeProgram.program pc≠.halt) :
    program (sizeLabel pc)=ReferenceProgramLabels.instruction sizeLabel (BinarySizeProgram.program pc) := by
  by_cases hp : pc.val=47
  · have he : pc=47 := Fin.ext hp
    subst pc;simp [BinarySizeProgram.program] at h
  · simp [program,sizeLabel,show ¬116+pc.val=115 by omega,show ¬116+pc.val=163 by omega,
      show ¬116+pc.val<116 by omega,show 116+pc.val<164 by omega]

def steps (dimension width : Bits) : ℕ :=
  let size := (BinaryCounters.sizeBits dimension).1
  let twiceW := (mulCanonical [false,true] width).1
  let twiceN := (mulCanonical [false,true] size).1
  let sum := (addCanonical twiceW twiceN).1
  BinarySizeProgram.steps dimension+CanonicalArithmeticProgram.instructions true [false,true] width+
    CanonicalArithmeticProgram.instructions true [false,true] size+
    CanonicalArithmeticProgram.instructions false twiceW twiceN+
    CanonicalArithmeticProgram.instructions false sum [true,true]+28

def arithmeticCells (product : Bool) (xs ys : Bits) : ℕ :=
  CanonicalArithmeticProgram.rawCells product xs ys+(CanonicalArithmeticProgram.result product xs ys).length

def cells (dimension width : Bits) : ℕ :=
  let size := (BinaryCounters.sizeBits dimension).1
  let twiceW := (mulCanonical [false,true] width).1
  let twiceN := (mulCanonical [false,true] size).1
  let sum := (addCanonical twiceW twiceN).1
  BinarySizeProgram.cells dimension+arithmeticCells true [false,true] width+
    arithmeticCells true [false,true] size+arithmeticCells false twiceW twiceN+
    arithmeticCells false sum [true,true]+9
end DirectedFlowCutGap.GridFuelProgram
