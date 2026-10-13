import DirectedFlowCutGap.ActualNaturalFraction
import DirectedFlowCutGap.ActualBinaryPower
import DirectedFlowCutGap.BinaryFractionalGuesses

namespace DirectedFlowCutGap.LambdaCoreProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

def naturalLabel (pc : Fin 8) : Fin 432 := ⟨pc.val,by omega⟩
def quotientLabel (pc : Fin 164) : Fin 432 := ⟨8+pc.val,by omega⟩
def powerLabel (pc : Fin 96) : Fin 432 := ⟨172+pc.val,by omega⟩
def productLabel (pc : Fin 132) : Fin 432 := ⟨268+pc.val,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 432) : Instruction C → Instruction 432
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

theorem callable_eq {C : ℕ} (label : Fin C → Fin 432) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

def program : Program 432 := fun pc =>
  if h : pc.val<8 then callable naturalLabel (NaturalFractionProgram.program ⟨pc.val,h⟩)
  else if h : pc.val<172 then callable quotientLabel (CanonicalRationalQuotient.program ⟨pc.val-8,by omega⟩)
  else if h : pc.val<268 then callable powerLabel (BinaryPowerProgram.program ⟨pc.val-172,by omega⟩)
  else if h : pc.val<400 then callable productLabel (CanonicalRationalProduct.program ⟨pc.val-268,by omega⟩)
  else match pc.val with
  | 400 => .make .r3 (.pair .r0 .r1) 401
  | 401 => .make .r2 (.pair .r2 .r3) 402
  | 402 => .move .r0 .r1 403
  | 403 => .call 6 404 .r3
  | 404 => .move .r1 .r3 405
  | 405 => .field .r0 .r2 true 406
  | 406 => .field .r0 .r0 false 407
  | 407 => .call 169 408 .r3
  | 408 => .make .r2 (.pair .r3 .r2) 409
  | 409 => .field .r0 .r2 true 410
  | 410 => .field .r0 .r0 false 411
  | 411 => .call 266 412 .r3
  | 412 => .move .r0 .r3 413
  | 413 => .call 6 414 .r3
  | 414 => .move .r1 .r3 415
  | 415 => .field .r0 .r2 false 416
  | 416 => .call 398 417 .r3
  | 417 => .ret .r3
  | 430 => .call 400 431 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 432)) (source : Bits) (pc : Fin 432) : NaturalState 432 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem natural_slots (pc : Fin 8) (h : NaturalFractionProgram.program pc≠.halt) :
    program (naturalLabel pc)=ReferenceProgramLabels.instruction naturalLabel (NaturalFractionProgram.program pc) := by
  simpa [program,naturalLabel,pc.isLt] using callable_eq naturalLabel (NaturalFractionProgram.program pc) h

theorem quotient_slots (pc : Fin 164) (h : CanonicalRationalQuotient.program pc≠.halt) :
    program (quotientLabel pc)=ReferenceProgramLabels.instruction quotientLabel (CanonicalRationalQuotient.program pc) := by
  simpa [program,quotientLabel,show ¬8+pc.val<8 by omega,show 8+pc.val<172 by omega] using
    callable_eq quotientLabel (CanonicalRationalQuotient.program pc) h

theorem power_slots (pc : Fin 96) (h : BinaryPowerProgram.program pc≠.halt) :
    program (powerLabel pc)=ReferenceProgramLabels.instruction powerLabel (BinaryPowerProgram.program pc) := by
  simpa [program,powerLabel,show ¬172+pc.val<8 by omega,show ¬172+pc.val<172 by omega,
    show 172+pc.val<268 by omega] using callable_eq powerLabel (BinaryPowerProgram.program pc) h

theorem product_slots (pc : Fin 132) (h : CanonicalRationalProduct.program pc≠.halt) :
    program (productLabel pc)=ReferenceProgramLabels.instruction productLabel (CanonicalRationalProduct.program pc) := by
  simpa [program,productLabel,show ¬268+pc.val<8 by omega,show ¬268+pc.val<172 by omega,
    show ¬268+pc.val<268 by omega,show 268+pc.val<400 by omega] using
    callable_eq productLabel (CanonicalRationalProduct.program pc) h

def quotient (x : Fraction) (dimension : Bits) : Fraction :=
  (BinaryRational.div x (BinaryFractionalCore.naturalFraction dimension)).1
def power (exponent : Bits) : Bits := (BinaryCounters.powerOfTwoBinary exponent).1
def result (x : Fraction) (dimension exponent : Bits) : Fraction :=
  (BinaryRational.mul (quotient x dimension) (BinaryFractionalCore.naturalFraction (power exponent))).1
def steps (x : Fraction) (dimension exponent : Bits) : ℕ :=
  CanonicalRationalQuotient.steps x (BinaryFractionalCore.naturalFraction dimension)+
  BinaryPowerProgram.steps exponent+
  CanonicalRationalProduct.instructions (quotient x dimension) (BinaryFractionalCore.naturalFraction (power exponent))+38
def cells (x : Fraction) (dimension exponent : Bits) : ℕ :=
  CanonicalRationalQuotient.cells x (BinaryFractionalCore.naturalFraction dimension)+
  BinaryPowerProgram.cells exponent+
  CanonicalRationalProduct.cells (quotient x dimension) (BinaryFractionalCore.naturalFraction (power exponent))+11
end DirectedFlowCutGap.LambdaCoreProgram
