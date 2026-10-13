import DirectedFlowCutGap.PackingDimension

namespace DirectedFlowCutGap.PackingParameters
open BinaryArithmetic ImmutableReferenceSimulation

def lengthLabel (pc : Fin 24) : Fin 360 := ⟨pc.val,by omega⟩
def arithmeticLabel (pc : Fin 116) : Fin 360 := ⟨pc.val+24,by omega⟩
def quotientLabel (pc : Fin 164) : Fin 360 := ⟨pc.val+140,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 360) (result : Reg) : Instruction C → Instruction 360
  | .halt => .ret result
  | op => ReferenceProgramLabels.instruction label op

/-- The row length is counted by actual increments; the same canonical product
supplies both the fuel and the denominator used by actual rational division. -/
def program : Program 360 := fun pc =>
  if h : pc.val<24 then callable lengthLabel .r1 (BinaryLengthProgram.program ⟨pc.val,h⟩)
  else if h : pc.val<140 then callable arithmeticLabel .r3 (CanonicalArithmeticProgram.program ⟨pc.val-24,by omega⟩)
  else if h : pc.val<304 then callable quotientLabel .r3 (CanonicalRationalQuotient.program ⟨pc.val-140,by omega⟩)
  else match pc.val with
  | 310 => .call 16 311 .r0
  | 311 => .move .r1 .r0 312
  | 312 => .call 134 313 .r1
  | 313 => .make .r0 .nil 314
  | 314 => .make .r3 (.flag true) 315
  | 315 => .make .r0 (.pair .r3 .r0) 316
  | 316 => .make .r0 (.pair .r3 .r0) 317
  | 317 => .call 134 318 .r3
  | 318 => .make .r0 .nil 319
  | 319 => .make .r1 (.flag true) 320
  | 320 => .make .r0 (.pair .r1 .r0) 321
  | 321 => .make .r1 (.pair .r3 .r0) 322
  | 322 => .move .r2 .r3 323
  | 323 => .make .r3 (.flag false) 324
  | 324 => .make .r3 (.pair .r3 .r0) 325
  | 325 => .make .r0 (.pair .r3 .r0) 326
  | 326 => .call 301 327 .r3
  | 327 => .make .r3 (.pair .r3 .r2) 328
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 360)) (source : Bits) (pc : Fin 360) : NaturalState 360 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem callable_eq {C : ℕ} (label : Fin C → Fin 360) (result : Reg) (op : Instruction C) (h : op≠.halt) :
    callable label result op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

theorem length_slots (pc : Fin 24) (h : BinaryLengthProgram.program pc≠.halt) :
    program (lengthLabel pc)=ReferenceProgramLabels.instruction lengthLabel (BinaryLengthProgram.program pc) := by
  simpa [program,lengthLabel,pc.isLt] using callable_eq lengthLabel .r1 (BinaryLengthProgram.program pc) h

theorem length_halt (pc : Fin 24) (h : BinaryLengthProgram.program pc=.halt) :
    program (lengthLabel pc)=.ret .r1 := by simp [program,lengthLabel,pc.isLt,h,callable]

theorem arithmetic_slots (pc : Fin 116) (h : CanonicalArithmeticProgram.program pc≠.halt) :
    program (arithmeticLabel pc)=ReferenceProgramLabels.instruction arithmeticLabel (CanonicalArithmeticProgram.program pc) := by
  simpa [program,arithmeticLabel,show ¬pc.val+24<24 by omega,show pc.val+24<140 by omega] using
    callable_eq arithmeticLabel .r3 (CanonicalArithmeticProgram.program pc) h

theorem arithmetic_halt (pc : Fin 116) (h : CanonicalArithmeticProgram.program pc=.halt) :
    program (arithmeticLabel pc)=.ret .r3 := by
  simp [program,arithmeticLabel,show ¬pc.val+24<24 by omega,show pc.val+24<140 by omega,h,callable]

theorem quotient_slots (pc : Fin 164) (h : CanonicalRationalQuotient.program pc≠.halt) :
    program (quotientLabel pc)=ReferenceProgramLabels.instruction quotientLabel (CanonicalRationalQuotient.program pc) := by
  simpa [program,quotientLabel,show ¬pc.val+140<24 by omega,show ¬pc.val+140<140 by omega,show pc.val+140<304 by omega] using
    callable_eq quotientLabel .r3 (CanonicalRationalQuotient.program pc) h

theorem quotient_halt (pc : Fin 164) (h : CanonicalRationalQuotient.program pc=.halt) :
    program (quotientLabel pc)=.ret .r3 := by
  simp [program,quotientLabel,show ¬pc.val+140<24 by omega,show ¬pc.val+140<140 by omega,show pc.val+140<304 by omega,h,callable]
end DirectedFlowCutGap.PackingParameters
