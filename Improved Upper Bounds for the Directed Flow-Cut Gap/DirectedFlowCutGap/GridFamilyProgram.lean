import DirectedFlowCutGap.MinimumGuessRange
import DirectedFlowCutGap.BinaryIncrementProgram
import DirectedFlowCutGap.BinaryPredecessorExecution

namespace DirectedFlowCutGap.GridFamily
open ImmutableReferenceSimulation BinaryArithmetic
set_option maxRecDepth 32768

def guessLabel (pc : Fin 10000) : Fin 10180 := ⟨pc.val,by omega⟩
def zeroLabel (pc : Fin 9) : Fin 10180 := ⟨10000+pc.val,by omega⟩
def incrementLabel (pc : Fin 16) : Fin 10180 := ⟨10009+pc.val,by omega⟩
def predecessorLabel (pc : Fin 64) : Fin 10180 := ⟨10025+pc.val,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 10180) : Instruction C → Instruction 10180
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

/-- The loop retains original context, exponent and remaining binary fuel.
Each returned optional guess is retained in order; no loop outcome is supplied. -/
def program : Program 10180 := fun pc =>
  if h : pc.val<10000 then callable guessLabel (MinimumGuess.program ⟨pc.val,h⟩)
  else if h : pc.val<10009 then callable zeroLabel (BinaryZeroProgram.program ⟨pc.val-10000,by omega⟩)
  else if h : pc.val<10025 then callable incrementLabel (BinaryIncrementProgram.program ⟨pc.val-10009,by omega⟩)
  else if h : pc.val<10089 then callable predecessorLabel (BinaryPredecessorProgram.program ⟨pc.val-10025,by omega⟩)
  else match pc.val with
  | 10100 => .move .r0 .r2 10101
  | 10101 => .call 10007 10102 .r3
  | 10102 => .ret .r3
  | 10104 => .move .r0 .r1 10105
  | 10105 => .call 10024 10106 .r3
  | 10106 => .ret .r3
  | 10107 => .move .r0 .r2 10108
  | 10108 => .call 10087 10109 .r3
  | 10109 => .ret .r3
  | 10110 => .move .r3 .r0 10111
  | 10111 => .field .r0 .r3 false 10112
  | 10112 => .field .r3 .r3 true 10113
  | 10113 => .field .r2 .r3 false 10114
  | 10114 => .field .r3 .r3 true 10115
  | 10115 => .call 9998 10116 .r3
  | 10116 => .ret .r3
  | 10130 => .call 10100 10131 .r3
  | 10131 => .branch .r3 10179 10132 10150 10179
  | 10132 => .call 10110 10133 .r3
  | 10133 => .call 10104 10134 .r1
  | 10134 => .call 10107 10135 .r2
  | 10135 => .call 10130 10136 .r2
  | 10136 => .make .r3 (.pair .r3 .r2) 10137
  | 10137 => .ret .r3
  | 10150 => .make .r3 .nil 10151
  | 10151 => .ret .r3
  | 10178 => .call 10130 10179 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 10180)) (source : Bits) (pc : Fin 10180) : NaturalState 10180 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem callable_eq {C : ℕ} (label : Fin C → Fin 10180) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

theorem guess_slots (pc : Fin 10000) (h : MinimumGuess.program pc≠.halt) :
    program (guessLabel pc)=ReferenceProgramLabels.instruction guessLabel (MinimumGuess.program pc) := by
  simpa [program,guessLabel,pc.isLt] using callable_eq guessLabel (MinimumGuess.program pc) h

theorem zero_slots (pc : Fin 9) (h : BinaryZeroProgram.program pc≠.halt) :
    program (zeroLabel pc)=ReferenceProgramLabels.instruction zeroLabel (BinaryZeroProgram.program pc) := by
  simpa [program,zeroLabel,show ¬10000+pc.val<10000 by omega,show 10000+pc.val<10009 by omega] using
    callable_eq zeroLabel (BinaryZeroProgram.program pc) h

theorem increment_slots (pc : Fin 16) (h : BinaryIncrementProgram.program pc≠.halt) :
    program (incrementLabel pc)=ReferenceProgramLabels.instruction incrementLabel (BinaryIncrementProgram.program pc) := by
  simpa [program,incrementLabel,show ¬10009+pc.val<10000 by omega,show ¬10009+pc.val<10009 by omega,
    show 10009+pc.val<10025 by omega] using callable_eq incrementLabel (BinaryIncrementProgram.program pc) h

theorem predecessor_slots (pc : Fin 64) (h : BinaryPredecessorProgram.program pc≠.halt) :
    program (predecessorLabel pc)=ReferenceProgramLabels.instruction predecessorLabel (BinaryPredecessorProgram.program pc) := by
  simpa [program,predecessorLabel,show ¬10025+pc.val<10000 by omega,show ¬10025+pc.val<10009 by omega,
    show ¬10025+pc.val<10025 by omega,show 10025+pc.val<10089 by omega] using
    callable_eq predecessorLabel (BinaryPredecessorProgram.program pc) h
end DirectedFlowCutGap.GridFamily
