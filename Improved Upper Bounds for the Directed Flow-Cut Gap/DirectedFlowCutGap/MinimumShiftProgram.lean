import DirectedFlowCutGap.OriginalRowMinimumIndex
import DirectedFlowCutGap.ShiftedGridRange

namespace DirectedFlowCutGap.MinimumShift
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

def minimumLabel (pc : Fin 320) : Fin 1560 := ⟨pc.val,by omega⟩
def shiftLabel (pc : Fin 1220) : Fin 1560 := ⟨320+pc.val,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 1560) : Instruction C → Instruction 1560
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

theorem callable_eq {C : ℕ} (label : Fin C → Fin 1560) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

def program : Program 1560 := fun pc =>
  if h : pc.val<320 then callable minimumLabel (OriginalRowMinimum.program ⟨pc.val,h⟩)
  else if h : pc.val<1540 then callable shiftLabel (ShiftedGridProgram.program ⟨pc.val-320,by omega⟩)
  else match pc.val with
  | 1540 => .call 318 1541 .r3
  | 1541 => .branch .r3 1547 1547 1547 1542
  | 1542 => .field .r1 .r3 true 1543
  | 1543 => .call 1538 1544 .r3
  | 1544 => .ret .r3
  | 1547 => .ret .r3
  | 1558 => .call 1540 1559 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 1560)) (source : Bits) (pc : Fin 1560) : NaturalState 1560 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem minimum_slots (pc : Fin 320) (h : OriginalRowMinimum.program pc≠.halt) :
    program (minimumLabel pc)=ReferenceProgramLabels.instruction minimumLabel (OriginalRowMinimum.program pc) := by
  simpa [program,minimumLabel,pc.isLt] using callable_eq minimumLabel (OriginalRowMinimum.program pc) h

theorem shift_slots (pc : Fin 1220) (h : ShiftedGridProgram.program pc≠.halt) :
    program (shiftLabel pc)=ReferenceProgramLabels.instruction shiftLabel (ShiftedGridProgram.program pc) := by
  simpa [program,shiftLabel,show ¬320+pc.val<320 by omega,show 320+pc.val<1540 by omega] using
    callable_eq shiftLabel (ShiftedGridProgram.program pc) h

def result {n : ℕ} (costs : BinaryFractionalRows.Row n) (exponent : Bits) : Option (List Fraction) :=
  (BinaryFractionalDispatch.minimumPositive costs).1.map
    (fun i => ShiftedGridProgram.result costs.toList (RowVertices.vertexLabel i) exponent)

def Result (heap : NaturalHeap) (root : ℕ) : Option (List Fraction) → Prop
  | none => heap[root]?=some .nil
  | some rows => CanonicalRationalSum.StoredList heap root rows

def inputSteps (rows : List Fraction) (exponent : Bits) : ℕ :=
  OriginalRowMinimum.inputSteps rows+
    ShiftedGridProgram.inputSteps rows (List.replicate rows.length false) exponent+8
end DirectedFlowCutGap.MinimumShift
