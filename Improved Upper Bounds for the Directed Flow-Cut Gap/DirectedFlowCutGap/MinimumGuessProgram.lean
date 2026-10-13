import DirectedFlowCutGap.MinimumShiftRange
import DirectedFlowCutGap.ActualEnumeratedPacking

namespace DirectedFlowCutGap.MinimumGuess
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

def shiftLabel (pc : Fin 1560) : Fin 10000 := ⟨pc.val,by omega⟩
def solveLabel (pc : Fin 8420) : Fin 10000 := ⟨1560+pc.val,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 10000) : Instruction C → Instruction 10000
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

theorem callable_eq {C : ℕ} (label : Fin C → Fin 10000) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

/-- The intermediate call frame retains the original graph and demands while
preparing shifted costs, then restores both for the real full packing solver. -/
def program : Program 10000 := fun pc =>
  if h : pc.val<1560 then callable shiftLabel (MinimumShift.program ⟨pc.val,h⟩)
  else if h : pc.val<9980 then callable solveLabel (EnumeratedPacking.program ⟨pc.val-1560,by omega⟩)
  else match pc.val with
  | 9980 => .move .r2 .r1 9981
  | 9981 => .call 1558 9982 .r3
  | 9982 => .ret .r3
  | 9984 => .call 9980 9985 .r1
  | 9985 => .branch .r1 9991 9999 9999 9986
  | 9986 => .move .r0 .r1 9987
  | 9987 => .call 9970 9988 .r3
  | 9988 => .ret .r3
  | 9991 => .move .r3 .r1 9992
  | 9992 => .ret .r3
  | 9998 => .call 9984 9999 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 10000)) (source : Bits) (pc : Fin 10000) : NaturalState 10000 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem shift_slots (pc : Fin 1560) (h : MinimumShift.program pc≠.halt) :
    program (shiftLabel pc)=ReferenceProgramLabels.instruction shiftLabel (MinimumShift.program pc) := by
  simpa [program,shiftLabel,pc.isLt] using callable_eq shiftLabel (MinimumShift.program pc) h

theorem solve_slots (pc : Fin 8420) (h : EnumeratedPacking.program pc≠.halt) :
    program (solveLabel pc)=ReferenceProgramLabels.instruction solveLabel (EnumeratedPacking.program pc) := by
  simpa [program,solveLabel,show ¬1560+pc.val<1560 by omega,show 1560+pc.val<9980 by omega] using
    callable_eq solveLabel (EnumeratedPacking.program pc) h

def shifted {n : ℕ} (costs : BinaryFractionalRows.Row n) (i : Fin n) (exponent : Bits) : BinaryFractionalRows.Row n :=
  (BinaryFractionalGuesses.shifted costs
    (BinaryFractionalGuesses.lambda costs i (BinaryFractionalCore.dimension costs).1 exponent).1).1

def result {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (ds : List (BinaryFractionalWalkOracle.Pair n)) (costs : BinaryFractionalRows.Row n) (exponent : Bits) :
    Option (BinaryFractionalCore.State n) :=
  (BinaryFractionalDispatch.minimumPositive costs).1.map
    (fun i => (BinaryFractionalGuesses.guess adjacency ds costs i (BinaryFractionalCore.dimension costs).1 exponent).state)

def Result {n : ℕ} (heap : NaturalHeap) (root : ℕ) : Option (BinaryFractionalCore.State n) → Prop
  | none => heap[root]?=some .nil
  | some s => PackingStart.StateRecord heap root RowVertices.vertexLabel s

def shiftedWidth (rows : List Fraction) (exponent : Bits) : ℕ :=
  LambdaRowProgram.rowBits rows+ShiftedGridProgram.scalarWidth rows exponent+2

def inputSteps (d : ℕ) (rows : List Fraction) (exponent : Bits) : ℕ :=
  MinimumShift.inputSteps rows exponent+EnumeratedPacking.instructionBound d rows.length (shiftedWidth rows exponent)+12
end DirectedFlowCutGap.MinimumGuess
