import DirectedFlowCutGap.ActualGridFamily
import DirectedFlowCutGap.OriginalGridInput

namespace DirectedFlowCutGap.GridFamilyInput
open BinaryArithmetic ImmutableReferenceSimulation
set_option maxRecDepth 32768

def familyLabel (pc : Fin 10180) : Fin 10760 := ⟨pc.val,by omega⟩
def gridLabel (pc : Fin 544) : Fin 10760 := ⟨10180+pc.val,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 10760) : Instruction C → Instruction 10760
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

/-- Original cost, graph and demand roots are the only input fields. -/
def program : Program 10760 := fun pc =>
  if h : pc.val<10180 then callable familyLabel (GridFamily.program ⟨pc.val,h⟩)
  else if h : pc.val<10724 then callable gridLabel (GridInputProgram.program ⟨pc.val-10180,by omega⟩)
  else match pc.val with
  | 10730 => .call 10722 10731 .r3
  | 10731 => .make .r1 (.pair .r1 .r2) 10732
  | 10732 => .make .r0 (.pair .r0 .r1) 10733
  | 10733 => .field .r2 .r3 true 10734
  | 10734 => .make .r1 .nil 10735
  | 10735 => .call 10178 10736 .r3
  | 10736 => .ret .r3
  | 10758 => .call 10730 10759 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 10760)) (source : Bits) (pc : Fin 10760) : NaturalState 10760 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem callable_eq {C : ℕ} (label : Fin C → Fin 10760) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

theorem family_slots (pc : Fin 10180) (h : GridFamily.program pc≠.halt) :
    program (familyLabel pc)=ReferenceProgramLabels.instruction familyLabel (GridFamily.program pc) := by
  simpa [program,familyLabel,pc.isLt] using callable_eq familyLabel (GridFamily.program pc) h

theorem grid_slots (pc : Fin 544) (h : GridInputProgram.program pc≠.halt) :
    program (gridLabel pc)=ReferenceProgramLabels.instruction gridLabel (GridInputProgram.program pc) := by
  simpa [program,gridLabel,show ¬10180+pc.val<10180 by omega,show 10180+pc.val<10724 by omega] using
    callable_eq gridLabel (GridInputProgram.program pc) h

def fuel (rows : List BinaryRational.Fraction) : Bits :=
  (BinaryFractionalGuesses.gridFuel (GridInputProgram.dimension rows) (GridInputProgram.width rows)).1

def inputSteps (d : ℕ) (rows : List BinaryRational.Fraction) : ℕ :=
  GridInputProgram.inputSteps rows+GridFamily.instructionBound d rows [] (fuel rows)+16
end DirectedFlowCutGap.GridFamilyInput
