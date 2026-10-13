import DirectedFlowCutGap.ActualGridFuel
import DirectedFlowCutGap.ActualInputWidth
import DirectedFlowCutGap.PackingSourceContracts
import DirectedFlowCutGap.PackingParametersSpecification

namespace DirectedFlowCutGap.GridInputProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

def widthLabel (pc : Fin 208) : Fin 544 := ⟨pc.val,by omega⟩
def lengthLabel (pc : Fin 24) : Fin 544 := ⟨208+pc.val,by omega⟩
def fuelLabel (pc : Fin 256) : Fin 544 := ⟨232+pc.val,by omega⟩
def program : Program 544 := fun pc =>
  if pc.val=207 then .ret .r3
  else if pc.val=230 then .ret .r1
  else if pc.val=487 then .ret .r3
  else if h : pc.val<208 then
    ReferenceProgramLabels.instruction widthLabel (InputWidthProgram.program ⟨pc.val,h⟩)
  else if h : pc.val<232 then
    ReferenceProgramLabels.instruction lengthLabel (BinaryLengthProgram.program ⟨pc.val-208,by omega⟩)
  else if h : pc.val<488 then
    ReferenceProgramLabels.instruction fuelLabel (GridFuelProgram.program ⟨pc.val-232,by omega⟩)
  else match pc.val with
  | 500 => .move .r2 .r0 501
  | 501 => .call 206 502 .r3
  | 502 => .move .r1 .r3 503
  | 503 => .move .r0 .r2 504
  | 504 => .call 224 505 .r3
  | 505 => .move .r0 .r3 506
  | 506 => .call 486 507 .r3
  | 507 => .make .r1 (.pair .r0 .r1) 508
  | 508 => .make .r3 (.pair .r1 .r3) 509
  | 509 => .ret .r3
  | 542 => .call 500 543 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 544)) (source : Bits) (pc : Fin 544) : NaturalState 544 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem width_slots (pc : Fin 208) (h : InputWidthProgram.program pc≠.halt) :
    program (widthLabel pc)=ReferenceProgramLabels.instruction widthLabel (InputWidthProgram.program pc) := by
  by_cases hp : pc.val=207
  · have he : pc=207 := Fin.ext hp
    subst pc;simp [InputWidthProgram.program] at h
  · simp [program,widthLabel,pc.isLt,hp,show ¬pc.val=230 by omega,show ¬pc.val=487 by omega]

theorem length_slots (pc : Fin 24) (h : BinaryLengthProgram.program pc≠.halt) :
    program (lengthLabel pc)=ReferenceProgramLabels.instruction lengthLabel (BinaryLengthProgram.program pc) := by
  by_cases hp : pc.val=22
  · have he : pc=22 := Fin.ext hp
    subst pc;simp [BinaryLengthProgram.program] at h
  · simp [program,lengthLabel,show ¬208+pc.val=207 by omega,show ¬208+pc.val=230 by omega,
      show ¬208+pc.val=487 by omega,show ¬208+pc.val<208 by omega,show 208+pc.val<232 by omega]

theorem fuel_slots (pc : Fin 256) (h : GridFuelProgram.program pc≠.halt) :
    program (fuelLabel pc)=ReferenceProgramLabels.instruction fuelLabel (GridFuelProgram.program pc) := by
  by_cases hp : pc.val=255
  · have he : pc=255 := Fin.ext hp
    subst pc;simp [GridFuelProgram.program] at h
  · simp [program,fuelLabel,show ¬232+pc.val=207 by omega,show ¬232+pc.val=230 by omega,
      show ¬232+pc.val=487 by omega,show ¬232+pc.val<208 by omega,show ¬232+pc.val<232 by omega,
      show 232+pc.val<488 by omega]

def dimension (rows : List Fraction) : Bits := BinaryLengthProgram.countWord rows.length []
def width (rows : List Fraction) : Bits := (BinaryFractionalGuesses.widthList rows).1

def Prepared (heap : NaturalHeap) (root : ℕ) (rows : List Fraction) : Prop :=
  ∃ pair dim wid fuel,heap[root]?=some (.pair pair fuel) ∧ heap[pair]?=some (.pair dim wid) ∧
    BoolList heap dim (dimension rows) ∧ BoolList heap wid (width rows) ∧
    BoolList heap fuel (BinaryFractionalGuesses.gridFuel (dimension rows) (width rows)).1

def steps (rows : List Fraction) : ℕ := InputWidthProgram.steps rows+
  BinaryLengthProgram.scanSteps rows.length []+GridFuelProgram.steps (dimension rows) (width rows)+16

def cells (rows : List Fraction) : ℕ := InputWidthProgram.cells rows+
  BinaryLengthProgram.scanCells rows.length []+GridFuelProgram.cells (dimension rows) (width rows)+3
end DirectedFlowCutGap.GridInputProgram
