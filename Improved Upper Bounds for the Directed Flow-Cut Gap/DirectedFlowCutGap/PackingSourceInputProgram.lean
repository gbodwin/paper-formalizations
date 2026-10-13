import DirectedFlowCutGap.SourceMatrixExecution

/-! Three actual self-delimited source-table calls followed by the real
first-column projection. Capacity, matrix and demand cells are allocated here. -/
namespace DirectedFlowCutGap.PackingSourceInput
open BinaryArithmetic ImmutableReferenceSimulation

def inputLabel (pc : Fin 32) : Fin 64 := ⟨pc.val,by omega⟩
def runLabel (pc : Fin 16) : Fin 64 := ⟨pc.val+32,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 64) : Instruction C → Instruction 64
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

def program : Program 64 := fun pc =>
  if h : pc.val<32 then callable inputLabel (SourceRowTableProgram.program ⟨pc.val,by omega⟩)
  else if h : pc.val<48 then callable runLabel (SourceMatrixProjection.program ⟨pc.val-32,by omega⟩)
  else match pc.val with
  | 48 => .call 30 49 .r0
  | 49 => .call 30 50 .r1
  | 50 => .call 30 51 .r3
  | 51 => .move .r2 .r0 52
  | 52 => .move .r0 .r1 53
  | 53 => .call 46 54 .r1
  | 54 => .move .r0 .r2 55
  | 55 => .move .r2 .r1 56
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 64)) (source : Bits) (pc : Fin 64) : NaturalState 64 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem callable_eq {C : ℕ} (label : Fin C → Fin 64) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

theorem input_slots (pc : Fin 32) (h : SourceRowTableProgram.program pc≠.halt) :
    program (inputLabel pc)=ReferenceProgramLabels.instruction inputLabel (SourceRowTableProgram.program pc) := by
  simpa [program,inputLabel] using callable_eq inputLabel (SourceRowTableProgram.program pc) h

theorem input_halt (pc : Fin 32) (h : SourceRowTableProgram.program pc=.halt) :
    program (inputLabel pc)=.ret .r3 := by simp [program,inputLabel,h,callable]

theorem run_slots (pc : Fin 16) (h : SourceMatrixProjection.program pc≠.halt) :
    program (runLabel pc)=ReferenceProgramLabels.instruction runLabel (SourceMatrixProjection.program pc) := by
  simpa [program,runLabel,show ¬pc.val+32<32 by omega,show pc.val+32<48 by omega] using
    callable_eq runLabel (SourceMatrixProjection.program pc) h

theorem run_halt (pc : Fin 16) (h : SourceMatrixProjection.program pc=.halt) :
    program (runLabel pc)=.ret .r3 := by
  simp [program,runLabel,show ¬pc.val+32<32 by omega,show pc.val+32<48 by omega,h,callable]
end DirectedFlowCutGap.PackingSourceInput
