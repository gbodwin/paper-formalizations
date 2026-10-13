import DirectedFlowCutGap.RowVerticesLabels

/-! Actual primitive-list metadata assembly followed by complete packing.
The same original roots survive both real calls on the same heap. -/
namespace DirectedFlowCutGap.EnumeratedPacking
open BinaryArithmetic ImmutableReferenceSimulation

def inputLabel (pc : Fin 44) : Fin 8420 := ⟨pc.val,by omega⟩
def runLabel (pc : Fin 8360) : Fin 8420 := ⟨pc.val+44,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 8420) : Instruction C → Instruction 8420
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

def program : Program 8420 := fun pc =>
  if h : pc.val<44 then callable inputLabel (RowVertices.program ⟨pc.val,by omega⟩)
  else if h : pc.val<8404 then callable runLabel (PreparedPacking.program ⟨pc.val-44,by omega⟩)
  else match pc.val with
  | 8410 => .call 40 8411 .r1
  | 8411 => .call 8392 8412 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 8420)) (source : Bits) (pc : Fin 8420) : NaturalState 8420 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem callable_eq {C : ℕ} (label : Fin C → Fin 8420) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

theorem input_slots (pc : Fin 44) (h : RowVertices.program pc≠.halt) :
    program (inputLabel pc)=ReferenceProgramLabels.instruction inputLabel (RowVertices.program pc) := by
  simpa [program,inputLabel] using callable_eq inputLabel (RowVertices.program pc) h

theorem input_halt (pc : Fin 44) (h : RowVertices.program pc=.halt) :
    program (inputLabel pc)=.ret .r3 := by simp [program,inputLabel,h,callable]

theorem run_slots (pc : Fin 8360) (h : PreparedPacking.program pc≠.halt) :
    program (runLabel pc)=ReferenceProgramLabels.instruction runLabel (PreparedPacking.program pc) := by
  simpa [program,runLabel,show ¬pc.val+44<44 by omega,show pc.val+44<8404 by omega] using
    callable_eq runLabel (PreparedPacking.program pc) h

theorem run_halt (pc : Fin 8360) (h : PreparedPacking.program pc=.halt) :
    program (runLabel pc)=.ret .r3 := by
  simp [program,runLabel,show ¬pc.val+44<44 by omega,show pc.val+44<8404 by omega,h,callable]
end DirectedFlowCutGap.EnumeratedPacking
