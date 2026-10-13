import DirectedFlowCutGap.ActualPackingSourceInput

/-! The actual source parser flows directly into the generated-vertex solver.
Its four primitive registers stay live at the handover; no host reconstruction
or ghost return value supplies them. -/
namespace DirectedFlowCutGap.SourcePacking
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation

def inputLabel (pc : Fin 64) : Fin 8490 := ⟨pc.val,by omega⟩
def runLabel (pc : Fin 8420) : Fin 8490 := ⟨pc.val+64,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 8490) : Instruction C → Instruction 8490
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

def program : Program 8490 := fun pc =>
  if pc.val=56 then .call 8474 8485 .r3
  else if h : pc.val<64 then ReferenceProgramLabels.instruction inputLabel
    (PackingSourceInput.program ⟨pc.val,by omega⟩)
  else if h : pc.val<8484 then callable runLabel (EnumeratedPacking.program ⟨pc.val-64,by omega⟩)
  else .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 8490)) (source : Bits) (pc : Fin 8490) : NaturalState 8490 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem input_slots (pc : Fin 64) (h : PackingSourceInput.program pc≠.halt) :
    program (inputLabel pc)=ReferenceProgramLabels.instruction inputLabel (PackingSourceInput.program pc) := by
  have hp : pc.val≠56 := by
    intro he
    have hx : pc=56 := Fin.ext he
    subst pc
    exact h rfl
  simp [program,inputLabel,hp]

theorem callable_eq {C : ℕ} (label : Fin C → Fin 8490) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

theorem run_slots (pc : Fin 8420) (h : EnumeratedPacking.program pc≠.halt) :
    program (runLabel pc)=ReferenceProgramLabels.instruction runLabel (EnumeratedPacking.program pc) := by
  simpa [program,runLabel,show pc.val+64≠56 by omega,show ¬pc.val+64<64 by omega,
    show pc.val+64<8484 by omega] using callable_eq runLabel (EnumeratedPacking.program pc) h

theorem run_halt (pc : Fin 8420) (h : EnumeratedPacking.program pc=.halt) :
    program (runLabel pc)=.ret .r3 := by
  simp [program,runLabel,show pc.val+64≠56 by omega,show ¬pc.val+64<64 by omega,
    show pc.val+64<8484 by omega,h,callable]

end DirectedFlowCutGap.SourcePacking
