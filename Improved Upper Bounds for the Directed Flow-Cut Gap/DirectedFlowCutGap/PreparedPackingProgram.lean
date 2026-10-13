import DirectedFlowCutGap.PackingInputConstruction

/-! Actual primitive-list metadata assembly followed by complete packing.
The same original roots survive both real calls on the same heap. -/
namespace DirectedFlowCutGap.PreparedPacking
open BinaryArithmetic ImmutableReferenceSimulation

def inputLabel (pc : Fin 6) : Fin 8360 := ⟨pc.val,by omega⟩
def runLabel (pc : Fin 8340) : Fin 8360 := ⟨pc.val+6,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 8360) : Instruction C → Instruction 8360
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

def program : Program 8360 := fun pc =>
  if h : pc.val<6 then callable inputLabel (PackingInput.program ⟨pc.val,by omega⟩)
  else if h : pc.val<8346 then callable runLabel (PackingComplete.program ⟨pc.val-6,by omega⟩)
  else match pc.val with
  | 8348 => .call 0 8349 .r1
  | 8349 => .call 8326 8350 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 8360)) (source : Bits) (pc : Fin 8360) : NaturalState 8360 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem callable_eq {C : ℕ} (label : Fin C → Fin 8360) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

theorem input_slots (pc : Fin 6) (h : PackingInput.program pc≠.halt) :
    program (inputLabel pc)=ReferenceProgramLabels.instruction inputLabel (PackingInput.program pc) := by
  simpa [program,inputLabel] using callable_eq inputLabel (PackingInput.program pc) h

theorem input_halt (pc : Fin 6) (h : PackingInput.program pc=.halt) :
    program (inputLabel pc)=.ret .r3 := by simp [program,inputLabel,h,callable]

theorem run_slots (pc : Fin 8340) (h : PackingComplete.program pc≠.halt) :
    program (runLabel pc)=ReferenceProgramLabels.instruction runLabel (PackingComplete.program pc) := by
  simpa [program,runLabel,show ¬pc.val+6<6 by omega,show pc.val+6<8346 by omega] using
    callable_eq runLabel (PackingComplete.program pc) h

theorem run_halt (pc : Fin 8340) (h : PackingComplete.program pc=.halt) :
    program (runLabel pc)=.ret .r3 := by
  simp [program,runLabel,show ¬pc.val+6<6 by omega,show pc.val+6<8346 by omega,h,callable]
end DirectedFlowCutGap.PreparedPacking
