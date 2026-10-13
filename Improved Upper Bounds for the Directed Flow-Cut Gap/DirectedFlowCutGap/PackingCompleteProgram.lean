import DirectedFlowCutGap.ActualPackingParameters

/-! Actual parameter construction followed by actual initialization and finite iteration.
The original input survives both real calls on the same heap. -/
namespace DirectedFlowCutGap.PackingComplete
open BinaryArithmetic ImmutableReferenceSimulation

def parameterLabel (pc : Fin 360) : Fin 8340 := ⟨pc.val,by omega⟩
def runLabel (pc : Fin 7960) : Fin 8340 := ⟨pc.val+360,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 8340) : Instruction C → Instruction 8340
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

def program : Program 8340 := fun pc =>
  if h : pc.val<360 then callable parameterLabel (PackingParameters.program ⟨pc.val,by omega⟩)
  else if h : pc.val<8320 then callable runLabel (PackingRun.program ⟨pc.val-360,by omega⟩)
  else match pc.val with
  | 8320 => .call 310 8321 .r2
  | 8321 => .field .r3 .r2 false 8322
  | 8322 => .field .r2 .r2 true 8323
  | 8323 => .make .r2 (.pair .r1 .r2) 8324
  | 8324 => .move .r1 .r3 8325
  | 8325 => .call 8300 8326 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 8340)) (source : Bits) (pc : Fin 8340) : NaturalState 8340 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem callable_eq {C : ℕ} (label : Fin C → Fin 8340) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

theorem parameter_slots (pc : Fin 360) (h : PackingParameters.program pc≠.halt) :
    program (parameterLabel pc)=ReferenceProgramLabels.instruction parameterLabel (PackingParameters.program pc) := by
  simpa [program,parameterLabel] using callable_eq parameterLabel (PackingParameters.program pc) h

theorem parameter_halt (pc : Fin 360) (h : PackingParameters.program pc=.halt) :
    program (parameterLabel pc)=.ret .r3 := by simp [program,parameterLabel,h,callable]

theorem run_slots (pc : Fin 7960) (h : PackingRun.program pc≠.halt) :
    program (runLabel pc)=ReferenceProgramLabels.instruction runLabel (PackingRun.program pc) := by
  simpa [program,runLabel,show ¬pc.val+360<360 by omega,show pc.val+360<8320 by omega] using
    callable_eq runLabel (PackingRun.program pc) h

theorem run_halt (pc : Fin 7960) (h : PackingRun.program pc=.halt) :
    program (runLabel pc)=.ret .r3 := by
  simp [program,runLabel,show ¬pc.val+360<360 by omega,show pc.val+360<8320 by omega,h,callable]
end DirectedFlowCutGap.PackingComplete
