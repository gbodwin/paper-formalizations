import DirectedFlowCutGap.ActualPackingIteration

/-! Actual initialization followed by actual represented-fuel iteration.
The original input/fuel context survives both real calls on the same heap. -/
namespace DirectedFlowCutGap.PackingRun
open BinaryArithmetic ImmutableReferenceSimulation

def startLabel (pc : Fin 3060) : Fin 7960 := ⟨pc.val,by omega⟩
def iterationLabel (pc : Fin 4860) : Fin 7960 := ⟨pc.val+3060,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 7960) : Instruction C → Instruction 7960
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

def program : Program 7960 := fun pc =>
  if h : pc.val<3060 then callable startLabel (PackingStart.program ⟨pc.val,by omega⟩)
  else if h : pc.val<7920 then callable iterationLabel (PackingIteration.program ⟨pc.val-3060,by omega⟩)
  else match pc.val with
  | 7940 => .make .r3 (.pair .r0 .r2) 7941
  | 7941 => .field .r2 .r2 false 7942
  | 7942 => .call 3020 7943 .r1
  | 7943 => .field .r2 .r3 true 7944
  | 7944 => .call 7880 7945 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 7960)) (source : Bits) (pc : Fin 7960) : NaturalState 7960 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem callable_eq {C : ℕ} (label : Fin C → Fin 7960) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

theorem start_slots (pc : Fin 3060) (h : PackingStart.program pc≠.halt) :
    program (startLabel pc)=ReferenceProgramLabels.instruction startLabel (PackingStart.program pc) := by
  simpa [program,startLabel] using callable_eq startLabel (PackingStart.program pc) h

theorem start_halt (pc : Fin 3060) (h : PackingStart.program pc=.halt) :
    program (startLabel pc)=.ret .r3 := by simp [program,startLabel,h,callable]

theorem iteration_slots (pc : Fin 4860) (h : PackingIteration.program pc≠.halt) :
    program (iterationLabel pc)=ReferenceProgramLabels.instruction iterationLabel (PackingIteration.program pc) := by
  simpa [program,iterationLabel,show ¬pc.val+3060<3060 by omega,show pc.val+3060<7920 by omega] using
    callable_eq iterationLabel (PackingIteration.program pc) h

theorem iteration_halt (pc : Fin 4860) (h : PackingIteration.program pc=.halt) :
    program (iterationLabel pc)=.ret .r3 := by
  simp [program,iterationLabel,show ¬pc.val+3060<3060 by omega,show pc.val+3060<7920 by omega,h,callable]
end DirectedFlowCutGap.PackingRun
