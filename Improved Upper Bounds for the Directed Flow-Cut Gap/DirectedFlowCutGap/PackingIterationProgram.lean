import DirectedFlowCutGap.PackingIterationSpecification
import DirectedFlowCutGap.BinaryCounterProgram

/-! The represented binary fuel is physically converted to a unary spine, then
consumed by a fixed controller calling the actual adaptive step on each cursor.
The conversion is charged in numerical fuel, not merely the fuel-word length. -/
namespace DirectedFlowCutGap.PackingIteration
open BinaryArithmetic ImmutableReferenceSimulation

def stepLabel (pc : Fin 4800) : Fin 4860 := ⟨pc.val,by omega⟩
def counterLabel (pc : Fin 17) : Fin 4860 := ⟨pc.val+4800,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 4860) : Instruction C → Instruction 4860
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

def program : Program 4860 := fun pc =>
  if h : pc.val<4800 then callable stepLabel (AdaptivePackingState.program ⟨pc.val,by omega⟩)
  else if h : pc.val<4817 then callable counterLabel (BinaryCounterProgram.program ⟨pc.val-4800,by omega⟩)
  else match pc.val with
  | 4817 => .call 4800 4816 .r3
  | 4820 => .make .r3 (.pair .r0 .r2) 4821
  | 4821 => .field .r0 .r2 true 4822
  | 4822 => .call 4817 4823 .r2
  | 4823 => .field .r0 .r3 false 4824
  | 4824 => .field .r3 .r3 true 4825
  | 4825 => .field .r3 .r3 false 4830
  | 4830 => .branch .r2 4858 4859 4859 4831
  | 4831 => .field .r2 .r2 true 4832
  | 4832 => .make .r2 (.pair .r2 .r3) 4833
  | 4833 => .move .r3 .r2 4834
  | 4834 => .field .r2 .r3 true 4835
  | 4835 => .call 4400 4836 .r1
  | 4836 => .field .r2 .r3 false 4837
  | 4837 => .field .r3 .r3 true 4830
  | 4858 => .move .r3 .r1 4859
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 4860)) (source : Bits) (pc : Fin 4860) : NaturalState 4860 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem callable_eq {C : ℕ} (label : Fin C → Fin 4860) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

theorem step_slots (pc : Fin 4800) (h : AdaptivePackingState.program pc≠.halt) :
    program (stepLabel pc)=ReferenceProgramLabels.instruction stepLabel (AdaptivePackingState.program pc) := by
  simpa [program,stepLabel] using callable_eq stepLabel (AdaptivePackingState.program pc) h

theorem step_halt (pc : Fin 4800) (h : AdaptivePackingState.program pc=.halt) :
    program (stepLabel pc)=.ret .r3 := by simp [program,stepLabel,h,callable]

theorem counter_slots (pc : Fin 17) (h : BinaryCounterProgram.program pc≠.halt) :
    program (counterLabel pc)=ReferenceProgramLabels.instruction counterLabel (BinaryCounterProgram.program pc) := by
  simpa [program,counterLabel,show ¬pc.val+4800<4800 by omega,show pc.val+4800<4817 by omega] using
    callable_eq counterLabel (BinaryCounterProgram.program pc) h
end DirectedFlowCutGap.PackingIteration
