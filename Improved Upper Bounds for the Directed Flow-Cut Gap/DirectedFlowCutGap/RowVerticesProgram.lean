import DirectedFlowCutGap.RowVertexInitialization
import DirectedFlowCutGap.VertexListReverse

namespace DirectedFlowCutGap.RowVertices
open BinaryArithmetic ImmutableReferenceSimulation

def scanLabel (pc : Fin 32) : Fin 44 := ⟨pc.val,by omega⟩
def reverseLabel (pc : Fin 6) : Fin 44 := ⟨pc.val+32,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 44) (result : Reg) : Instruction C → Instruction 44
  | .halt => .ret result
  | op => ReferenceProgramLabels.instruction label op

def program : Program 44 := fun pc =>
  if h : pc.val<32 then callable scanLabel .r3 (RowVertexScan.program ⟨pc.val,by omega⟩)
  else if h : pc.val<38 then callable reverseLabel .r1 (HeapWordReverse.program ⟨pc.val-32,by omega⟩)
  else match pc.val with
  | 40 => .call 16 41 .r3
  | 41 => .move .r0 .r3 42
  | 42 => .call 32 43 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 44)) (source : Bits) (pc : Fin 44) : NaturalState 44 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem callable_eq {C : ℕ} (label : Fin C → Fin 44) (result : Reg) (op : Instruction C) (h : op≠.halt) :
    callable label result op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

theorem scan_slots (pc : Fin 32) (h : RowVertexScan.program pc≠.halt) :
    program (scanLabel pc)=ReferenceProgramLabels.instruction scanLabel (RowVertexScan.program pc) := by
  simpa [program,scanLabel] using callable_eq scanLabel .r3 (RowVertexScan.program pc) h

theorem scan_halt (pc : Fin 32) (h : RowVertexScan.program pc=.halt) :
    program (scanLabel pc)=.ret .r3 := by simp [program,scanLabel,h,callable]

theorem reverse_slots (pc : Fin 6) (h : HeapWordReverse.program pc≠.halt) :
    program (reverseLabel pc)=ReferenceProgramLabels.instruction reverseLabel (HeapWordReverse.program pc) := by
  simpa [program,reverseLabel,show ¬pc.val+32<32 by omega,show pc.val+32<38 by omega] using
    callable_eq reverseLabel .r1 (HeapWordReverse.program pc) h

theorem reverse_halt (pc : Fin 6) (h : HeapWordReverse.program pc=.halt) :
    program (reverseLabel pc)=.ret .r1 := by
  simp [program,reverseLabel,show ¬pc.val+32<32 by omega,show pc.val+32<38 by omega,h,callable]
end DirectedFlowCutGap.RowVertices
