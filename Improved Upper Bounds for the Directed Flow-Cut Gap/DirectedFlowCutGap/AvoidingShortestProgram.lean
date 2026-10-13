import DirectedFlowCutGap.ActualAvoidingZeroContext
import DirectedFlowCutGap.ActualGraphShortest

namespace DirectedFlowCutGap.AvoidingShortest
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

def zeroLabel (pc : Fin 64) : Fin 1440 := ⟨pc.val,by omega⟩
def graphLabel (pc : Fin 1344) : Fin 1440 := ⟨pc.val+64,by omega⟩
def program : Program 1440 := fun pc =>
  if pc.val=63 ∨ pc.val=1407 then .ret .r3
  else if h : pc.val<64 then
    ReferenceProgramLabels.instruction zeroLabel (AvoidingZeroContext.program ⟨pc.val,h⟩)
  else if h : pc.val<1408 then
    ReferenceProgramLabels.instruction graphLabel (GraphRecoveryController.program ⟨pc.val-64,by omega⟩)
  else match pc.val with
  | 1410 => .make .r2 (.pair .r0 .r1) 1411
  | 1411 => .call 62 1412 .r3
  | 1412 => .move .r1 .r3 1413
  | 1413 => .field .r2 .r2 true 1414
  | 1414 => .field .r2 .r2 true 1415
  | 1415 => .field .r2 .r2 false 1416
  | 1416 => .call 1406 1417 .r3
  | 1417 => .ret .r3
  | 1438 => .call 1410 1439 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 1440)) (source : Bits) (pc : Fin 1440) : NaturalState 1440 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem zero_slots (pc : Fin 64) (h : AvoidingZeroContext.program pc≠.halt) :
    program (zeroLabel pc)=ReferenceProgramLabels.instruction zeroLabel (AvoidingZeroContext.program pc) := by
  by_cases hp : pc.val=63
  · have he : pc=63 := Fin.ext hp
    subst pc;simp [AvoidingZeroContext.program] at h
  · simp [program,zeroLabel,pc.isLt,hp,show ¬pc.val=1407 by omega]

theorem graph_slots (pc : Fin 1344) (h : GraphRecoveryController.program pc≠.halt) :
    program (graphLabel pc)=ReferenceProgramLabels.instruction graphLabel (GraphRecoveryController.program pc) := by
  by_cases hp : pc.val=1343
  · have he : pc=1343 := Fin.ext hp
    subst pc;simp [GraphRecoveryController.program] at h
  · simp [program,graphLabel,show ¬pc.val+64=63 by omega,show ¬pc.val+64=1407 by omega,
      show ¬pc.val+64<64 by omega,show pc.val+64<1408 by omega]
end DirectedFlowCutGap.AvoidingShortest
