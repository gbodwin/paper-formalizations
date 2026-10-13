import DirectedFlowCutGap.AvoidingGraphContextExecution
import DirectedFlowCutGap.PackingZeroRowConstruction

namespace DirectedFlowCutGap.AvoidingZeroContext
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

def Static (heap : NaturalHeap) (p : ℕ) (adjacency : List Bits) (s t : Bits) : Prop :=
  ∃ ar ep sr tr,heap[p]?=some (.pair ar ep) ∧ heap[ep]?=some (.pair sr tr) ∧
    GraphAdjacencyProgram.Matrix heap ar adjacency ∧ BoolList heap sr s ∧ BoolList heap tr t

theorem static_extend {heap : NaturalHeap} {p : ℕ} {adjacency : List Bits} {s t : Bits}
    (h : Static heap p adjacency s t) (extra : NaturalHeap) : Static (heap++extra) p adjacency s t := by
  obtain ⟨ar,ep,sr,tr,hp,he,ha,hs,ht⟩ := h
  exact ⟨ar,ep,sr,tr,lookup_extend hp extra,lookup_extend he extra,
    GraphAdjacencyProgram.matrix_extend ha extra,boolList_extend hs extra,boolList_extend ht extra⟩

def contextLabel (pc : Fin 20) : Fin 64 := ⟨pc.val,by omega⟩
def zeroLabel (pc : Fin 16) : Fin 64 := ⟨pc.val+20,by omega⟩
def program : Program 64 := fun pc =>
  if pc.val=19 ∨ pc.val=34 then .ret .r3
  else if h : pc.val<20 then
    ReferenceProgramLabels.instruction contextLabel (AvoidingGraphContext.program ⟨pc.val,h⟩)
  else if h : pc.val<36 then
    ReferenceProgramLabels.instruction zeroLabel (PackingZeroRow.program ⟨pc.val-20,by omega⟩)
  else match pc.val with
  | 40 => .make .r2 (.pair .r0 .r1) 41
  | 41 => .call 28 42 .r3
  | 42 => .field .r3 .r3 true 43
  | 43 => .field .r0 .r1 false 44
  | 44 => .make .r3 (.pair .r0 .r3) 45
  | 45 => .field .r0 .r1 true 46
  | 46 => .make .r1 (.pair .r0 .r3) 47
  | 47 => .field .r0 .r2 false 48
  | 48 => .call 18 49 .r3
  | 49 => .ret .r3
  | 62 => .call 40 63 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 64)) (source : Bits) (pc : Fin 64) : NaturalState 64 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem context_slots (pc : Fin 20) (h : AvoidingGraphContext.program pc≠.halt) :
    program (contextLabel pc)=ReferenceProgramLabels.instruction contextLabel (AvoidingGraphContext.program pc) := by
  by_cases hp : pc.val=19
  · have he : pc=19 := Fin.ext hp
    subst pc;simp [AvoidingGraphContext.program] at h
  · simp [program,contextLabel,pc.isLt,hp,show ¬pc.val=34 by omega]

theorem zero_slots (pc : Fin 16) (h : PackingZeroRow.program pc≠.halt) :
    program (zeroLabel pc)=ReferenceProgramLabels.instruction zeroLabel (PackingZeroRow.program pc) := by
  by_cases hp : pc.val=14
  · have he : pc=14 := Fin.ext hp
    subst pc;simp [PackingZeroRow.program] at h
  · simp [program,zeroLabel,show ¬pc.val+20=19 by omega,show ¬pc.val+20=34 by omega,
      show ¬pc.val+20<20 by omega,show pc.val+20<36 by omega]
end DirectedFlowCutGap.AvoidingZeroContext
