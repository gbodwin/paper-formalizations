import DirectedFlowCutGap.ActualKeptAdjacencyRow

namespace DirectedFlowCutGap.KeptAdjacencyMatrix
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
abbrev Matrix := GraphDiscoveryProgram.Vertices

def Context (heap : NaturalHeap) (p : ℕ) (remaining kept : Bits) : Prop :=
  ∃ r k,heap[p]?=some (.pair r k) ∧ BoolList heap r remaining ∧ BoolList heap k kept

theorem context_extend {heap : NaturalHeap} {p : ℕ} {remaining kept : Bits}
    (h : Context heap p remaining kept) (extra : NaturalHeap) : Context (heap++extra) p remaining kept := by
  obtain ⟨r,k,hp,hr,hk⟩ := h
  exact ⟨r,k,lookup_extend hp extra,boolList_extend hr extra,boolList_extend hk extra⟩

def rowLabel (pc : Fin 36) : Fin 84 := ⟨pc.val,by omega⟩
def program : Program 84 := fun pc =>
  if pc.val=35 then .ret .r3
  else if h : pc.val<36 then
    ReferenceProgramLabels.instruction rowLabel (KeptAdjacencyRow.program ⟨pc.val,h⟩)
  else match pc.val with
  | 40 => .branch .r0 41 83 83 43
  | 41 => .make .r3 .nil 42
  | 42 => .ret .r3
  | 43 => .make .r2 (.pair .r0 .r1) 44
  | 44 => .field .r0 .r0 false 45
  | 45 => .field .r1 .r1 false 46
  | 46 => .field .r1 .r1 false 47
  | 47 => .field .r3 .r2 true 48
  | 48 => .field .r3 .r3 true 49
  | 49 => .make .r1 (.pair .r1 .r3) 50
  | 50 => .call 34 51 .r3
  | 51 => .make .r2 (.pair .r2 .r3) 52
  | 52 => .field .r0 .r2 false 53
  | 53 => .field .r0 .r0 false 54
  | 54 => .field .r0 .r0 true 55
  | 55 => .field .r1 .r2 false 56
  | 56 => .field .r1 .r1 true 57
  | 57 => .field .r3 .r1 false 58
  | 58 => .field .r3 .r3 true 59
  | 59 => .field .r1 .r1 true 60
  | 60 => .make .r1 (.pair .r3 .r1) 61
  | 61 => .call 40 62 .r3
  | 62 => .field .r2 .r2 true 63
  | 63 => .make .r3 (.pair .r2 .r3) 64
  | 64 => .ret .r3
  | 82 => .call 40 83 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 84)) (source : Bits) (pc : Fin 84) : NaturalState 84 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem row_slots (pc : Fin 36) (h : KeptAdjacencyRow.program pc≠.halt) :
    program (rowLabel pc)=ReferenceProgramLabels.instruction rowLabel (KeptAdjacencyRow.program pc) := by
  by_cases hp : pc.val=35
  · have he : pc=35 := Fin.ext hp
    subst pc;simp [KeptAdjacencyRow.program] at h
  · simp [program,rowLabel,pc.isLt,hp]
end DirectedFlowCutGap.KeptAdjacencyMatrix
