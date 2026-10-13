import DirectedFlowCutGap.ActualKeptAdjacencyInput

namespace DirectedFlowCutGap.EmptyDemandEdge
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

def Demand (heap : NaturalHeap) (p : ℕ) (u v : Bits) : Prop :=
  ∃ a b,heap[p]?=some (.pair a b) ∧ BoolList heap a u ∧ BoolList heap b v

theorem demand_extend {heap : NaturalHeap} {p : ℕ} {u v : Bits}
    (h : Demand heap p u v) (extra : NaturalHeap) : Demand (heap++extra) p u v := by
  obtain ⟨a,b,hp,ha,hb⟩ := h
  exact ⟨a,b,lookup_extend hp extra,boolList_extend ha extra,boolList_extend hb extra⟩

def cmpLabel (pc : Fin 48) : Fin 128 := ⟨pc.val,by omega⟩
def graphLabel (pc : Fin 36) : Fin 128 := ⟨pc.val+48,by omega⟩
def program : Program 128 := fun pc =>
  if pc.val=47 ∨ pc.val=83 then .ret .r3
  else if h : pc.val<48 then
    ReferenceProgramLabels.instruction cmpLabel (BinaryComparisonProgram.program ⟨pc.val,h⟩)
  else if h : pc.val<84 then
    ReferenceProgramLabels.instruction graphLabel (GraphAdjacencyProgram.program ⟨pc.val-48,by omega⟩)
  else match pc.val with
  | 84 => .call 0 47 .r3
  | 96 => .make .r2 (.pair .r0 .r1) 97
  | 97 => .field .r0 .r0 false 98
  | 98 => .field .r1 .r2 false 99
  | 99 => .field .r1 .r1 true 100
  | 100 => .call 84 101 .r3
  | 101 => .branch .r3 118 102 102 127
  | 102 => .field .r3 .r2 true 103
  | 103 => .make .r1 (.pair .r3 .r1) 104
  | 104 => .call 82 105 .r3
  | 105 => .ret .r3
  | 118 => .make .r3 (.flag true) 119
  | 119 => .ret .r3
  | 126 => .call 96 127 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 128)) (source : Bits) (pc : Fin 128) : NaturalState 128 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem cmp_slots (pc : Fin 48) (h : BinaryComparisonProgram.program pc≠.halt) :
    program (cmpLabel pc)=ReferenceProgramLabels.instruction cmpLabel (BinaryComparisonProgram.program pc) := by
  by_cases hp : pc.val=47
  · have he : pc=47 := Fin.ext hp
    subst pc;simp [BinaryComparisonProgram.program] at h
  · have hn : ¬pc.val=83 := by omega
    simp [program,cmpLabel,pc.isLt,hp,hn]

theorem graph_slots (pc : Fin 36) (h : GraphAdjacencyProgram.program pc≠.halt) :
    program (graphLabel pc)=ReferenceProgramLabels.instruction graphLabel (GraphAdjacencyProgram.program pc) := by
  by_cases hp : pc.val=35
  · have he : pc=35 := Fin.ext hp
    subst pc;simp [GraphAdjacencyProgram.program] at h
  · have h1 : ¬pc.val+48=47 := by omega
    have h2 : ¬pc.val+48=83 := by omega
    have h3 : ¬pc.val+48<48 := by omega
    have h4 : pc.val+48<84 := by omega
    simp [program,graphLabel,h1,h2,h3,h4]
end DirectedFlowCutGap.EmptyDemandEdge
