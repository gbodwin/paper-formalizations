import DirectedFlowCutGap.ActualEmptyDemandEdge

namespace DirectedFlowCutGap.EmptyDemandScan
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
abbrev Table := WordPairTableRead.Table

def Result (heap : NaturalHeap) (p : ℕ) : Option (Bits × Bits) → Prop
  | none => heap[p]?=some .nil
  | some e => EmptyDemandEdge.Demand heap p e.1 e.2

theorem result_extend {heap : NaturalHeap} {p : ℕ} {e : Option (Bits × Bits)}
    (h : Result heap p e) (extra : NaturalHeap) : Result (heap++extra) p e := by
  cases e with
  | none => exact lookup_extend h extra
  | some e => exact EmptyDemandEdge.demand_extend h extra

def edgeLabel (pc : Fin 128) : Fin 160 := ⟨pc.val,by omega⟩
def program : Program 160 := fun pc =>
  if pc.val=127 then .ret .r3
  else if h : pc.val<128 then
    ReferenceProgramLabels.instruction edgeLabel (EmptyDemandEdge.program ⟨pc.val,h⟩)
  else match pc.val with
  | 136 => .branch .r0 137 159 159 139
  | 137 => .make .r3 .nil 138
  | 138 => .ret .r3
  | 139 => .make .r2 (.pair .r0 .r1) 140
  | 140 => .field .r0 .r0 false 141
  | 141 => .call 126 142 .r3
  | 142 => .branch .r3 159 146 143 159
  | 143 => .move .r3 .r0 144
  | 144 => .ret .r3
  | 146 => .field .r0 .r2 false 147
  | 147 => .field .r0 .r0 true 148
  | 148 => .call 136 149 .r3
  | 149 => .ret .r3
  | 158 => .call 136 159 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 160)) (source : Bits) (pc : Fin 160) : NaturalState 160 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem edge_slots (pc : Fin 128) (h : EmptyDemandEdge.program pc≠.halt) :
    program (edgeLabel pc)=ReferenceProgramLabels.instruction edgeLabel (EmptyDemandEdge.program pc) := by
  by_cases hp : pc.val=127
  · have he : pc=127 := Fin.ext hp
    subst pc;simp [EmptyDemandEdge.program] at h
  · simp [program,edgeLabel,pc.isLt,hp]
end DirectedFlowCutGap.EmptyDemandScan
