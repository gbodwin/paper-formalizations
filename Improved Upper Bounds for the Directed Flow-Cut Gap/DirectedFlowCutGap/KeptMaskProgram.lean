import DirectedFlowCutGap.ActualKeptVertex

namespace DirectedFlowCutGap.KeptMask
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
abbrev Vertices := GraphDiscoveryProgram.Vertices

def Context (heap : NaturalHeap) (p : ℕ) (s t zeros : Bits) : Prop :=
  ∃ endpoints sr tr flags,heap[p]?=some (.pair endpoints flags) ∧
    heap[endpoints]?=some (.pair sr tr) ∧ BoolList heap sr s ∧ BoolList heap tr t ∧
    BoolList heap flags zeros

theorem context_extend {heap : NaturalHeap} {p : ℕ} {s t zeros : Bits}
    (h : Context heap p s t zeros) (extra : NaturalHeap) : Context (heap++extra) p s t zeros := by
  obtain ⟨ep,sr,tr,f,hp,he,hs,ht,hf⟩ := h
  exact ⟨ep,sr,tr,f,lookup_extend hp extra,lookup_extend he extra,
    boolList_extend hs extra,boolList_extend ht extra,boolList_extend hf extra⟩

def keepLabel (pc : Fin 80) : Fin 132 := ⟨pc.val,by omega⟩
def program : Program 132 := fun pc =>
  if pc.val=79 then .ret .r3
  else if h : pc.val<80 then
    ReferenceProgramLabels.instruction keepLabel (KeptVertex.program ⟨pc.val,h⟩)
  else match pc.val with
  | 100 => .branch .r0 101 131 131 103
  | 101 => .make .r3 .nil 102
  | 102 => .ret .r3
  | 103 => .make .r2 (.pair .r0 .r1) 104
  | 104 => .field .r0 .r0 false 105
  | 105 => .field .r1 .r1 true 106
  | 106 => .field .r1 .r1 false 107
  | 107 => .field .r3 .r2 true 108
  | 108 => .field .r3 .r3 false 109
  | 109 => .make .r1 (.pair .r3 .r1) 110
  | 110 => .call 78 111 .r3
  | 111 => .make .r2 (.pair .r2 .r3) 112
  | 112 => .field .r0 .r2 false 113
  | 113 => .field .r0 .r0 false 114
  | 114 => .field .r0 .r0 true 115
  | 115 => .field .r1 .r2 false 116
  | 116 => .field .r1 .r1 true 117
  | 117 => .field .r3 .r1 true 118
  | 118 => .field .r3 .r3 true 119
  | 119 => .field .r1 .r1 false 120
  | 120 => .make .r1 (.pair .r1 .r3) 121
  | 121 => .call 100 122 .r3
  | 122 => .field .r2 .r2 true 123
  | 123 => .make .r3 (.pair .r2 .r3) 124
  | 124 => .ret .r3
  | 130 => .call 100 131 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 132)) (source : Bits) (pc : Fin 132) : NaturalState 132 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem keep_slots (pc : Fin 80) (h : KeptVertex.program pc≠.halt) :
    program (keepLabel pc)=ReferenceProgramLabels.instruction keepLabel (KeptVertex.program pc) := by
  by_cases hp : pc.val=79
  · have he : pc=79 := Fin.ext hp
    subst pc;simp [KeptVertex.program] at h
  · simp [program,keepLabel,pc.isLt,hp]
end DirectedFlowCutGap.KeptMask
