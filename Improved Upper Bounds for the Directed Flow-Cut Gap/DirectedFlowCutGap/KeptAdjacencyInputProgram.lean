import DirectedFlowCutGap.KeptAdjacencyMatrixRepresentation

namespace DirectedFlowCutGap.KeptAdjacencyInput
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
abbrev Vertices := GraphDiscoveryProgram.Vertices
abbrev Matrix := KeptAdjacencyMatrix.Matrix

def Context (heap : NaturalHeap) (p : ℕ) (s t : Bits) (costs : List (Bits × Bits)) (rows : List Bits) : Prop :=
  ∃ mc ar,heap[p]?=some (.pair mc ar) ∧ KeptMaskInput.Context heap mc s t costs ∧ Matrix heap ar rows

theorem context_extend {heap : NaturalHeap} {p : ℕ} {s t : Bits} {costs : List (Bits × Bits)} {rows : List Bits}
    (h : Context heap p s t costs rows) (extra : NaturalHeap) : Context (heap++extra) p s t costs rows := by
  obtain ⟨mc,ar,hp,hm,ha⟩ := h
  exact ⟨mc,ar,lookup_extend hp extra,KeptMaskInput.context_extend hm extra,
    GraphDiscoveryProgram.vertices_extend ha extra⟩

def maskLabel (pc : Fin 200) : Fin 320 := ⟨pc.val,by omega⟩
def matrixLabel (pc : Fin 84) : Fin 320 := ⟨pc.val+200,by omega⟩
def program : Program 320 := fun pc =>
  if pc.val=199 ∨ pc.val=283 then .ret .r3
  else if h : pc.val<200 then
    ReferenceProgramLabels.instruction maskLabel (KeptMaskInput.program ⟨pc.val,h⟩)
  else if h : pc.val<284 then
    ReferenceProgramLabels.instruction matrixLabel (KeptAdjacencyMatrix.program ⟨pc.val-200,by omega⟩)
  else match pc.val with
  | 290 => .make .r2 (.pair .r0 .r1) 291
  | 291 => .field .r1 .r1 false 292
  | 292 => .call 198 293 .r3
  | 293 => .make .r1 (.pair .r3 .r3) 294
  | 294 => .field .r0 .r2 true 295
  | 295 => .field .r0 .r0 true 296
  | 296 => .call 282 297 .r3
  | 297 => .ret .r3
  | 318 => .call 290 319 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 320)) (source : Bits) (pc : Fin 320) : NaturalState 320 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem mask_slots (pc : Fin 200) (h : KeptMaskInput.program pc≠.halt) :
    program (maskLabel pc)=ReferenceProgramLabels.instruction maskLabel (KeptMaskInput.program pc) := by
  by_cases hp : pc.val=199
  · have he : pc=199 := Fin.ext hp
    subst pc;simp [KeptMaskInput.program] at h
  · have hn : ¬pc.val=283 := by omega
    simp [program,maskLabel,pc.isLt,hp,hn]

theorem matrix_slots (pc : Fin 84) (h : KeptAdjacencyMatrix.program pc≠.halt) :
    program (matrixLabel pc)=ReferenceProgramLabels.instruction matrixLabel (KeptAdjacencyMatrix.program pc) := by
  by_cases hp : pc.val=83
  · have he : pc=83 := Fin.ext hp
    subst pc;simp [KeptAdjacencyMatrix.program] at h
  · have h1 : ¬pc.val+200=199 := by omega
    have h2 : ¬pc.val+200=283 := by omega
    have h3 : ¬pc.val+200<200 := by omega
    have h4 : pc.val+200<284 := by omega
    simp [program,matrixLabel,h1,h2,h3,h4]
end DirectedFlowCutGap.KeptAdjacencyInput
