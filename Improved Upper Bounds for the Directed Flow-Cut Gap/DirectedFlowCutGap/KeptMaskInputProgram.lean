import DirectedFlowCutGap.ActualKeptMask

namespace DirectedFlowCutGap.KeptMaskInput
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
abbrev Vertices := GraphDiscoveryProgram.Vertices

def Context (heap : NaturalHeap) (p : ℕ) (s t : Bits) (rows : List (Bits × Bits)) : Prop :=
  ∃ endpoints sr tr table,heap[p]?=some (.pair endpoints table) ∧
    heap[endpoints]?=some (.pair sr tr) ∧ BoolList heap sr s ∧ BoolList heap tr t ∧
    WordPairTableRead.Table heap table rows

theorem context_extend {heap : NaturalHeap} {p : ℕ} {s t : Bits} {rows : List (Bits × Bits)}
    (h : Context heap p s t rows) (extra : NaturalHeap) : Context (heap++extra) p s t rows := by
  obtain ⟨ep,sr,tr,f,hp,he,hs,ht,hf⟩ := h
  exact ⟨ep,sr,tr,f,lookup_extend hp extra,lookup_extend he extra,
    boolList_extend hs extra,boolList_extend ht extra,BinaryIndexedPairRead.table_extend hf extra⟩

def zeroLabel (pc : Fin 32) : Fin 200 := ⟨pc.val,by omega⟩
def maskLabel (pc : Fin 132) : Fin 200 := ⟨pc.val+32,by omega⟩
def program : Program 200 := fun pc =>
  if pc.val=31 ∨ pc.val=163 then .ret .r3
  else if h : pc.val<32 then
    ReferenceProgramLabels.instruction zeroLabel (PackingZeroMask.program ⟨pc.val,h⟩)
  else if h : pc.val<164 then
    ReferenceProgramLabels.instruction maskLabel (KeptMask.program ⟨pc.val-32,by omega⟩)
  else match pc.val with
  | 170 => .make .r2 (.pair .r0 .r1) 171
  | 171 => .field .r0 .r1 true 172
  | 172 => .call 30 173 .r3
  | 173 => .make .r3 (.pair .r2 .r3) 174
  | 174 => .field .r1 .r2 true 175
  | 175 => .field .r1 .r1 false 176
  | 176 => .field .r0 .r3 true 177
  | 177 => .make .r1 (.pair .r1 .r0) 178
  | 178 => .field .r0 .r2 false 179
  | 179 => .call 162 180 .r3
  | 180 => .ret .r3
  | 198 => .call 170 199 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 200)) (source : Bits) (pc : Fin 200) : NaturalState 200 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem zero_slots (pc : Fin 32) (h : PackingZeroMask.program pc≠.halt) :
    program (zeroLabel pc)=ReferenceProgramLabels.instruction zeroLabel (PackingZeroMask.program pc) := by
  by_cases hp : pc.val=31
  · have he : pc=31 := Fin.ext hp
    subst pc;simp [PackingZeroMask.program] at h
  · have hn : ¬pc.val=163 := by omega
    simp [program,zeroLabel,pc.isLt,hp,hn]

theorem mask_slots (pc : Fin 132) (h : KeptMask.program pc≠.halt) :
    program (maskLabel pc)=ReferenceProgramLabels.instruction maskLabel (KeptMask.program pc) := by
  by_cases hp : pc.val=131
  · have he : pc=131 := Fin.ext hp
    subst pc;simp [KeptMask.program] at h
  · have h1 : ¬pc.val+32=31 := by omega
    have h2 : ¬pc.val+32=163 := by omega
    have h3 : ¬pc.val+32<32 := by omega
    have h4 : pc.val+32<164 := by omega
    simp [program,maskLabel,h1,h2,h3,h4]
end DirectedFlowCutGap.KeptMaskInput
