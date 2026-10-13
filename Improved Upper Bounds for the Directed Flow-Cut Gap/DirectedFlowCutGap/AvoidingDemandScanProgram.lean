import DirectedFlowCutGap.ActualAvoidingKeptPath
import DirectedFlowCutGap.ActualEmptyDemandScan

namespace DirectedFlowCutGap.AvoidingDemandScan
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
abbrev Table := WordPairTableRead.Table

def Context (heap : NaturalHeap) (p : ℕ) (vs : List Bits) (costs : List (Bits × Bits)) (rows : List Bits) : Prop :=
  ∃ vr detail cr ar,heap[p]?=some (.pair vr detail) ∧ heap[detail]?=some (.pair cr ar) ∧
    GraphDiscoveryProgram.Vertices heap vr vs ∧ WordPairTableRead.Table heap cr costs ∧
    KeptAdjacencyInput.Matrix heap ar rows

theorem context_extend {heap : NaturalHeap} {p : ℕ} {vs : List Bits} {costs : List (Bits × Bits)} {rows : List Bits}
    (h : Context heap p vs costs rows) (extra : NaturalHeap) : Context (heap++extra) p vs costs rows := by
  obtain ⟨vr,detail,cr,ar,hp,hd,hv,hc,ha⟩ := h
  exact ⟨vr,detail,cr,ar,lookup_extend hp extra,lookup_extend hd extra,
    GraphDiscoveryProgram.vertices_extend hv extra,BinaryIndexedPairRead.table_extend hc extra,
    GraphDiscoveryProgram.vertices_extend ha extra⟩

def Result (heap : NaturalHeap) (root : ℕ) : Option ((Bits × Bits) × GraphWalkExtension.Walk) → Prop
  | none => heap[root]?=some .nil
  | some (e,w) => ∃ er wr,heap[root]?=some (.pair er wr) ∧ EmptyDemandEdge.Demand heap er e.1 e.2 ∧
      GraphDiscoveryProgram.StoredOption heap wr (some w)

def queryLabel (pc : Fin 1800) : Fin 1900 := ⟨pc.val,by omega⟩
def program : Program 1900 := fun pc =>
  if pc.val=1799 then .ret .r3
  else if h : pc.val<1800 then
    ReferenceProgramLabels.instruction queryLabel (AvoidingKeptPath.program ⟨pc.val,h⟩)
  else match pc.val with
  | 1810 => .branch .r0 1811 1899 1899 1813
  | 1811 => .make .r3 .nil 1812
  | 1812 => .ret .r3
  | 1813 => .make .r2 (.pair .r0 .r1) 1814
  | 1814 => .field .r0 .r0 false 1815
  | 1815 => .field .r3 .r1 true 1816
  | 1816 => .field .r3 .r3 false 1817
  | 1817 => .make .r0 (.pair .r0 .r3) 1818
  | 1818 => .field .r3 .r1 true 1819
  | 1819 => .field .r3 .r3 true 1820
  | 1820 => .make .r1 (.pair .r0 .r3) 1821
  | 1821 => .field .r0 .r2 true 1822
  | 1822 => .field .r0 .r0 false 1823
  | 1823 => .call 1798 1824 .r3
  | 1824 => .branch .r3 1834 1899 1899 1825
  | 1825 => .field .r0 .r2 false 1826
  | 1826 => .field .r0 .r0 false 1827
  | 1827 => .make .r3 (.pair .r0 .r3) 1828
  | 1828 => .ret .r3
  | 1834 => .field .r0 .r2 false 1835
  | 1835 => .field .r0 .r0 true 1836
  | 1836 => .field .r1 .r2 true 1837
  | 1837 => .call 1810 1838 .r3
  | 1838 => .ret .r3
  | 1898 => .call 1810 1899 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 1900)) (source : Bits) (pc : Fin 1900) : NaturalState 1900 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem query_slots (pc : Fin 1800) (h : AvoidingKeptPath.program pc≠.halt) :
    program (queryLabel pc)=ReferenceProgramLabels.instruction queryLabel (AvoidingKeptPath.program pc) := by
  by_cases hp : pc.val=1799
  · have he : pc=1799 := Fin.ext hp
    subst pc;simp [AvoidingKeptPath.program] at h
  · simp [program,queryLabel,pc.isLt,hp]
end DirectedFlowCutGap.AvoidingDemandScan
