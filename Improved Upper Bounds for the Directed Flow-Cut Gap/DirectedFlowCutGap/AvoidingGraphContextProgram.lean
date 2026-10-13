import DirectedFlowCutGap.PackingGraphContext

namespace DirectedFlowCutGap.AvoidingGraphContext
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open CanonicalRationalSum (StoredList list_extend)

def Input (heap : NaturalHeap) (p : ℕ) (adjacency : List Bits) (rows : List Fraction) (s t : Bits) : Prop :=
  ∃ ep sr tr detail ar cost,heap[p]?=some (.pair ep detail) ∧
    heap[ep]?=some (.pair sr tr) ∧ heap[detail]?=some (.pair ar cost) ∧
    BoolList heap sr s ∧ BoolList heap tr t ∧
    GraphAdjacencyProgram.Matrix heap ar adjacency ∧ StoredList heap cost rows

theorem input_extend {heap : NaturalHeap} {p : ℕ} {adjacency : List Bits}
    {rows : List Fraction} {s t : Bits} (h : Input heap p adjacency rows s t) (extra : NaturalHeap) :
    Input (heap++extra) p adjacency rows s t := by
  obtain ⟨ep,sr,tr,detail,ar,cost,hp,he,hd,hs,ht,ha,hc⟩ := h
  exact ⟨ep,sr,tr,detail,ar,cost,lookup_extend hp extra,lookup_extend he extra,lookup_extend hd extra,
    boolList_extend hs extra,boolList_extend ht extra,GraphAdjacencyProgram.matrix_extend ha extra,list_extend hc extra⟩

def program : Program 20 := fun pc => match pc.val with
  | 0 => .make .r2 (.pair .r0 .r1) 1
  | 1 => .field .r0 .r1 true 2
  | 2 => .field .r3 .r0 true 3
  | 3 => .field .r1 .r1 false 4
  | 4 => .field .r1 .r1 false 5
  | 5 => .make .r3 (.pair .r3 .r1) 6
  | 6 => .field .r0 .r0 false 7
  | 7 => .make .r3 (.pair .r0 .r3) 8
  | 8 => .field .r0 .r2 false 9
  | 9 => .make .r3 (.pair .r0 .r3) 10
  | 10 => .field .r1 .r2 true 11
  | 11 => .field .r1 .r1 false 12
  | 12 => .field .r1 .r1 true 13
  | 13 => .make .r3 (.pair .r1 .r3) 14
  | 14 => .ret .r3
  | 18 => .call 0 19 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 20)) (source : Bits) (pc : Fin 20) : NaturalState 20 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩
end DirectedFlowCutGap.AvoidingGraphContext
