import DirectedFlowCutGap.OracleSelectedMask

namespace DirectedFlowCutGap.OracleChoice
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor

def StoredChoice {n : ℕ} (heap : NaturalHeap) (root : ℕ) (label : Fin n → Bits)
    (q : BinaryFractionalCore.Choice n) : Prop :=
  ∃ mask word,heap[root]?=some (.pair mask word) ∧
    BoolList heap mask q.mask.toList ∧ BoolList heap word (label q.bottleneck)

def choice {n : ℕ} (capacity : Row n) (hn : 0<n) :
    Option (BinaryFractionalGraphOracle.Selected n) → BinaryFractionalCore.Choice n
  | none => ⟨(BinaryFractionalGraphOracle.singletonMask ⟨0,hn⟩).1,⟨0,hn⟩⟩
  | some q =>
    let mask := (BinaryFractionalGraphOracle.internalMask q.demand.1 q.demand.2 q.path.edges).1
    ⟨mask,(BinaryFractionalGraphOracle.bottleneck capacity mask).1.getD ⟨0,hn⟩⟩

theorem oracle_choice {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (ds : List (BinaryFractionalWalkOracle.Pair n)) (capacity y : Row n) (hn : 0<n) :
    (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn y).1=
      choice capacity hn (BinaryFractionalGraphOracle.selected adjacency y ds).1 := by
  cases h : (BinaryFractionalGraphOracle.selected adjacency y ds).1 <;>
    simp [BinaryFractionalGraphOracle.oracle,choice,h]

theorem graph_context_extend {n : ℕ} {heap : NaturalHeap} {b : ℕ}
    {label : Fin n → Bits} {capacity : Row n}
    (h : CapacityBottleneck.GraphContext heap b label capacity) (extra : NaturalHeap) :
    CapacityBottleneck.GraphContext (heap++extra) b label capacity := by
  obtain ⟨v,t,hp,hv,ht⟩ := h
  exact ⟨v,t,lookup_extend hp extra,GraphDiscoveryProgram.vertices_extend hv extra,
    BinaryIndexedPairRead.table_extend ht extra⟩

theorem singleton_mask_list (n : ℕ) :
    (BinaryFractionalGraphOracle.singletonMask (0 : Fin (n+1))).1.toList=
      true::List.replicate n false := by
  have get (i : Fin (n+1)) :
      (BinaryFractionalGraphOracle.singletonMask (0 : Fin (n+1))).1[i.val]=decide (i=0) :=
    EncodedRoundingInput.tabulate_get _ i
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i<n+1 := by simpa using h1
    rw [Vector.getElem_toList,get ⟨i,hi⟩]
    cases i with
    | zero => simp
    | succ i => simp [Fin.ext_iff]

end DirectedFlowCutGap.OracleChoice
