import DirectedFlowCutGap.SupportRecoveryProgram

namespace DirectedFlowCutGap.SupportRecoveryProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

def StoredPredContext (heap : NaturalHeap) (p : ℕ) (adjacency : List Bits)
    (es : List (Bits × Bits)) (u : Bits) : Prop :=
  ∃ vertex context,heap[p]?=some (.pair vertex context) ∧ BoolList heap vertex u ∧
    SupportContext heap context adjacency es
def StoredVisitContext (heap : NaturalHeap) (p : ℕ) (adjacency : List Bits)
    (es : List (Bits × Bits)) (xs : List Code) : Prop :=
  ∃ table context,heap[p]?=some (.pair table context) ∧ Codes heap table xs ∧
    SupportContext heap context adjacency es
def StoredGlobalContext (heap : NaturalHeap) (p : ℕ) (vs : List Bits) (adjacency : List Bits)
    (es : List (Bits × Bits)) (target : Bits) : Prop :=
  ∃ tr bundle vertices context,heap[p]?=some (.pair tr bundle) ∧
    heap[bundle]?=some (.pair vertices context) ∧ BoolList heap tr target ∧
    Vertices heap vertices vs ∧ SupportContext heap context adjacency es

theorem code_extend {heap : NaturalHeap} {p : ℕ} {x : Code}
    (h : StoredCode heap p x) (extra : NaturalHeap) : StoredCode (heap++extra) p x := by
  obtain ⟨v,e,hp,hv,he⟩ := h
  exact ⟨v,e,lookup_extend hp extra,boolList_extend hv extra,edgeList_extend he extra⟩
theorem codes_extend {heap : NaturalHeap} {p : ℕ} {xs : List Code}
    (h : Codes heap p xs) (extra : NaturalHeap) : Codes (heap++extra) p xs := by
  induction h with
  | nil hp => exact .nil (lookup_extend hp extra)
  | cons hp hx _ ih => exact .cons (lookup_extend hp extra) (code_extend hx extra) ih
theorem option_extend {heap : NaturalHeap} {p : ℕ} {x : Option Code}
    (h : StoredOption heap p x) (extra : NaturalHeap) : StoredOption (heap++extra) p x := by
  cases x with
  | none => exact lookup_extend h extra
  | some x => exact code_extend h extra
theorem supportContext_extend {heap : NaturalHeap} {p : ℕ} {adjacency : List Bits}
    {es : List (Bits × Bits)} (h : SupportContext heap p adjacency es) (extra : NaturalHeap) :
    SupportContext (heap++extra) p adjacency es := by
  obtain ⟨m,e,hp,hm,he⟩ := h
  exact ⟨m,e,lookup_extend hp extra,GraphAdjacencyProgram.matrix_extend hm extra,edgeList_extend he extra⟩
theorem predContext_extend {heap : NaturalHeap} {p : ℕ} {adjacency : List Bits}
    {es : List (Bits × Bits)} {u : Bits} (h : StoredPredContext heap p adjacency es u)
    (extra : NaturalHeap) : StoredPredContext (heap++extra) p adjacency es u := by
  obtain ⟨v,c,hp,hv,hc⟩ := h
  exact ⟨v,c,lookup_extend hp extra,boolList_extend hv extra,supportContext_extend hc extra⟩
theorem visitContext_extend {heap : NaturalHeap} {p : ℕ} {adjacency : List Bits}
    {es : List (Bits × Bits)} {xs : List Code} (h : StoredVisitContext heap p adjacency es xs)
    (extra : NaturalHeap) : StoredVisitContext (heap++extra) p adjacency es xs := by
  obtain ⟨t,c,hp,ht,hc⟩ := h
  exact ⟨t,c,lookup_extend hp extra,codes_extend ht extra,supportContext_extend hc extra⟩
theorem globalContext_extend {heap : NaturalHeap} {p : ℕ} {vs adjacency : List Bits}
    {es : List (Bits × Bits)} {target : Bits} (h : StoredGlobalContext heap p vs adjacency es target)
    (extra : NaturalHeap) : StoredGlobalContext (heap++extra) p vs adjacency es target := by
  obtain ⟨t,b,v,c,hp,hb,ht,hv,hc⟩ := h
  exact ⟨t,b,v,c,lookup_extend hp extra,lookup_extend hb extra,boolList_extend ht extra,
    GraphDiscoveryProgram.vertices_extend hv extra,supportContext_extend hc extra⟩

end DirectedFlowCutGap.SupportRecoveryProgram
