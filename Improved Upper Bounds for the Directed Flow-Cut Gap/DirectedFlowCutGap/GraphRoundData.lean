import DirectedFlowCutGap.GraphPassConstruction

/-! The exact finite round recurrence and its retained global input. The round
counter is the real supplied list spine, not an abstract evaluation oracle. -/
namespace DirectedFlowCutGap.GraphDiscoveryProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

def rounds (vertices : List Bits) (adjacency : List Bits) (rows : List Fraction)
    (sw target : Bits) : List Bits → List Entry
  | [] => [(target,zero)]
  | _::rest => pass adjacency rows sw target (rounds vertices adjacency rows sw target rest) vertices

def roundSteps (vertices : List Bits) (adjacency : List Bits) (rows : List Fraction)
    (sw target : Bits) : List Bits → ℕ
  | [] => 13
  | _::rest => roundSteps vertices adjacency rows sw target rest+
      passSteps adjacency rows sw target (rounds vertices adjacency rows sw target rest) vertices+11

def roundCells (vertices : List Bits) (adjacency : List Bits) (rows : List Fraction)
    (sw target : Bits) : List Bits → ℕ
  | [] => 8
  | _::rest => roundCells vertices adjacency rows sw target rest+2+
      passCells adjacency rows sw target (rounds vertices adjacency rows sw target rest) vertices

def GlobalContext (heap : NaturalHeap) (p : ℕ) (vertices : List Bits)
    (adjacency : List Bits) (rows : List Fraction) (sw target : Bits) : Prop :=
  ∃ tr bundle enumRoot mix matrix cost,heap[p]?=some (.pair tr bundle) ∧
    heap[bundle]?=some (.pair enumRoot mix) ∧ heap[mix]?=some (.pair matrix cost) ∧
    BoolList heap tr target ∧ Vertices heap enumRoot vertices ∧
    GraphAdjacencyProgram.Matrix heap matrix adjacency ∧ OutgoingCostProgram.Context heap cost rows sw

theorem global_extend {heap : NaturalHeap} {p : ℕ} {vertices adjacency : List Bits}
    {rows : List Fraction} {sw target : Bits} (h : GlobalContext heap p vertices adjacency rows sw target)
    (extra : NaturalHeap) : GlobalContext (heap++extra) p vertices adjacency rows sw target := by
  obtain ⟨tr,bundle,enumRoot,mix,matrix,cost,hp,hb,hm,ht,he,ha,hc⟩ := h
  exact ⟨tr,bundle,enumRoot,mix,matrix,cost,lookup_extend hp extra,lookup_extend hb extra,
    lookup_extend hm extra,boolList_extend ht extra,vertices_extend he extra,
    GraphAdjacencyProgram.matrix_extend ha extra,PathCostMaterialization.context_extend hc extra⟩

theorem pass_label {adjacency : List Bits} {rows : List Fraction} {sw target : Bits}
    {old : List Entry} {vertices : List Bits} {x : Entry}
    (hx : x∈pass adjacency rows sw target old vertices) : x.1∈vertices := by
  induction vertices with
  | nil => simp [pass] at hx
  | cons u us ih =>
    simp only [pass] at hx
    cases h : atVertex adjacency rows sw target u old with
    | none => simp only [h] at hx;exact List.mem_cons_of_mem u (ih hx)
    | some q =>
      simp only [h,List.mem_cons] at hx
      rcases hx with rfl|hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem u (ih hx)

theorem round_label {vertices adjacency : List Bits} {rows : List Fraction} {sw target : Bits}
    (fuel : List Bits) {x : Entry} (hx : x∈rounds vertices adjacency rows sw target fuel) :
    x.1=target ∨ x.1∈vertices := by
  cases fuel with
  | nil =>
    simp only [rounds,List.mem_singleton] at hx
    subst x;exact Or.inl rfl
  | cons u us => exact Or.inr (pass_label hx)

end DirectedFlowCutGap.GraphDiscoveryProgram
