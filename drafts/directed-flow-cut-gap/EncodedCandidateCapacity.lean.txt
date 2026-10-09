import DirectedFlowCutGap.ClosureRuntime

/-!
# Finite encoded inputs and direct threshold capacities

The graph and current cut are retained Boolean arrays. The executable capacity
builder evaluates the finite threshold predicates directly, and receives the
already computed absolute-cost budget as an integer. It never constructs and
rescans the closure problem's full implication-arc finset for each lookup.
The equality proofs target that exact frozen closure problem.
-/
set_option synthInstance.maxSize 1024

namespace DirectedFlowCutGap.EncodedCandidateCapacity

open scoped BigOperators
open CandidateGridOptimizer CandidatePortDifferenceSystem CandidateThresholdClosure
open MinimumClosureProblem MinimumClosureCut IntegralNetworkFlow

attribute [local instance] CandidatePortDifferenceSystem.decidablePortAdj

structure Input (n : ℕ) where
  adjacency : Vector (Vector Bool n) n
  removed : Vector Bool n

namespace Input
variable {n : ℕ}

def graph (D : Input n) : Digraph (Fin n) where
  Adj u v := (D.adjacency[u.val])[v.val] = true

instance (D : Input n) : DecidableRel D.graph.Adj := fun u v =>
  inferInstanceAs (Decidable ((D.adjacency[u.val])[v.val] = true))

def cut (D : Input n) : Finset (Fin n) := Finset.univ.filter fun v => D.removed[v.val] = true

@[simp] theorem mem_cut (D : Input n) (v : Fin n) : v ∈ D.cut ↔ D.removed[v.val] = true := by
  simp [cut]

def cost (D : Input n) : Point (Fin n) → ℤ
  | (.inl v,b) => if D.removed[v.val] then 0 else if b then 1 else -1
  | (.inr _,_) => 0

theorem cost_eq (D : Input n) (a : Point (Fin n)) : D.cost a = integerCosts D.cut a := by
  rcases a with ⟨v,b⟩
  cases v with
  | inl v => cases h : D.removed[v.val] <;> simp [cost,integerCosts,mem_cut,h]
  | inr a => rfl

def portCapacity (D : Input n) (L B : ℕ) : TerminalPorts.Vertex (Fin n) → ℕ
  | .inl v => if D.removed[v.val] then L else B
  | .inr _ => 0

theorem portCapacity_eq (D : Input n) (L B : ℕ) (v : TerminalPorts.Vertex (Fin n)) :
    D.portCapacity L B v = portCap D.cut L B v := by
  cases v with
  | inl v => cases h : D.removed[v.val] <;> simp [portCapacity,portCap,mem_cut,h]
  | inr a => rfl

def gap (D : Input n) (L B : ℕ) (a b : Point (Fin n)) : ℤ :=
  if a.1=b.1 ∧ a.2=true ∧ b.2=false then D.portCapacity L B a.1 else L

def bound (D : Input n) (L B : ℕ) (a b : Point (Fin n)) : ℤ :=
  min (orderBound L a b) (min (D.gap L B a b) (edgeBound D.graph L a b))

theorem bound_eq (D : Input n) (s t : Fin n) (L B : ℕ) (a b : Point (Fin n)) :
    D.bound L B a b = (system D.graph s t D.cut L B).bound a b := by
  simp only [bound,gap,system,gapBound,portCapacity_eq]

theorem bound_nonneg (D : Input n) (L B : ℕ) (a b : Point (Fin n)) : 0 ≤ D.bound L B a b := by
  simp only [bound,le_min_iff]
  constructor
  · unfold orderBound
    split <;> omega
  · constructor
    · unfold gap
      split <;> exact Int.natCast_nonneg _
    · unfold edgeBound
      split <;> omega

/-- Unit signed threshold cost, computed by one array read and finite tests. -/
def nodeCost (D : Input n) {L : ℕ} (a : Node (Point (Fin n)) L) : ℤ :=
  if a.2 = 0 then 0 else D.cost a.1

theorem nodeCost_eq (D : Input n) (s t : Fin n) (L B : ℕ)
    (a : Node (Point (Fin n)) L) :
    D.nodeCost a = (candidateClosure D.graph s t D.cut L B).cost a := by
  simp [nodeCost,candidateClosure,problem,cost_eq]

/-! The word model charges each tag test, scalar comparison, Boolean operation,
array access, scalar conversion/arithmetic operation, list case and allocation.
Fixed charges below bound only the displayed straight-line finite code; all
list traversals have recursive counters. Vector access is random access. Proofs,
reference projections and counter bookkeeping are erased/not charged. -/

/-- A core cost uses one outer tag, one array access, and at most two branches.
A port uses just the outer tag. Pair construction is included. -/
def costWithCost (D : Input n) : Point (Fin n) → ℤ × ℕ
  | (.inl v,b) => (if D.removed[v.val] then 0 else if b then 1 else -1,5)
  | (.inr _,_) => (0,2)

@[simp] theorem costWithCost_value (D : Input n) (a : Point (Fin n)) :
    (D.costWithCost a).1 = D.cost a := by
  rcases a with ⟨a,b⟩; cases a <;> rfl

theorem costWithCost_bound (D : Input n) (a : Point (Fin n)) :
    (D.costWithCost a).2 ≤ 5 := by
  rcases a with ⟨a,b⟩; cases a <;> simp only [costWithCost] <;> omega

/-- The threshold zero test and branch add two operations; the zero branch
allocates its result in the third operation. -/
def nodeCostWithCost (D : Input n) {L : ℕ} (a : Node (Point (Fin n)) L) : ℤ × ℕ :=
  if a.2 = 0 then (0,3) else
    let r := D.costWithCost a.1
    (r.1,r.2+3)

@[simp] theorem nodeCostWithCost_value (D : Input n) {L : ℕ}
    (a : Node (Point (Fin n)) L) : (D.nodeCostWithCost a).1 = D.nodeCost a := by
  by_cases h : a.2 = 0 <;> simp [nodeCostWithCost,nodeCost,h]

theorem nodeCostWithCost_bound (D : Input n) {L : ℕ} (a : Node (Point (Fin n)) L) :
    (D.nodeCostWithCost a).2 ≤ 8 := by
  have h := D.costWithCost_bound a.1
  unfold nodeCostWithCost
  split <;> dsimp only <;> omega

/-- One budget pass; five operations per cell cover the list case, absolute
value, addition, recursion sequencing and pair allocation. -/
def budgetScan (D : Input n) {L : ℕ} : List (Node (Point (Fin n)) L) → ℕ × ℕ
  | [] => (0,1)
  | a::as =>
    let c := D.nodeCostWithCost a
    let r := D.budgetScan as
    (c.1.natAbs+r.1,c.2+r.2+5)

theorem budgetScan_value (D : Input n) {L : ℕ} (as : List (Node (Point (Fin n)) L)) :
    (D.budgetScan as).1 = (as.map fun a => (D.nodeCost a).natAbs).sum := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [budgetScan,ih]

theorem budgetScan_bound (D : Input n) {L : ℕ} (as : List (Node (Point (Fin n)) L)) :
    (D.budgetScan as).2 ≤ 13*as.length+1 := by
  induction as with
  | nil => simp [budgetScan]
  | cons a as ih =>
    have h := D.nodeCostWithCost_bound a
    simp only [budgetScan,List.length_cons]
    omega

theorem budgetScan_eq (D : Input n) (s t : Fin n) (L B : ℕ)
    (E : ResidualSearch.Enumeration (Node (Point (Fin n)) L)) :
    (D.budgetScan E.vertices).1 = budget (candidateClosure D.graph s t D.cut L B) := by
  have hu : E.vertices.toFinset = Finset.univ := by ext a; simp [E.complete]
  rw [budgetScan_value, ← List.sum_toFinset _ E.nodup, hu]
  apply Finset.sum_congr rfl
  intro a _
  rw [nodeCost_eq D s t L B]

/-- Direct capacity predicates. Every call is a bounded straight-line program
on encoded vertices, integer levels, and the two retained Boolean arrays. -/
def directCapacity (D : Input n) (s t : Fin n) (L B β : ℕ) :
    Capacity (Vertex (Node (Point (Fin n)) L))
  | .inr false, .inl a =>
    (-D.nodeCost a).toNat + if a.2 ≤ (if a.1.1=TerminalPorts.sink t then L else 0) then β+1 else 0
  | .inl a, .inr true =>
    (D.nodeCost a).toNat + if (if a.1.1=TerminalPorts.source s then 0 else L) < a.2 then β+1 else 0
  | .inl a, .inl b =>
    if (a.1=b.1 ∧ b.2≤a.2) ∨
      ((b.2 : ℕ) : ℤ) = ((a.2 : ℕ) : ℤ)-D.bound L B a.1 b.1 then β+1 else 0
  | _,_ => 0

theorem directCapacity_eq (D : Input n) (s t : Fin n) (L B : ℕ) :
    D.directCapacity s t L B (budget (candidateClosure D.graph s t D.cut L B)) =
      capacity (candidateClosure D.graph s t D.cut L B) := by
  have hn (a : Node (Point (Fin n)) L) :
      ¬∃ j, (L : ℤ) < ((a.2 : ℕ) : ℤ) - (system D.graph s t D.cut L B).bound a.1 j := by
    rintro ⟨j,hj⟩
    have hb := D.bound_nonneg L B a.1 j
    rw [D.bound_eq s t L B] at hb
    have ha : ((a.2 : ℕ) : ℤ) ≤ L := by exact_mod_cast Nat.le_of_lt_succ a.2.isLt
    omega
  have hr (a : Node (Point (Fin n)) L) :
      a ∈ (candidateClosure D.graph s t D.cut L B).required ↔
        (a.2 : ℕ) ≤ (if a.1.1=TerminalPorts.sink t then L else 0) := by
    simp only [candidateClosure,mem_required,system]
    split_ifs <;> rfl
  have hf (a : Node (Point (Fin n)) L) :
      a ∈ (candidateClosure D.graph s t D.cut L B).forbidden ↔
        (if a.1.1=TerminalPorts.source s then 0 else L) < (a.2 : ℕ) := by
    simp only [candidateClosure,mem_forbidden,hn a,or_false]
    simp only [system]
    split_ifs <;> rfl
  funext u v
  cases u with
  | inl a =>
    cases v with
    | inl b =>
      simp only [directCapacity,capacity,barrier,candidateClosure,mem_arcs,
        D.bound_eq s t L B]
    | inr b =>
      cases b with
      | false => rfl
      | true => simp only [directCapacity,capacity,positive,barrier,nodeCost_eq D s t L B,hf]
  | inr b =>
    cases b with
    | false =>
      cases v with
      | inl a => simp only [directCapacity,capacity,negative,barrier,nodeCost_eq D s t L B,hr]
      | inr b => cases b <;> rfl
    | true => cases v <;> rfl

/-- Concrete port adjacency: at most four sum-tag inspections, two vector
reads, a comparison/Boolean disjunction, branching and result allocation.
No graph callback is invoked. -/
def portAdjWithCost (D : Input n) : TerminalPorts.Vertex (Fin n) →
    TerminalPorts.Vertex (Fin n) → Bool × ℕ
  | .inl u,.inl v => ((D.adjacency[u.val])[v.val],6)
  | .inr (.inl u),.inl v => ((D.adjacency[u.val])[v.val],6)
  | .inl u,.inr (.inr v) => ((D.adjacency[u.val])[v.val],6)
  | .inr (.inl u),.inr (.inr v) =>
    (decide (u=v) || (D.adjacency[u.val])[v.val],10)
  | _,_ => (false,4)

theorem portAdjWithCost_value (D : Input n) (a b : TerminalPorts.Vertex (Fin n)) :
    (D.portAdjWithCost a b).1 = decide ((TerminalPorts.graph D.graph).Adj a b) := by
  rw [Bool.eq_iff_iff,decide_eq_true_eq]
  rcases a with a | a <;> rcases b with b | b
  · simp [portAdjWithCost,TerminalPorts.graph,graph]
  · cases b <;> simp [portAdjWithCost,TerminalPorts.graph,graph]
  · cases a <;> simp [portAdjWithCost,TerminalPorts.graph,graph]
  · cases a <;> cases b <;> simp [portAdjWithCost,TerminalPorts.graph,graph]

theorem portAdjWithCost_bound (D : Input n) (a b : TerminalPorts.Vertex (Fin n)) :
    (D.portAdjWithCost a b).2 ≤ 10 := by
  rcases a with a | a <;> rcases b with b | b
  · simp only [portAdjWithCost]; omega
  · cases b <;> simp only [portAdjWithCost] <;> omega
  · cases a <;> simp only [portAdjWithCost] <;> omega
  · cases a <;> cases b <;> simp only [portAdjWithCost] <;> omega

/-- Two tag/branch operations, at most one vector read and result allocation. -/
def portCapacityWithCost (D : Input n) (L B : ℕ) : TerminalPorts.Vertex (Fin n) → ℕ × ℕ
  | .inl v => (if D.removed[v.val] then L else B,4)
  | .inr _ => (0,2)

@[simp] theorem portCapacityWithCost_value (D : Input n) (L B : ℕ)
    (a : TerminalPorts.Vertex (Fin n)) :
    (D.portCapacityWithCost L B a).1 = D.portCapacity L B a := by cases a <;> rfl

theorem portCapacityWithCost_bound (D : Input n) (L B : ℕ)
    (a : TerminalPorts.Vertex (Fin n)) : (D.portCapacityWithCost L B a).2 ≤ 4 := by
  cases a <;> simp only [portCapacityWithCost] <;> omega

/-- The extra 32 operations cover two port equalities (at most five word/tag
operations each), six Boolean tests, four conjunctions, three branches, three
casts, two minima and allocation. The retained adjacency and cut reads are
charged in their actual subcomputations. -/
def boundWithCost (D : Input n) (L B : ℕ) (a b : Point (Fin n)) : ℤ × ℕ :=
  let p := D.portCapacityWithCost L B a.1
  let e := D.portAdjWithCost b.1 a.1
  let o : ℤ := if a.1=b.1 ∧ a.2=false ∧ b.2=true then 0 else L
  let g : ℤ := if a.1=b.1 ∧ a.2=true ∧ b.2=false then p.1 else L
  let z : ℤ := if a.2=false ∧ b.2=true ∧ e.1=true then 0 else L
  (min o (min g z),p.2+e.2+32)

@[simp] theorem boundWithCost_value (D : Input n) (L B : ℕ) (a b : Point (Fin n)) :
    (D.boundWithCost L B a b).1 = D.bound L B a b := by
  simp [boundWithCost,bound,orderBound,gap,edgeBound,portAdjWithCost_value]

theorem boundWithCost_bound (D : Input n) (L B : ℕ) (a b : Point (Fin n)) :
    (D.boundWithCost L B a b).2 ≤ 46 := by
  have hp := D.portCapacityWithCost_bound L B a.1
  have he := D.portAdjWithCost_bound b.1 a.1
  simp only [boundWithCost]
  omega

/-- A genuinely compositional capacity computation. Source/sink arms add at
most 18 operations for outer tags, port equality, casts, signs, tests, barrier
addition, final addition and allocation. The core arm adds at most 22 for tags,
point equality, comparisons, casts, subtraction, disjunction and allocation. -/
def capacityWithCost (D : Input n) (s t : Fin n) (L B β : ℕ) :
    Vertex (Node (Point (Fin n)) L) → Vertex (Node (Point (Fin n)) L) → ℕ × ℕ
  | .inr false,.inl a =>
    let c := D.nodeCostWithCost a
    ((-c.1).toNat + if a.2 ≤ (if a.1.1=TerminalPorts.sink t then L else 0) then β+1 else 0,
      c.2+18)
  | .inl a,.inr true =>
    let c := D.nodeCostWithCost a
    (c.1.toNat + if (if a.1.1=TerminalPorts.source s then 0 else L) < a.2 then β+1 else 0,
      c.2+18)
  | .inl a,.inl b =>
    let d := D.boundWithCost L B a.1 b.1
    (if (a.1=b.1 ∧ b.2≤a.2) ∨ ((b.2 : ℕ) : ℤ)=((a.2 : ℕ) : ℤ)-d.1 then β+1 else 0,
      d.2+22)
  | _,_ => (0,4)

@[simp] theorem capacityWithCost_value (D : Input n) (s t : Fin n) (L B β : ℕ)
    (u v : Vertex (Node (Point (Fin n)) L)) :
    (D.capacityWithCost s t L B β u v).1 = D.directCapacity s t L B β u v := by
  cases u with
  | inl a => cases v with
    | inl b => simp [capacityWithCost,directCapacity]
    | inr b => cases b <;> simp [capacityWithCost,directCapacity]
  | inr a => cases a <;> cases v with
    | inl b => simp [capacityWithCost,directCapacity]
    | inr b => cases b <;> rfl

theorem capacityWithCost_bound (D : Input n) (s t : Fin n) (L B β : ℕ)
    (u v : Vertex (Node (Point (Fin n)) L)) :
    (D.capacityWithCost s t L B β u v).2 ≤ 68 := by
  cases u with
  | inl a =>
    cases v with
    | inl b =>
      have h := D.boundWithCost_bound L B a.1 b.1
      simp only [capacityWithCost]
      omega
    | inr b =>
      cases b with
      | false => simp only [capacityWithCost]; omega
      | true =>
        have h := D.nodeCostWithCost_bound a
        simp only [capacityWithCost]
        omega
  | inr a =>
    cases a with
    | false =>
      cases v with
      | inl b =>
        have h := D.nodeCostWithCost_bound b
        simp only [capacityWithCost]
        omega
      | inr b => cases b <;> simp only [capacityWithCost] <;> omega
    | true => cases v <;> simp only [capacityWithCost] <;> omega

open IntegralNetworkFlow.Tabulated

/-- Each cell is computed once; the extra six operations are list case,
integer cast, key/cell construction, list allocation and result allocation. -/
def capacityRow (D : Input n) (s t : Fin n) (L B β : ℕ)
    (u : Vertex (Node (Point (Fin n)) L)) :
    List (Vertex (Node (Point (Fin n)) L)) → List (((Vertex (Node (Point (Fin n)) L)) ×
      Vertex (Node (Point (Fin n)) L)) × ℤ) × ℕ
  | [] => ([],1)
  | v::vs =>
    let a := D.capacityWithCost s t L B β u v
    let b := D.capacityRow s t L B β u vs
    (((u,v),(a.1 : ℤ))::b.1,a.2+b.2+6)

theorem capacityRow_value (D : Input n) (s t : Fin n) (L B β : ℕ)
    (u : Vertex (Node (Point (Fin n)) L)) (vs : List (Vertex (Node (Point (Fin n)) L))) :
    (D.capacityRow s t L B β u vs).1 =
      vs.map fun v => ((u,v),(D.directCapacity s t L B β u v : ℤ)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [capacityRow,ih]

theorem capacityRow_bound (D : Input n) (s t : Fin n) (L B β : ℕ)
    (u : Vertex (Node (Point (Fin n)) L)) (vs : List (Vertex (Node (Point (Fin n)) L))) :
    (D.capacityRow s t L B β u vs).2 ≤ 74*vs.length+1 := by
  induction vs with
  | nil => simp [capacityRow]
  | cons v vs ih =>
    have h := D.capacityWithCost_bound s t L B β u v
    simp only [capacityRow,List.length_cons]
    omega

/-- Nested list construction, including copying the first list in append. -/
def capacityRows (D : Input n) (s t : Fin n) (L B β : ℕ)
    (vs : List (Vertex (Node (Point (Fin n)) L))) :
    List (Vertex (Node (Point (Fin n)) L)) → List (((Vertex (Node (Point (Fin n)) L)) ×
      Vertex (Node (Point (Fin n)) L)) × ℤ) × ℕ
  | [] => ([],1)
  | u::us =>
    let a := D.capacityRow s t L B β u vs
    let b := D.capacityRows s t L B β vs us
    (a.1++b.1,a.2+b.2+2*a.1.length+4)

theorem capacityRows_value (D : Input n) (s t : Fin n) (L B β : ℕ)
    (vs us : List (Vertex (Node (Point (Fin n)) L))) :
    (D.capacityRows s t L B β vs us).1 =
      us.flatMap fun u => vs.map fun v => ((u,v),(D.directCapacity s t L B β u v : ℤ)) := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [capacityRows,capacityRow_value,ih]

theorem capacityRows_bound (D : Input n) (s t : Fin n) (L B β : ℕ)
    (vs us : List (Vertex (Node (Point (Fin n)) L))) :
    (D.capacityRows s t L B β vs us).2 ≤ us.length*(76*vs.length+5)+1 := by
  induction us with
  | nil => simp [capacityRows]
  | cons u us ih =>
    have h := D.capacityRow_bound s t L B β u vs
    simp only [capacityRows,capacityRow_value,List.length_map,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- The retained construction result is an ordinary finite table and a single
budget value. The enumerations are supplied retained lists, not callbacks. -/
structure Construction (n L : ℕ) where
  cells : List ((Vertex (Node (Point (Fin n)) L) × Vertex (Node (Point (Fin n)) L)) × ℤ)
  budget : ℕ
  work : ℕ

def construct (D : Input n) (s t : Fin n) (L B : ℕ)
    (EN : ResidualSearch.Enumeration (Node (Point (Fin n)) L))
    (E : ResidualSearch.Enumeration (Vertex (Node (Point (Fin n)) L))) : Construction n L :=
  let b := D.budgetScan EN.vertices
  let c := D.capacityRows s t L B b.1 E.vertices E.vertices
  ⟨c.1,b.1,b.2+c.2+3⟩

@[simp] theorem construct_budget (D : Input n) (s t : Fin n) (L B : ℕ)
    (EN : ResidualSearch.Enumeration (Node (Point (Fin n)) L))
    (E : ResidualSearch.Enumeration (Vertex (Node (Point (Fin n)) L))) :
    (D.construct s t L B EN E).budget = budget (candidateClosure D.graph s t D.cut L B) :=
  D.budgetScan_eq s t L B EN

theorem construct_cells (D : Input n) (s t : Fin n) (L B : ℕ)
    (EN : ResidualSearch.Enumeration (Node (Point (Fin n)) L))
    (E : ResidualSearch.Enumeration (Vertex (Node (Point (Fin n)) L))) :
    (D.construct s t L B EN E).cells = FlowTable.dense E
      (fun u v => (capacity (candidateClosure D.graph s t D.cut L B) u v : ℤ)) := by
  simp only [construct,capacityRows_value,D.budgetScan_eq s t L B EN,D.directCapacity_eq s t L B,FlowTable.dense]

theorem construct_capacity (D : Input n) (s t : Fin n) (L B : ℕ)
    (EN : ResidualSearch.Enumeration (Node (Point (Fin n)) L))
    (E : ResidualSearch.Enumeration (Vertex (Node (Point (Fin n)) L))) :
    (fun (u v : Vertex (Node (Point (Fin n)) L)) =>
      (IntegralNetworkFlow.Tabulated.read (u,v) (D.construct s t L B EN E).cells).1.toNat) =
      capacity (candidateClosure D.graph s t D.cut L B) := by
  funext u v
  simp [construct_cells,FlowTable.read_dense]

theorem construct_length (D : Input n) (s t : Fin n) (L B : ℕ)
    (EN : ResidualSearch.Enumeration (Node (Point (Fin n)) L))
    (E : ResidualSearch.Enumeration (Vertex (Node (Point (Fin n)) L))) :
    (D.construct s t L B EN E).cells.length =
      (Fintype.card (Vertex (Node (Point (Fin n)) L)))^2 := by
  rw [construct_cells,FlowTable.dense_length]

theorem network_card (n L : ℕ) :
    Fintype.card (Vertex (Node (Point (Fin n)) L)) = 6*n*(L+1)+2 := by
  simp only [MinimumClosureCut.Vertex,Fintype.card_sum,Fintype.card_bool,card_node,card_point,Fintype.card_fin]

theorem construct_bound (D : Input n) (s t : Fin n) (L B : ℕ)
    (EN : ResidualSearch.Enumeration (Node (Point (Fin n)) L))
    (E : ResidualSearch.Enumeration (Vertex (Node (Point (Fin n)) L))) :
    (D.construct s t L B EN E).work ≤ 90*(6*n*(L+1)+3)^2 := by
  have hb := D.budgetScan_bound EN.vertices
  have hc := D.capacityRows_bound s t L B (D.budgetScan EN.vertices).1 E.vertices E.vertices
  rw [EN.length_eq_card,card_node,card_point,Fintype.card_fin] at hb
  rw [E.length_eq_card,network_card] at hc
  simp only [construct]
  nlinarith

theorem construct_cell_bits (D : Input n) (s t : Fin n) (L B : ℕ) (hL : L ≤ n)
    (EN : ResidualSearch.Enumeration (Node (Point (Fin n)) L))
    (E : ResidualSearch.Enumeration (Vertex (Node (Point (Fin n)) L)))
    (e : Vertex (Node (Point (Fin n)) L) × Vertex (Node (Point (Fin n)) L)) (z : ℤ)
    (hz : (e,z) ∈ (D.construct s t L B EN E).cells) :
    1+Nat.size z.natAbs ≤ 1+Nat.size (12*n*(n+1)+1) := by
  rw [construct_cells] at hz
  simp only [FlowTable.dense,List.mem_flatMap,List.mem_map] at hz
  obtain ⟨u,_,v,_,h⟩ := hz
  cases h
  have hc := ClosureRuntime.candidate_capacity_polynomial D.graph s t D.cut L B
    (by simpa using hL) u v
  simpa using Nat.add_le_add_left (Nat.size_le_size hc) 1

/-- The bound is in [0,L] even if the supplied epoch cap B is enormous. -/
theorem bound_le_limit (D : Input n) (L B : ℕ) (a b : Point (Fin n)) :
    D.bound L B a b ≤ L := by
  apply (min_le_left _ _).trans
  unfold orderBound
  split <;> omega

theorem bound_natAbs_le (D : Input n) (L B : ℕ) (a b : Point (Fin n)) :
    (D.bound L B a b).natAbs ≤ L := by
  have h := D.bound_le_limit L B a b
  rw [← Int.natAbs_of_nonneg (D.bound_nonneg L B a b)] at h
  exact_mod_cast h

theorem nodeCost_natAbs_le (D : Input n) {L : ℕ} (a : Node (Point (Fin n)) L) :
    (D.nodeCost a).natAbs ≤ 1 := by
  unfold nodeCost
  split
  · decide
  · rw [cost_eq]
    exact integerCosts_abs_le _ _

/-- This is the only numeric temporary that can contain B rather than a
polynomial in n,L: the selected outside cap, before taking the minimum. -/
theorem portCapacity_le (D : Input n) (L B : ℕ) (a : TerminalPorts.Vertex (Fin n)) :
    D.portCapacity L B a ≤ L+B := by
  cases a with
  | inl v => cases h : D.removed[v.val] <;> simp [portCapacity,h]
  | inr a => simp [portCapacity]

theorem shiftedLevel_natAbs_le (D : Input n) (L B : ℕ)
    (a : Node (Point (Fin n)) L) (b : Point (Fin n)) :
    (((a.2 : ℕ) : ℤ)-D.bound L B a.1 b).natAbs ≤ 2*L := by
  have h := Int.natAbs_sub_le ((a.2 : ℕ) : ℤ) (D.bound L B a.1 b)
  have hb := D.bound_natAbs_le L B a.1 b
  have ha := a.2.isLt
  simp only [Int.natAbs_natCast] at h
  omega

/-- Binary addition enlarges the larger operand width by at most one bit. -/
theorem size_add_le (a b : ℕ) : Nat.size (a+b) ≤ Nat.size a+Nat.size b+1 := by
  have ha : a < 2^(Nat.size a+Nat.size b) :=
    (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hb : b < 2^(Nat.size a+Nat.size b) :=
    (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  apply Nat.size_le.mpr
  rw [pow_succ]
  omega

/-- Signed scalar width for construction. B contributes its binary input
length, never a loop of B iterations. Multiprecision operation costs are a
separate refinement of the declared word model. -/
def constructionBits (n L B : ℕ) : ℕ :=
  Nat.size B + Nat.size (12*n*(L+1)+2*L+n+3) + 2

theorem scalar_bits (n L B k : ℕ) (hk : k ≤ B+(12*n*(L+1)+2*L+n+3)) :
    1+Nat.size k ≤ constructionBits n L B := by
  have hm := Nat.size_le_size hk
  have hs := size_add_le B (12*n*(L+1)+2*L+n+3)
  unfold constructionBits
  omega

theorem cap_temporary_bits (D : Input n) (L B : ℕ) (a : TerminalPorts.Vertex (Fin n)) :
    1+Nat.size (D.portCapacity L B a) ≤ constructionBits n L B := by
  apply scalar_bits
  have h := D.portCapacity_le L B a
  omega

theorem shiftedLevel_bits (D : Input n) (L B : ℕ)
    (a : Node (Point (Fin n)) L) (b : Point (Fin n)) :
    1+Nat.size ((((a.2 : ℕ) : ℤ)-D.bound L B a.1 b).natAbs) ≤ constructionBits n L B := by
  apply scalar_bits
  have h := D.shiftedLevel_natAbs_le L B a b
  omega

theorem constructed_flow_bits (D : Input n) (s t : Fin n) (L B : ℕ) (hL : L ≤ n)
    (EN : ResidualSearch.Enumeration (Node (Point (Fin n)) L))
    (E : ResidualSearch.Enumeration (Vertex (Node (Point (Fin n)) L)))
    (T : FlowTable (fun (u v : Vertex (Node (Point (Fin n)) L)) =>
      (IntegralNetworkFlow.Tabulated.read (u,v) (D.construct s t L B EN E).cells).1.toNat) source sink)
    (e : Vertex (Node (Point (Fin n)) L) × Vertex (Node (Point (Fin n)) L)) (z : ℤ)
    (hz : (e,z) ∈ T.cells) :
    1+Nat.size z.natAbs ≤ 1+Nat.size (12*n*(n+1)+1) := by
  apply T.cell_signed_bits_le (12*n*(n+1)+1) _ e z hz
  intro u v
  have he := congrFun (congrFun (D.construct_capacity s t L B EN E) u) v
  change (IntegralNetworkFlow.Tabulated.read (u,v) (D.construct s t L B EN E).cells).1.toNat = _ at he
  rw [he]
  simpa using ClosureRuntime.candidate_capacity_polynomial D.graph s t D.cut L B
    (by simpa using hL) u v

end Input
end DirectedFlowCutGap.EncodedCandidateCapacity
