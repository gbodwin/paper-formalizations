import DirectedFlowCutGap.ResidualSearchComplexity

/-!
# Retained finite tables for integral augmentation

The executable state contains one finite list of integer cells. Its feasibility
fields are propositions and disappear on extraction. In particular `asFlow`
reads that list; it does not close over any earlier augmentation. The edge list
of each selected path is materialized once, and the next table is a strict map
of the preceding table. `run_refines` identifies the exact output with the
frozen finite-search recursion, including its deterministic path choices.
-/
namespace DirectedFlowCutGap.IntegralNetworkFlow.Tabulated

open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An explicit short-circuiting table lookup and its number of inspected cells. -/
def read {K : Type*} [DecidableEq K] (k : K) : List (K × ℤ) → ℤ × ℕ
  | [] => (0, 0)
  | (a, z) :: xs => if a = k then (z, 1) else
      let r := read k xs
      (r.1, r.2 + 1)

theorem read_count_le {K : Type*} [DecidableEq K] (k : K) (xs : List (K × ℤ)) :
    (read k xs).2 ≤ xs.length := by
  induction xs with
  | nil => simp [read]
  | cons x xs ih =>
    rcases x with ⟨a,z⟩
    by_cases h : a = k <;> simp [read, h, ih]

theorem read_eq_of_cells {K : Type*} [DecidableEq K] (xs : List (K × ℤ))
    (f : K → ℤ) (h : ∀ a z, (a,z) ∈ xs → z = f a)
    (k : K) (hk : k ∈ xs.map Prod.fst) : (read k xs).1 = f k := by
  induction xs with
  | nil => simp at hk
  | cons x xs ih =>
    rcases x with ⟨a,z⟩
    by_cases ha : a = k
    · subst a
      simpa [read] using h k z (by simp)
    · have hk' : k ∈ xs.map Prod.fst := by simpa [ha, Ne.symm ha] using hk
      simpa [read, ha] using ih (fun a z hz => h a z (by simp [hz])) hk'

/-- Updating a complete table preserves lookup semantics, even if keys repeat. -/
theorem read_map {K : Type*} [DecidableEq K] (xs : List (K × ℤ))
    (f : K → ℤ → ℤ) (k : K) (hk : k ∈ xs.map Prod.fst) :
    (read k (xs.map fun e => (e.1, f e.1 e.2))).1 = f k (read k xs).1 := by
  induction xs with
  | nil => simp at hk
  | cons x xs ih =>
    rcases x with ⟨a,z⟩
    by_cases ha : a = k
    · simp [read, ha]
    · have hk' : k ∈ xs.map Prod.fst := by simpa [ha, Ne.symm ha] using hk
      simpa [read, ha] using ih hk'

/-- Feasibility is checked against the cells themselves, with no executable
reference to a historical functional flow. -/
structure FlowTable (c : Capacity V) (s t : V) where
  cells : List ((V × V) × ℤ)
  complete : ∀ u v, (u,v) ∈ cells.map Prod.fst
  coherent : ∀ e z, (e,z) ∈ cells → z = (read e cells).1
  antisymm : ∀ u v, (read (u,v) cells).1 = -(read (v,u) cells).1
  upper : ∀ u v, (read (u,v) cells).1 ≤ (c u v : ℤ)
  conserve : ∀ v, v ≠ s → v ≠ t → ∑ u, (read (v,u) cells).1 = 0

namespace FlowTable
variable {c : Capacity V} {s t : V}

def asFlow (T : FlowTable c s t) : Flow c s t where
  amount := fun u v => (read (u,v) T.cells).1
  antisymm := T.antisymm
  upper := T.upper
  conserve := T.conserve

omit [DecidableEq V] in
theorem flow_ext (f g : Flow c s t) (h : ∀ u v, f.amount u v = g.amount u v) : f = g := by
  have ha : f.amount = g.amount := funext fun u => funext (h u)
  cases f
  cases g
  cases ha
  rfl

/-- Materialize all ordered pairs in the supplied vertex order. -/
def dense (E : ResidualSearch.Enumeration V) (f : V → V → ℤ) : List ((V × V) × ℤ) :=
  E.vertices.flatMap fun u => E.vertices.map fun v => ((u,v), f u v)

omit [Fintype V] [DecidableEq V] in
theorem dense_complete (E : ResidualSearch.Enumeration V) (f : V → V → ℤ) (u v : V) :
    (u,v) ∈ (dense E f).map Prod.fst := by
  simp only [dense, List.mem_map, List.mem_flatMap]
  exact ⟨((u,v), f u v), ⟨u, E.complete u, v, E.complete v, rfl⟩, rfl⟩

omit [Fintype V] in
theorem read_dense (E : ResidualSearch.Enumeration V) (f : V → V → ℤ) (u v : V) :
    (read (u,v) (dense E f)).1 = f u v := by
  apply read_eq_of_cells (dense E f) (fun e => f e.1 e.2) _ (u,v) (dense_complete E f u v)
  intro a z h
  simp only [dense, List.mem_flatMap, List.mem_map] at h
  obtain ⟨i, _, j, _, he⟩ := h
  cases he
  rfl

theorem dense_length (E : ResidualSearch.Enumeration V) (f : V → V → ℤ) :
    (dense E f).length = (Fintype.card V)^2 := by
  simp [dense, List.length_flatMap, E.length_eq_card, pow_two]

/-- Retaining an arbitrary initial flow costs one materialization. -/
def materialize (E : ResidualSearch.Enumeration V) (f : Flow c s t) : FlowTable c s t where
  cells := dense E f.amount
  complete := dense_complete E f.amount
  coherent := by
    intro e z h
    rw [read_dense]
    simp only [dense, List.mem_flatMap, List.mem_map] at h
    obtain ⟨u, _, v, _, he⟩ := h
    cases he
    rfl
  antisymm := by simpa only [read_dense] using f.antisymm
  upper := by simpa only [read_dense] using f.upper
  conserve := by simpa only [read_dense] using f.conserve

@[simp] theorem materialize_asFlow (E : ResidualSearch.Enumeration V) (f : Flow c s t) :
    (materialize E f).asFlow = f :=
  flow_ext _ _ (read_dense E f.amount)

/-- A path's edge list is concrete data shared by all cell updates. -/
def edgeList {G : Digraph V} (p : SimplePath G s t) : List (V × V) := List.ofFn p.edgeAt

omit [Fintype V] in
@[simp] theorem mem_edgeList {G : Digraph V} (p : SimplePath G s t) (e : V × V) :
    e ∈ edgeList p ↔ e ∈ p.edges := by simp [edgeList, SimplePath.mem_edges]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem edgeList_length {G : Digraph V} (p : SimplePath G s t) :
    (edgeList p).length = p.edgeLength := by simp [edgeList]

/-- Materialized directed path signals; the counter records actual list tests. -/
def signal (es : List (V × V)) (e : V × V) : ℤ × ℕ :=
  let r := ResidualSearch.scan (fun a => a = e) es
  (if r.1.isSome then 1 else 0, r.2)

omit [Fintype V] in
theorem signal_value (es : List (V × V)) (e : V × V) :
    (signal es e).1 = if e ∈ es then 1 else 0 := by
  induction es with
  | nil => simp [signal, ResidualSearch.scan]
  | cons a es ih =>
    by_cases h : a = e
    · simp [signal, ResidualSearch.scan, h]
    · simpa [signal, ResidualSearch.scan, h, Ne.symm h] using ih

omit [Fintype V] in
theorem signal_count_le (es : List (V × V)) (e : V × V) :
    (signal es e).2 ≤ es.length := ResidualSearch.scan_count_le _ _

omit [Fintype V] in
theorem signal_edgeList {G : Digraph V} (p : SimplePath G s t) (u v : V) :
    (signal (edgeList p) (u,v)).1 = pathSignal p u v := by
  simp [signal_value, pathSignal]

/-- Each row performs two counted signal scans and two integer operations.
The result stores the new integer, not a function referring to the old row. -/
def updateCells (es : List (V × V)) : List ((V × V) × ℤ) → List ((V × V) × ℤ) × ℕ
  | [] => ([], 0)
  | (e,z) :: xs =>
      let a := signal es e
      let b := signal es (e.2,e.1)
      let r := updateCells es xs
      ((e,z+a.1-b.1) :: r.1, a.2+b.2+2+r.2)

omit [Fintype V] in
theorem updateCells_value (es : List (V × V)) (xs : List ((V × V) × ℤ)) :
    (updateCells es xs).1 = xs.map fun e =>
      (e.1, e.2 + (signal es e.1).1 - (signal es (e.1.2,e.1.1)).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x; simp [updateCells, ih]

omit [Fintype V] in
theorem updateCells_length (es : List (V × V)) (xs : List ((V × V) × ℤ)) :
    (updateCells es xs).1.length = xs.length := by simp [updateCells_value]

omit [Fintype V] in
theorem updateCells_count_le (es : List (V × V)) (xs : List ((V × V) × ℤ)) :
    (updateCells es xs).2 ≤ xs.length * (2 * es.length + 2) := by
  induction xs with
  | nil => simp [updateCells]
  | cons x xs ih =>
    have ha := signal_count_le es x.1
    have hb := signal_count_le es (x.1.2,x.1.1)
    cases x
    dsimp only at ha hb
    simp only [updateCells, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem updateCells_read (T : FlowTable c s t) (p : SimplePath T.asFlow.residual s t) (u v : V) :
    (read (u,v) (updateCells (edgeList p) T.cells).1).1 = (T.asFlow.augment p).amount u v := by
  rw [updateCells_value, read_map T.cells
    (fun e z => z + (signal (edgeList p) e).1 - (signal (edgeList p) (e.2,e.1)).1)
    (u,v) (T.complete u v)]
  change (read (u,v) T.cells).1 + (signal (edgeList p) (u,v)).1 -
    (signal (edgeList p) (v,u)).1 =
    T.asFlow.amount u v + pathSignal p u v - pathSignal p v u
  rw [signal_edgeList, signal_edgeList]
  rfl

def augmentWithCost (T : FlowTable c s t) (p : SimplePath T.asFlow.residual s t) :
    FlowTable c s t × ℕ :=
  let es := edgeList p
  let r := updateCells es T.cells
  ({ cells := r.1
     complete := by
       intro u v
       simpa only [es, r, updateCells_value, List.map_map, Function.comp_def] using T.complete u v
     coherent := by
       intro e z h
       change (e,z) ∈ (updateCells (edgeList p) T.cells).1 at h
       rw [updateCells_value] at h
       obtain ⟨⟨a,b⟩, hab, he⟩ := List.mem_map.mp h
       cases he
       change b + (signal (edgeList p) a).1 - (signal (edgeList p) (a.2,a.1)).1 =
         (read a (updateCells (edgeList p) T.cells).1).1
       rw [updateCells_value, read_map T.cells
         (fun e z => z + (signal (edgeList p) e).1 - (signal (edgeList p) (e.2,e.1)).1)
         a (T.complete a.1 a.2), T.coherent a b hab]
     antisymm := by simpa only [es, r, updateCells_read] using (T.asFlow.augment p).antisymm
     upper := by simpa only [es, r, updateCells_read] using (T.asFlow.augment p).upper
     conserve := by simpa only [es, r, updateCells_read] using (T.asFlow.augment p).conserve }, r.2)

def augment (T : FlowTable c s t) (p : SimplePath T.asFlow.residual s t) : FlowTable c s t :=
  (augmentWithCost T p).1

@[simp] theorem augment_asFlow (T : FlowTable c s t) (p : SimplePath T.asFlow.residual s t) :
    (T.augment p).asFlow = T.asFlow.augment p := flow_ext _ _ (updateCells_read T p)

@[simp] theorem augment_length (T : FlowTable c s t) (p : SimplePath T.asFlow.residual s t) :
    (T.augment p).cells.length = T.cells.length := updateCells_length _ _

/-- The actual retained-state step uses the frozen deterministic search. -/
def step (E : ResidualSearch.Enumeration V) (T : FlowTable c s t) : FlowTable c s t :=
  match finiteResidualSearch E c s t T.asFlow with
  | .found p => T.augment p
  | .stopped _ => T

@[simp] theorem step_asFlow (E : ResidualSearch.Enumeration V) (T : FlowTable c s t) :
    (T.step E).asFlow = T.asFlow.step (finiteResidualSearch E c s t) := by
  unfold step Flow.step
  cases finiteResidualSearch E c s t T.asFlow <;> simp

@[simp] theorem step_length (E : ResidualSearch.Enumeration V) (T : FlowTable c s t) :
    (T.step E).cells.length = T.cells.length := by
  unfold step
  cases finiteResidualSearch E c s t T.asFlow <;> simp

/-- No earlier table or functional flow is stored in the next iteration. -/
def run (E : ResidualSearch.Enumeration V) (T : FlowTable c s t) : ℕ → FlowTable c s t
  | 0 => T
  | k+1 => (run E T k).step E

theorem run_refines (E : ResidualSearch.Enumeration V) (T : FlowTable c s t) (k : ℕ) :
    (run E T k).asFlow = IntegralNetworkFlow.run (finiteResidualSearch E c s t) T.asFlow k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [run, step_asFlow, IntegralNetworkFlow.run_succ, ih]

theorem run_length (E : ResidualSearch.Enumeration V) (T : FlowTable c s t) (k : ℕ) :
    (run E T k).cells.length = T.cells.length := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [run, step_length] using ih


/-- A charged step executes the same search and table update. Search tests are
charged for a full scan of the retained flow table; this is a conservative
upper charge, not an assertion that every lookup reaches the final cell.
Path-edge accesses are charged separately by `edgeAccessCharge` below. -/
def stepWithCost (E : ResidualSearch.Enumeration V) (T : FlowTable c s t) :
    FlowTable c s t × ℕ :=
  let r := finiteResidualSearchWithCost E T.asFlow
  match r.1 with
  | .found p =>
      let a := T.augmentWithCost p
      (a.1, r.2 * (T.cells.length + 1) +
        a.2 + T.cells.length + p.edgeLength)
  | .stopped _ => (T, r.2 * (T.cells.length + 1))

theorem stepWithCost_table (E : ResidualSearch.Enumeration V) (T : FlowTable c s t) :
    (stepWithCost E T).1 = T.step E := by
  unfold stepWithCost step finiteResidualSearch
  dsimp only
  cases (finiteResidualSearchWithCost E T.asFlow).1 <;> rfl

/-- The charge covers flow-cell scans, residual comparisons, materialized edge
cells, signal scans, integer updates, and new flow cells. It does not count
capacity evaluation or evaluation of a path's functional vertex coordinates. -/
def stepCharge (N M : ℕ) : ℕ :=
  (2*N^3+N)*(M+1) + M*(2*N+2) + M + N

theorem stepWithCost_bound (E : ResidualSearch.Enumeration V) (T : FlowTable c s t) :
    (stepWithCost E T).2 ≤ stepCharge (Fintype.card V) T.cells.length := by
  have hq := finiteResidualSearchWithCost_bound E T.asFlow
  unfold stepWithCost
  dsimp only
  split
  · rename_i p hp
    have hu := updateCells_count_le (edgeList p) T.cells
    rw [edgeList_length] at hu
    have hl := p.edgeLength_lt_card
    have hmul := Nat.mul_le_mul_left T.cells.length
      (show 2*p.edgeLength+2 ≤ 2*Fintype.card V+2 by omega)
    have hqm := Nat.mul_le_mul_right (T.cells.length+1) hq
    change _ + (updateCells (edgeList p) T.cells).2 + _ + _ ≤ _
    unfold stepCharge
    omega
  · have hqm := Nat.mul_le_mul_right (T.cells.length+1) hq
    dsimp only
    unfold stepCharge
    omega

def runWithCost (E : ResidualSearch.Enumeration V) (T : FlowTable c s t) :
    ℕ → FlowTable c s t × ℕ
  | 0 => (T,0)
  | k+1 =>
      let a := runWithCost E T k
      let b := stepWithCost E a.1
      (b.1,a.2+b.2)

theorem runWithCost_table (E : ResidualSearch.Enumeration V) (T : FlowTable c s t) (k : ℕ) :
    (runWithCost E T k).1 = run E T k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [runWithCost, stepWithCost_table, ih, run]

theorem runWithCost_bound (E : ResidualSearch.Enumeration V) (T : FlowTable c s t) (k : ℕ) :
    (runWithCost E T k).2 ≤ k * stepCharge (Fintype.card V) T.cells.length := by
  induction k with
  | zero => simp [runWithCost]
  | succ k ih =>
    have hb := stepWithCost_bound E (runWithCost E T k).1
    have hl : (runWithCost E T k).1.cells.length = T.cells.length := by
      rw [runWithCost_table, run_length]
    rw [hl] at hb
    change (runWithCost E T k).2 + (stepWithCost E (runWithCost E T k).1).2 ≤ _
    calc
      _ ≤ k * stepCharge (Fintype.card V) T.cells.length +
          stepCharge (Fintype.card V) T.cells.length := Nat.add_le_add ih hb
      _ = _ := by ring

/-- All stored reads satisfy the two directional capacity bounds. -/
theorem amount_bounds (T : FlowTable c s t) (u v : V) :
    -(c v u : ℤ) ≤ (read (u,v) T.cells).1 ∧ (read (u,v) T.cells).1 ≤ (c u v : ℤ) :=
  ⟨T.asFlow.lower u v, T.upper u v⟩

/-- Uniform finite capacities bound every retained integer, independent of the
number of earlier updates. -/
theorem amount_natAbs_le (T : FlowTable c s t) (C : ℕ) (hc : ∀ u v, c u v ≤ C) (u v : V) :
    (read (u,v) T.cells).1.natAbs ≤ C := by
  have hl := (amount_bounds T u v).1
  have hu := (amount_bounds T u v).2
  have hlu : (c v u : ℤ) ≤ C := by exact_mod_cast hc v u
  have huu : (c u v : ℤ) ≤ C := by exact_mod_cast hc u v
  omega

/-- The magnitude bound applies to every stored cell, not only lookup results. -/
theorem cell_natAbs_le (T : FlowTable c s t) (C : ℕ) (hc : ∀ u v, c u v ≤ C)
    (e : V × V) (z : ℤ) (hz : (e,z) ∈ T.cells) : z.natAbs ≤ C := by
  rw [T.coherent e z hz]
  exact T.amount_natAbs_le C hc e.1 e.2

/-- One sign bit plus the binary magnitude suffices for every retained integer. -/
theorem cell_signed_bits_le (T : FlowTable c s t) (C : ℕ) (hc : ∀ u v, c u v ≤ C)
    (e : V × V) (z : ℤ) (hz : (e,z) ∈ T.cells) :
    1 + Nat.size z.natAbs ≤ 1 + Nat.size C := by
  exact Nat.add_le_add_left (Nat.size_le_size (T.cell_natAbs_le C hc e z hz)) 1

end FlowTable
end DirectedFlowCutGap.IntegralNetworkFlow.Tabulated
