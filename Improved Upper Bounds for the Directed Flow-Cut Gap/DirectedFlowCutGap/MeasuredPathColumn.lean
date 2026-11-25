import DirectedFlowCutGap.MeasuredPathMembership
import DirectedFlowCutGap.BinaryNaturalOperations
import DirectedFlowCutGap.ConcurrentVertexOracleWork
import DirectedFlowCutGap.BinaryFractionalGraphBounds

/-! Form the joint column with measured binary path membership tests and
accumulation of visit counts.  The count is the original per-demand
multiplicity, including a zero contribution for a missing retained path. -/
namespace DirectedFlowCutGap.MeasuredPathColumn

open scoped BigOperators
open IntegralNetworkFlow
open BinaryFractionalWalkOracle (Adjacency Candidate)
open ConcurrentEdgeOracle (Edge Resource)
open MultiplicityCover (Column)

variable {n m : ℕ}

def indicator (p : Bool) : ℕ := if p then 1 else 0

private theorem indicator_le (p : Bool) : indicator p ≤ 1 := by
  cases p <;> decide

private def sumChecks : List (Bool × ℕ) → ℕ × ℕ
  | [] => (0,1)
  | x::xs =>
    let rest := sumChecks xs
    let total := BinaryNaturalOperations.add (indicator x.1) rest.1
    (total.1,x.2+rest.2+total.2+4)

private theorem sumChecks_value (xs : List (Bool × ℕ)) :
    (sumChecks xs).1 = (xs.map fun x => indicator x.1).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [sumChecks,BinaryNaturalOperations.add_value,List.map_cons,List.sum_cons,ih]

private theorem sumChecks_count (xs : List (Bool × ℕ)) : (sumChecks xs).1 ≤ xs.length := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    simp only [sumChecks,BinaryNaturalOperations.add_value,List.length_cons,Nat.add_comm xs.length]
    exact Nat.add_le_add (indicator_le _) ih

def rowWork (m perDemand : ℕ) : ℕ :=
  m*(perDemand+BinaryRawRational.budget (m.size+1)+8)+1

private theorem sumChecks_charge (xs : List (Bool × ℕ)) {m perDemand : ℕ}
    (len : xs.length ≤ m) (fits : ∀ x ∈ xs, x.2 ≤ perDemand) :
    (sumChecks xs).2 ≤ xs.length*(perDemand+BinaryRawRational.budget (m.size+1)+8)+1 := by
  induction xs with
  | nil => simp [sumChecks]
  | cons x xs ih =>
    have shorter : xs.length ≤ m := by simp only [List.length_cons] at len; omega
    have tail := ih shorter (fun y member => fits y (List.mem_cons_of_mem _ member))
    have this := fits x List.mem_cons_self
    have count := (sumChecks_count xs).trans shorter
    have left : (indicator x.1).size ≤ m.size+1 :=
      ((BinaryNaturalOperations.size_le_self _).trans (indicator_le _)).trans (by omega)
    have right : (sumChecks xs).1.size ≤ m.size+1 :=
      (Nat.size_le_size count).trans (by omega)
    have add := BinaryNaturalOperations.add_paid left right
    simp only [sumChecks,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

private def edgeTest (e : Edge n) : Option (Candidate n) → Bool × ℕ
  | none => (false,1)
  | some p => MeasuredPathMembership.arc e p.edges

private theorem edgeTest_value (e : Edge n) (p : Option (Candidate n)) :
    (edgeTest e p).1 = (p.map fun q => q.edges.contains e).getD false := by
  cases p with
  | none => rfl
  | some q =>
    apply Bool.eq_iff_iff.mpr
    simpa only [edgeTest,Option.map_some,Option.getD_some,List.contains_iff_mem]
      using MeasuredPathMembership.arc_value e q.edges

def PathsFit (paths : Vector (Option (Candidate n)) m) : Prop :=
  ∀ j p, paths.get j = some p → p.edges.length ≤ n

def edgeTestWork (n : ℕ) : ℕ := n*(MeasuredPathMembership.arcComparisonWork n.size+4)+1

private theorem edgeTest_charge (e : Edge n) (p : Option (Candidate n))
    (fits : ∀ q, p = some q → q.edges.length ≤ n) : (edgeTest e p).2 ≤ edgeTestWork n := by
  cases p with
  | none => simp [edgeTest,edgeTestWork]
  | some q =>
    exact (MeasuredPathMembership.arc_charge e q.edges).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ (fits q rfl)) 1)

private def vertexTest (v : Fin n) (d : Edge n) : Option (Candidate n) → Bool × ℕ
  | none => (false,1)
  | some p => MeasuredPathMembership.internal v d.1 d.2 p.edges

private theorem vertexTest_value (v : Fin n) (d : Edge n) (p : Option (Candidate n)) :
    (vertexTest v d p).1 = (p.map fun q =>
      decide (v ∈ FractionalCoverGraphOracle.internalColumn d.1 d.2 q.edges)).getD false := by
  cases p with
  | none => rfl
  | some q =>
    apply Bool.eq_iff_iff.mpr
    simpa only [vertexTest,Option.map_some,Option.getD_some,decide_eq_true_eq]
      using MeasuredPathMembership.internal_value v d.1 d.2 q.edges

def vertexTestWork (n : ℕ) : ℕ := MeasuredPathMembership.internalWork n.size n

private theorem vertexTest_charge (v : Fin n) (d : Edge n) (p : Option (Candidate n))
    (fits : ∀ q, p = some q → q.edges.length ≤ n) :
    (vertexTest v d p).2 ≤ vertexTestWork n := by
  unfold vertexTestWork MeasuredPathMembership.internalWork
  cases p with
  | none => simp only [vertexTest]; omega
  | some q =>
    have used := MeasuredPathMembership.internal_charge v d.1 d.2 q.edges
    have scan := Nat.mul_le_mul_right (MeasuredPathMembership.vertexComparisonWork n.size+4) (fits q rfl)
    unfold MeasuredPathMembership.internalWork at used
    change (MeasuredPathMembership.internal v d.1 d.2 q.edges).2 ≤ _
    omega

def resourceCount (calls : Fin m → Bool × ℕ) : ℕ × ℕ := sumChecks (List.ofFn calls)

theorem resourceCount_value (calls : Fin m → Bool × ℕ) :
    (resourceCount calls).1 = ∑ j : Fin m, indicator (calls j).1 := by
  simp only [resourceCount,sumChecks_value,List.map_ofFn,List.sum_ofFn]
  rfl

theorem resourceCount_le (calls : Fin m → Bool × ℕ) : (resourceCount calls).1 ≤ m := by
  simpa only [resourceCount,List.length_ofFn] using sumChecks_count (List.ofFn calls)

theorem resourceCount_charge (calls : Fin m → Bool × ℕ) {perDemand : ℕ}
    (fits : ∀ j, (calls j).2 ≤ perDemand) : (resourceCount calls).2 ≤ rowWork m perDemand := by
  simpa only [resourceCount,rowWork,List.length_ofFn] using
    sumChecks_charge (List.ofFn calls) (Nat.le_of_eq List.length_ofFn)
      (fun x hx => by
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
        exact fits i)

def edge (paths : Vector (Option (Candidate n)) m) : Column (n*n) × ℕ :=
  let rows := Vector.ofFn fun i : Resource n => resourceCount fun j =>
    edgeTest (ConcurrentEdgeOracle.edge i) (paths.get j)
  (rows.map Prod.fst,∑ i : Resource n, (rows.get i).2)

theorem edge_value (paths : Vector (Option (Candidate n)) m) :
    (edge paths).1 = ConcurrentEdgeOracle.column paths := by
  apply Vector.ext
  intro i hi
  simp only [edge,ConcurrentEdgeOracle.column,Vector.getElem_map,Vector.getElem_ofFn,
    resourceCount_value,edgeTest_value,indicator]

def edgeWork (n m : ℕ) : ℕ := n*n*rowWork m (edgeTestWork n)

theorem edge_charge (paths : Vector (Option (Candidate n)) m) (fits : PathsFit paths) :
    (edge paths).2 ≤ edgeWork n m := by
  unfold edge edgeWork
  dsimp only
  simp only [Vector.get_ofFn]
  calc
    _ ≤ ∑ _i : Resource n, rowWork m (edgeTestWork n) :=
      Finset.sum_le_sum (fun _i _ => resourceCount_charge _
        (fun j => edgeTest_charge _ _ (fits j)))
    _ = _ := by simp

def vertex (P : Vector (Edge n) m) (paths : Vector (Option (Candidate n)) m) : Column n × ℕ :=
  let rows := Vector.ofFn fun v : Fin n => resourceCount fun j => vertexTest v (P.get j) (paths.get j)
  (rows.map Prod.fst,∑ v : Fin n, (rows.get v).2)

theorem vertex_value (P : Vector (Edge n) m) (paths : Vector (Option (Candidate n)) m) :
    (vertex P paths).1 = ConcurrentVertexOracle.column P paths := by
  apply Vector.ext
  intro i hi
  simp only [vertex,ConcurrentVertexOracle.column,Vector.getElem_map,Vector.getElem_ofFn,
    resourceCount_value,vertexTest_value,indicator]

def vertexWork (n m : ℕ) : ℕ := n*rowWork m (vertexTestWork n)

theorem vertex_charge (P : Vector (Edge n) m) (paths : Vector (Option (Candidate n)) m)
    (fits : PathsFit paths) : (vertex P paths).2 ≤ vertexWork n m := by
  unfold vertex vertexWork
  dsimp only
  simp only [Vector.get_ofFn]
  calc
    _ ≤ ∑ _i : Fin n, rowWork m (vertexTestWork n) :=
      Finset.sum_le_sum (fun _i _ => resourceCount_charge _
        (fun j => vertexTest_charge _ _ _ (fits j)))
    _ = _ := by simp

theorem edge_cells_fit (A : Adjacency n) (P : Vector (Edge n) m) (y : FractionalCover.Row (n*n)) :
    PathsFit (ConcurrentEdgeOracle.cells A P y) := by
  intro j p hp
  simp only [ConcurrentEdgeOracle.cells,Vector.get_ofFn,ConcurrentEdgeOracle.path] at hp
  exact BinaryFractionalGraphBounds.shortest_edges_length _ _ _ _ _ hp

theorem vertex_cells_fit (A : Adjacency n) (P : Vector (Edge n) m) (y : FractionalCover.Row n) :
    PathsFit (ConcurrentVertexOracle.cells A P y) := by
  intro j p hp
  simp only [ConcurrentVertexOracle.cells,Vector.get_ofFn,ConcurrentVertexOracle.path,
    ConcurrentEdgeOracle.path] at hp
  exact BinaryFractionalGraphBounds.shortest_edges_length _ _ _ _ _ hp

end DirectedFlowCutGap.MeasuredPathColumn
