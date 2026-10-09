import DirectedFlowCutGap.RetainedPathFlow

/-!
# Early stopping for the retained integral-flow backend

A returned no-path certificate ends the augmentation loop immediately. Exact
identity with the frozen fixed-budget run follows because every later step
would leave the same retained flow table unchanged. The final cut still uses
the same deterministic search and ordered complement conversion.
-/
namespace DirectedFlowCutGap.IntegralNetworkFlow.Tabulated.EarlyStopRetainedFlow

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (cs : List ((V × V) × ℤ)) {s t : V}

/-- Iterating a fixed transition from its first successor commutes with one
last transition. This is an equality of retained data tables. -/
theorem table_run_step (E : ResidualSearch.Enumeration V)
    (T : FlowTable (CountedFlow.capacityOf cs) s t) (k : ℕ) :
    FlowTable.run E (T.step E) k = (FlowTable.run E T k).step E := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [FlowTable.run,ih]

theorem table_run_fixed (E : ResidualSearch.Enumeration V)
    (T : FlowTable (CountedFlow.capacityOf cs) s t) (h : T.step E=T) (k : ℕ) :
    FlowTable.run E T k = T := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [FlowTable.run,ih,h]

/-- A successful search consumes one unit and recurses on the new table; a
stopped search returns immediately, without visiting the unused fuel. -/
def run (E : ResidualSearch.Enumeration V) (T : FlowTable (CountedFlow.capacityOf cs) s t) :
    ℕ → FlowTable (CountedFlow.capacityOf cs) s t × ℕ
  | 0 => (T,1)
  | k+1 =>
    let r := RetainedPathFlow.find cs E T
    match hr : r.result with
    | .found p =>
      let a := RetainedPathFlow.augmentWithEdges cs T p r.edges (by simpa only [hr] using r.correct)
      let b := run E a.1 k
      (b.1,r.work+16*a.2+8*T.cells.length+16+b.2+4)
    | .stopped _ => (T,r.work+4)

theorem run_table (E : ResidualSearch.Enumeration V)
    (T : FlowTable (CountedFlow.capacityOf cs) s t) (k : ℕ) :
    (run cs E T k).1 = FlowTable.run E T k := by
  induction k generalizing T with
  | zero => rfl
  | succ k ih =>
    simp only [run]
    split
    · rename_i p hp
      rw [ih,RetainedPathFlow.augmentWithEdges_table]
      have hs : T.step E = T.augment p := by
        unfold FlowTable.step
        rw [← RetainedPathFlow.find_value cs E T,hp]
      rw [← hs,table_run_step]
      rfl
    · rename_i hn hp
      have hs : T.step E=T := by
        unfold FlowTable.step
        rw [← RetainedPathFlow.find_value cs E T,hp]
      exact (table_run_fixed cs E T hs (k+1)).symm

/-- The same linear-in-budget upper bound is valid even when most fuel is
unvisited. It charges the actual successful steps and the first failed search. -/
theorem run_bound (E : ResidualSearch.Enumeration V)
    (T : FlowTable (CountedFlow.capacityOf cs) s t) (k : ℕ) :
    (run cs E T k).2 ≤
      k*(RetainedPathFlow.stepBound (Fintype.card V) T.cells.length cs.length+4)+1 := by
  induction k generalizing T with
  | zero => simp [run]
  | succ k ih =>
    have hf := RetainedPathFlow.find_bound cs E T
    simp only [run]
    split
    · rename_i p hp
      have hc : (RetainedPathFlow.find cs E T).edges = FlowTable.edgeList p := by
        simpa only [hp] using (RetainedPathFlow.find cs E T).correct
      let a := RetainedPathFlow.augmentWithEdges cs T p (RetainedPathFlow.find cs E T).edges hc
      have ha := RetainedPathFlow.augmentWithEdges_bound cs T p
        (RetainedPathFlow.find cs E T).edges hc
      have hi := ih a.1
      have hl : a.1.cells.length = T.cells.length := by
        simp only [a,RetainedPathFlow.augmentWithEdges_table,FlowTable.augment_length]
      rw [hl] at hi
      change _ ≤ (k+1)*(RetainedPathFlow.stepBound _ _ _+4)+1
      dsimp only [a] at hi
      unfold RetainedPathFlow.stepBound at hi ⊢
      nlinarith
    · dsimp only
      simp only [Nat.add_mul,Nat.one_mul]
      unfold RetainedPathFlow.stepBound
      omega

/-- One dense initial table, the early-stop loop, and the unchanged final cut. -/
def solve (E : ResidualSearch.Enumeration V) (s t : V) (k : ℕ) : CountedFlow.CutOutput V :=
  let initial := FlowTable.materialize E (Flow.zero (CountedFlow.capacityOf cs) s t)
  let r := run cs E initial k
  let cut := CountedFlow.finalCutWithCost cs E r.1
  { vertices := cut.vertices
    nodup := cut.nodup
    work := 16*initial.cells.length+8*E.vertices.length+8+r.2+cut.work }

theorem solve_vertices (E : ResidualSearch.Enumeration V) (s t : V) (k : ℕ) :
    (solve cs E s t k).vertices = (RetainedPathFlow.solve cs E s t k).vertices := by
  simp only [solve,RetainedPathFlow.solve,run_table,RetainedPathFlow.run_table]

theorem solve_value (E : ResidualSearch.Enumeration V) (s t : V) (k : ℕ) :
    (solve cs E s t k).asSet = finiteResidualCut E
      (IntegralNetworkFlow.run (finiteResidualSearch E (CountedFlow.capacityOf cs) s t)
        (Flow.zero (CountedFlow.capacityOf cs) s t) k) := by
  change (CountedFlow.finalCutWithCost cs E (run cs E
    (FlowTable.materialize E (Flow.zero (CountedFlow.capacityOf cs) s t)) k).1).asSet = _
  rw [CountedFlow.finalCutWithCost_value,run_table,FlowTable.run_refines,FlowTable.materialize_asFlow]

theorem solve_bound (E : ResidualSearch.Enumeration V) (s t : V) (k : ℕ) :
    (solve cs E s t k).work ≤ RetainedPathFlow.solveBound (Fintype.card V) cs.length k := by
  have hr := run_bound cs E (FlowTable.materialize E (Flow.zero (CountedFlow.capacityOf cs) s t)) k
  have hf := CountedFlow.finalCutWithCost_bound cs E
    (run cs E (FlowTable.materialize E (Flow.zero (CountedFlow.capacityOf cs) s t)) k).1
  have hi : (FlowTable.materialize E (Flow.zero (CountedFlow.capacityOf cs) s t)).cells.length =
      (Fintype.card V)^2 := FlowTable.dense_length E _
  have hl : (run cs E (FlowTable.materialize E (Flow.zero (CountedFlow.capacityOf cs) s t)) k).1.cells.length =
      (Fintype.card V)^2 := by rw [run_table,FlowTable.run_length,hi]
  rw [hi] at hr
  rw [hl] at hf
  simp only [solve,hi,E.length_eq_card]
  unfold RetainedPathFlow.solveBound
  omega

theorem solve_word_polynomial (E : ResidualSearch.Enumeration V) (s t : V) (k : ℕ)
    (hc : cs.length = (Fintype.card V)^2) :
    (solve cs E s t k).work ≤ 256*(k+1)*(Fintype.card V+1)^5 := by
  have h := solve_bound cs E s t k
  rw [hc] at h
  exact h.trans (RetainedPathFlow.solveBound_dense_polynomial _ _)

end DirectedFlowCutGap.IntegralNetworkFlow.Tabulated.EarlyStopRetainedFlow
