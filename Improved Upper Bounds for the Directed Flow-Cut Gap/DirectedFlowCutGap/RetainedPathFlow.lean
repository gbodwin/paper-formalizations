import DirectedFlowCutGap.RetainedPathSearch
import DirectedFlowCutGap.CountedTabulatedFlow

/-!
# Execution-linked augmentation from retained path edge lists

This backend feeds the edge list produced by RetainedPathSearch directly to
`updateCells`. The mathematical SimplePath is used only to certify that list
and establish exact refinement. There is no executable `p.vertex`, `p.edgeAt`
or `edgeList p` call in the augmentation loop. This removes the coordinate
representation interpretation required by the earlier counted backend.
-/
namespace DirectedFlowCutGap.IntegralNetworkFlow.Tabulated.RetainedPathFlow

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (cs : List ((V × V) × ℤ)) {s t : V}

structure SearchOutput (f : Flow (CountedFlow.capacityOf cs) s t) where
  result : PathSearchResult f
  edges : List (V × V)
  correct : match result with
    | .found p => edges = FlowTable.edgeList p
    | .stopped _ => edges = []
  work : ℕ

def find (E : ResidualSearch.Enumeration V) (T : FlowTable (CountedFlow.capacityOf cs) s t) :
    SearchOutput cs T.asFlow :=
  letI : DecidableRel T.asFlow.residual.Adj := fun u v =>
    inferInstanceAs (Decidable (T.asFlow.amount u v < (CountedFlow.capacityOf cs u v : ℤ)))
  let r := RetainedPathSearch.search E (CountedFlow.residualTest cs T) s t
  { result := match r.result with
      | .found p => .found p
      | .stopped h => .stopped h
    edges := r.edges
    correct := by cases hr : r.result <;> simpa only [hr] using r.correct
    work := r.work }

theorem find_value (E : ResidualSearch.Enumeration V)
    (T : FlowTable (CountedFlow.capacityOf cs) s t) :
    (find cs E T).result = finiteResidualSearch E (CountedFlow.capacityOf cs) s t T.asFlow := by
  let d₀ : DecidableRel T.asFlow.residual.Adj := fun u v =>
    inferInstanceAs (Decidable (T.asFlow.amount u v < (CountedFlow.capacityOf cs u v : ℤ)))
  have hcanon (d : DecidableRel T.asFlow.residual.Adj) :
      (letI := d; ResidualSearch.search E T.asFlow.residual s t) =
        (letI := d₀; ResidualSearch.search E T.asFlow.residual s t) := by
    have hd : d=d₀ := Subsingleton.elim _ _
    cases hd
    rfl
  simp only [find,finiteResidualSearch,finiteResidualSearchWithCost,
    RetainedPathSearch.search_result,hcanon]
  cases (ResidualSearch.search E T.asFlow.residual s t).1 <;> rfl

theorem find_bound (E : ResidualSearch.Enumeration V)
    (T : FlowTable (CountedFlow.capacityOf cs) s t) :
    (find cs E T).work ≤ RetainedPathSearch.searchBound (Fintype.card V)
      (8*(T.cells.length+cs.length)+8) := by
  let : DecidableRel T.asFlow.residual.Adj := fun u v =>
    inferInstanceAs (Decidable (T.asFlow.amount u v < (CountedFlow.capacityOf cs u v : ℤ)))
  exact RetainedPathSearch.search_bound E (CountedFlow.residualTest cs T) _
    (CountedFlow.residualTest_bound cs T) s t

/-- Only `es` is read by the executable update. All mentions of the frozen
path edge list are inside proof fields that disappear on extraction. -/
def augmentWithEdges (T : FlowTable (CountedFlow.capacityOf cs) s t)
    (p : SimplePath T.asFlow.residual s t) (es : List (V × V))
    (hes : es = FlowTable.edgeList p) : FlowTable (CountedFlow.capacityOf cs) s t × ℕ :=
  let a := FlowTable.updateCells es T.cells
  ({ cells := a.1
     complete := by subst es; exact (T.augment p).complete
     coherent := by subst es; exact (T.augment p).coherent
     antisymm := by subst es; exact (T.augment p).antisymm
     upper := by subst es; exact (T.augment p).upper
     conserve := by subst es; exact (T.augment p).conserve },a.2)

@[simp] theorem augmentWithEdges_table (T : FlowTable (CountedFlow.capacityOf cs) s t)
    (p : SimplePath T.asFlow.residual s t) (es : List (V × V))
    (hes : es = FlowTable.edgeList p) :
    (augmentWithEdges cs T p es hes).1 = T.augment p := by
  subst es
  rfl

theorem augmentWithEdges_bound (T : FlowTable (CountedFlow.capacityOf cs) s t)
    (p : SimplePath T.asFlow.residual s t) (es : List (V × V))
    (hes : es = FlowTable.edgeList p) :
    (augmentWithEdges cs T p es hes).2 ≤ T.cells.length*(2*Fintype.card V+2) := by
  have h := FlowTable.updateCells_count_le es T.cells
  have hl : es.length < Fintype.card V := by rw [hes,FlowTable.edgeList_length]; exact p.edgeLength_lt_card
  have hm := Nat.mul_le_mul_left T.cells.length
    (show 2*es.length+2 ≤ 2*Fintype.card V+2 by omega)
  exact h.trans hm

def step (E : ResidualSearch.Enumeration V) (T : FlowTable (CountedFlow.capacityOf cs) s t) :
    FlowTable (CountedFlow.capacityOf cs) s t × ℕ :=
  let r := find cs E T
  match hr : r.result with
  | .found p =>
    let a := augmentWithEdges cs T p r.edges (by simpa only [hr] using r.correct)
    (a.1,r.work+16*a.2+8*T.cells.length+16)
  | .stopped _ => (T,r.work+4)

theorem step_table (E : ResidualSearch.Enumeration V)
    (T : FlowTable (CountedFlow.capacityOf cs) s t) :
    (step cs E T).1 = T.step E := by
  unfold step FlowTable.step
  dsimp only
  split
  · rename_i p hp
    rw [augmentWithEdges_table]
    have h := (find_value cs E T).symm.trans hp
    split
    · rename_i q hq
      have heq : p=q := PathSearchResult.found.inj (h.symm.trans hq)
      subst q
      rfl
    · rename_i hn
      have hbad := h.symm.trans hn
      cases hbad
  · rename_i hp
    have h := (find_value cs E T).symm.trans hp
    split
    · rename_i p hq
      have hbad := h.symm.trans hq
      cases hbad
    · rfl

def stepBound (N M Q : ℕ) : ℕ :=
  RetainedPathSearch.searchBound N (8*(M+Q)+8) + 16*(M*(2*N+2))+8*M+16

theorem step_bound (E : ResidualSearch.Enumeration V)
    (T : FlowTable (CountedFlow.capacityOf cs) s t) :
    (step cs E T).2 ≤ stepBound (Fintype.card V) T.cells.length cs.length := by
  have hs := find_bound cs E T
  unfold step
  dsimp only
  split
  · rename_i p hp
    have hc : (find cs E T).edges = FlowTable.edgeList p := by
      simpa only [hp] using (find cs E T).correct
    have ha := augmentWithEdges_bound cs T p (find cs E T).edges hc
    dsimp only
    unfold stepBound
    omega
  · dsimp only
    unfold stepBound
    omega

def run (E : ResidualSearch.Enumeration V) (T : FlowTable (CountedFlow.capacityOf cs) s t) :
    ℕ → FlowTable (CountedFlow.capacityOf cs) s t × ℕ
  | 0 => (T,1)
  | k+1 =>
    let a := run E T k
    let b := step cs E a.1
    (b.1,a.2+b.2+4)

theorem run_table (E : ResidualSearch.Enumeration V)
    (T : FlowTable (CountedFlow.capacityOf cs) s t) (k : ℕ) :
    (run cs E T k).1 = FlowTable.run E T k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [run,step_table,ih,FlowTable.run]

theorem run_bound (E : ResidualSearch.Enumeration V)
    (T : FlowTable (CountedFlow.capacityOf cs) s t) (k : ℕ) :
    (run cs E T k).2 ≤ k*(stepBound (Fintype.card V) T.cells.length cs.length+4)+1 := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
    have hb := step_bound cs E (run cs E T k).1
    have hl : (run cs E T k).1.cells.length = T.cells.length := by rw [run_table,FlowTable.run_length]
    rw [hl] at hb
    simp only [run,Nat.add_mul,Nat.one_mul]
    omega

/-- The final cut routine uses root keys only, so its fully counted search
already requires no path-coordinate evaluation. Its retained list is reused. -/
def solve (E : ResidualSearch.Enumeration V) (s t : V) (k : ℕ) : CountedFlow.CutOutput V :=
  let initial := FlowTable.materialize E (Flow.zero (CountedFlow.capacityOf cs) s t)
  let r := run cs E initial k
  let cut := CountedFlow.finalCutWithCost cs E r.1
  { vertices := cut.vertices
    nodup := cut.nodup
    work := 16*initial.cells.length+8*E.vertices.length+8+r.2+cut.work }

/-- The retained backend preserves even the ordered cut list of the earlier
counted solver, so callers may reuse its decoding without an order argument. -/
theorem solve_vertices (E : ResidualSearch.Enumeration V) (s t : V) (k : ℕ) :
    (solve cs E s t k).vertices = (CountedFlow.solve cs E s t k).vertices := by
  simp only [solve,CountedFlow.solve,run_table,CountedFlow.runWithCost_table]

theorem solve_value (E : ResidualSearch.Enumeration V) (s t : V) (k : ℕ) :
    (solve cs E s t k).asSet = finiteResidualCut E
      (IntegralNetworkFlow.run (finiteResidualSearch E (CountedFlow.capacityOf cs) s t)
        (Flow.zero (CountedFlow.capacityOf cs) s t) k) := by
  change (CountedFlow.finalCutWithCost cs E (run cs E
    (FlowTable.materialize E (Flow.zero (CountedFlow.capacityOf cs) s t)) k).1).asSet = _
  rw [CountedFlow.finalCutWithCost_value,run_table,FlowTable.run_refines,FlowTable.materialize_asFlow]

def solveBound (N Q k : ℕ) : ℕ :=
  16*N^2+8*N+8 + k*(stepBound N (N^2) Q+4)+1 + CountedFlow.finalCutBound N (N^2) Q

theorem solve_bound (E : ResidualSearch.Enumeration V) (s t : V) (k : ℕ) :
    (solve cs E s t k).work ≤ solveBound (Fintype.card V) cs.length k := by
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
  unfold solveBound
  omega

theorem solveBound_dense_polynomial (N k : ℕ) : solveBound N (N^2) k ≤ 256*(k+1)*(N+1)^5 := by
  let slack := k*(240*N^5+1280*N^4+2488*N^3+2484*N^2+1250*N+199) +
    240*N^5+1280*N^4+2535*N^3+2506*N^2+1227*N+223
  calc
    _ ≤ solveBound N (N^2) k+slack := Nat.le_add_right _ _
    _ = _ := by
      unfold solveBound stepBound RetainedPathSearch.searchBound RetainedPathSearch.visitBound
        CountedFlow.finalCutBound CountedSearch.visitBound slack
      ring

theorem solve_word_polynomial (E : ResidualSearch.Enumeration V) (s t : V) (k : ℕ)
    (hc : cs.length = (Fintype.card V)^2) :
    (solve cs E s t k).work ≤ 256*(k+1)*(Fintype.card V+1)^5 := by
  have h := solve_bound cs E s t k
  rw [hc] at h
  exact h.trans (solveBound_dense_polynomial _ _)

/-- The returned ghost counter also has a bounded binary representation. -/
theorem solve_counter_bits (E : ResidualSearch.Enumeration V) (s t : V) (k : ℕ)
    (hc : cs.length = (Fintype.card V)^2) :
    Nat.size (solve cs E s t k).work ≤ Nat.size (256*(k+1)*(Fintype.card V+1)^5) :=
  Nat.size_le_size (solve_word_polynomial cs E s t k hc)

end DirectedFlowCutGap.IntegralNetworkFlow.Tabulated.RetainedPathFlow
