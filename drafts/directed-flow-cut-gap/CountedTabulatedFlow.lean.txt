import DirectedFlowCutGap.CountedResidualSearch
import DirectedFlowCutGap.ResidualPathRepresentation
import DirectedFlowCutGap.ClosureRuntime

/-!
# Counted search and augmentation over two retained integer tables

Capacities and flows are both read by the explicit linear lookup program.
Every executed residual test returns its decision and its lookup work together;
the counted search carries this work through its actual state-producing loops.
Path materialization is justified by the frozen search's proven representation,
not by an assumption about arbitrary function-valued simple paths.

The instruction model counts list cases/cells, word comparisons, conversions,
integer additions and subtractions. Counters are ghost annotations: this is
not a formal semantics of Lean's counter bookkeeping, compiler or allocator.
The Fintype and vertex enumeration dictionaries are retained input data; their
construction belongs to the caller, while algorithmic cardinality reads are
charged linearly. It treats fixed-arity encoded vertex comparisons as
word operations. Integer bit costs and concrete input-table construction must
be composed separately; this module does not claim a machine-code timing bound.
-/
namespace DirectedFlowCutGap.IntegralNetworkFlow.Tabulated.CountedFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A retained capacity lookup; missing cells mean zero capacity. -/
def capacityOf (cs : List ((V × V) × ℤ)) : Capacity V :=
  fun u v => (read (u,v) cs).1.toNat

variable (cs : List ((V × V) × ℤ)) {s t : V}

/-- The decision and cost are computed from the same two actual lookup results.
A cell inspection is charged for its list case, key test and branch. -/
def residualTest (T : FlowTable (capacityOf cs) s t) (u v : V) :
    Decidable (T.asFlow.residual.Adj u v) × ℕ :=
  let a := read (u,v) T.cells
  let b := read (u,v) cs
  let d : Decidable (a.1 < (b.1.toNat : ℤ)) := inferInstance
  (d, 8*(a.2+b.2)+8)

theorem residualTest_bound (T : FlowTable (capacityOf cs) s t) (u v : V) :
    (residualTest cs T u v).2 ≤ 8*(T.cells.length+cs.length)+8 := by
  have ha := read_count_le (u,v) T.cells
  have hb := read_count_le (u,v) cs
  simp only [residualTest]
  omega

def findWithCost (E : ResidualSearch.Enumeration V) (T : FlowTable (capacityOf cs) s t) :
    PathSearchResult T.asFlow × ℕ :=
  letI : DecidableRel T.asFlow.residual.Adj := fun u v =>
    inferInstanceAs (Decidable (T.asFlow.amount u v < (capacityOf cs u v : ℤ)))
  let r := CountedSearch.search E (residualTest cs T) s t
  ((match r.1 with
    | .found p => .found p
    | .stopped h => .stopped h), r.2)

theorem findWithCost_value (E : ResidualSearch.Enumeration V)
    (T : FlowTable (capacityOf cs) s t) :
    (findWithCost cs E T).1 = finiteResidualSearch E (capacityOf cs) s t T.asFlow := by
  let d₀ : DecidableRel T.asFlow.residual.Adj := fun u v =>
    inferInstanceAs (Decidable (T.asFlow.amount u v < (capacityOf cs u v : ℤ)))
  have hcanon (d : DecidableRel T.asFlow.residual.Adj) :
      (letI := d; ResidualSearch.search E T.asFlow.residual s t) =
        (letI := d₀; ResidualSearch.search E T.asFlow.residual s t) := by
    have hd : d=d₀ := Subsingleton.elim _ _
    cases hd
    rfl
  simp only [findWithCost, finiteResidualSearch, finiteResidualSearchWithCost,
    CountedSearch.search_value,hcanon]
  cases (ResidualSearch.search E T.asFlow.residual s t).1 <;> rfl

theorem findWithCost_bound (E : ResidualSearch.Enumeration V)
    (T : FlowTable (capacityOf cs) s t) :
    (findWithCost cs E T).2 ≤ CountedSearch.searchBound (Fintype.card V)
      (8*(T.cells.length+cs.length)+8) := by
  let : DecidableRel T.asFlow.residual.Adj := fun u v =>
    inferInstanceAs (Decidable (T.asFlow.amount u v < (capacityOf cs u v : ℤ)))
  exact CountedSearch.search_bound E (residualTest cs T) _ (residualTest_bound cs T) s t

/-- Coordinate materialization is legal for the exact found path because the
underlying frozen search only creates `refl`/`prepend` path programs. -/
theorem found_generated (E : ResidualSearch.Enumeration V)
    (T : FlowTable (capacityOf cs) s t) (p : SimplePath T.asFlow.residual s t)
    (hp : (findWithCost cs E T).1 = .found p) : PathRepresentation.Generated p := by
  let : DecidableRel T.asFlow.residual.Adj := fun u v =>
    inferInstanceAs (Decidable (T.asFlow.amount u v < (capacityOf cs u v : ℤ)))
  have hg := PathRepresentation.search_generated (G := T.asFlow.residual) E s t
  have hcast : (match (ResidualSearch.search E T.asFlow.residual s t).1 with
      | .found q => PathSearchResult.found q
      | .stopped hn => PathSearchResult.stopped hn) = (findWithCost cs E T).1 := by
    simp only [findWithCost,CountedSearch.search_value]
    congr 3
  have hp' := hcast.trans hp
  cases h : (ResidualSearch.search E T.asFlow.residual s t).1 with
  | found q =>
    have hq : q=p := PathSearchResult.found.inj (by simpa only [h] using hp')
    subst p
    simpa only [h] using hg
  | stopped hn => simp only [h] at hp'; cases hp'

/-- Updates charge signal scans, arithmetic, cell allocation and the now
certified functional-coordinate edge materialization. -/
def stepWithCost (E : ResidualSearch.Enumeration V) (T : FlowTable (capacityOf cs) s t) :
    FlowTable (capacityOf cs) s t × ℕ :=
  let r := findWithCost cs E T
  match r.1 with
  | .found p =>
    let a := T.augmentWithCost p
    (a.1,r.2+16*a.2+8*T.cells.length+8*PathRepresentation.edgeMaterializationCharge p+16)
  | .stopped _ => (T,r.2+4)

theorem stepWithCost_table (E : ResidualSearch.Enumeration V)
    (T : FlowTable (capacityOf cs) s t) :
    (stepWithCost cs E T).1 = T.step E := by
  unfold stepWithCost FlowTable.step
  dsimp only
  simp only [findWithCost_value]
  cases finiteResidualSearch E (capacityOf cs) s t T.asFlow <;> rfl

/-- This polynomial is derived from the two-table search and actual update
recurrences. `M` and `Q` are the retained list lengths, not cost assumptions. -/
def stepBound (N M Q : ℕ) : ℕ :=
  CountedSearch.searchBound N (8*(M+Q)+8) +
    16*(M*(2*N+2))+8*M+8*(N*(2*N+3))+16

theorem stepWithCost_bound (E : ResidualSearch.Enumeration V)
    (T : FlowTable (capacityOf cs) s t) :
    (stepWithCost cs E T).2 ≤ stepBound (Fintype.card V) T.cells.length cs.length := by
  have hs := findWithCost_bound cs E T
  unfold stepWithCost
  dsimp only
  split
  · rename_i p hp
    have hu := FlowTable.updateCells_count_le (FlowTable.edgeList p) T.cells
    rw [FlowTable.edgeList_length] at hu
    have hl := p.edgeLength_lt_card
    have hm := Nat.mul_le_mul_left T.cells.length
      (show 2*p.edgeLength+2 ≤ 2*Fintype.card V+2 by omega)
    have he := PathRepresentation.edgeMaterializationCharge_bound p
    change _ + 16*(FlowTable.updateCells (FlowTable.edgeList p) T.cells).2 + _ + _ + 16 ≤ _
    unfold stepBound
    omega
  · dsimp only
    unfold stepBound
    omega

def runWithCost (E : ResidualSearch.Enumeration V) (T : FlowTable (capacityOf cs) s t) :
    ℕ → FlowTable (capacityOf cs) s t × ℕ
  | 0 => (T,1)
  | k+1 =>
    let a := runWithCost E T k
    let b := stepWithCost cs E a.1
    (b.1,a.2+b.2+4)

theorem runWithCost_table (E : ResidualSearch.Enumeration V)
    (T : FlowTable (capacityOf cs) s t) (k : ℕ) :
    (runWithCost cs E T k).1 = FlowTable.run E T k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [runWithCost, stepWithCost_table, ih, FlowTable.run]

theorem runWithCost_bound (E : ResidualSearch.Enumeration V)
    (T : FlowTable (capacityOf cs) s t) (k : ℕ) :
    (runWithCost cs E T k).2 ≤
      k*(stepBound (Fintype.card V) T.cells.length cs.length+4)+1 := by
  induction k with
  | zero => simp [runWithCost]
  | succ k ih =>
    have hb := stepWithCost_bound cs E (runWithCost cs E T k).1
    have hl : (runWithCost cs E T k).1.cells.length = T.cells.length := by
      rw [runWithCost_table, FlowTable.run_length]
    rw [hl] at hb
    simp only [runWithCost, Nat.add_mul, Nat.one_mul]
    omega

/-- Dense capacities and dense flows make the entire augmentation stage
polynomial in vertex count and number of augmentations in the stated model. -/
theorem dense_run_bound (E : ResidualSearch.Enumeration V)
    (T : FlowTable (capacityOf cs) s t) (k : ℕ)
    (hT : T.cells.length = (Fintype.card V)^2) (hc : cs.length = (Fintype.card V)^2) :
    (runWithCost cs E T k).2 ≤
      k*(stepBound (Fintype.card V) ((Fintype.card V)^2) ((Fintype.card V)^2)+4)+1 := by
  simpa only [hT,hc] using runWithCost_bound cs E T k

/-- A retained duplicate-free cut list, suitable for one-pass core extraction. -/
structure CutOutput (V : Type*) where
  vertices : List V
  nodup : vertices.Nodup
  work : ℕ

def CutOutput.asSet (r : CutOutput V) : Finset V := ClosureRuntime.setOfNodup r.vertices r.nodup

omit [Fintype V] [DecidableEq V] in
@[simp] theorem CutOutput.mem_asSet (r : CutOutput V) (v : V) : v ∈ r.asSet ↔ v ∈ r.vertices :=
  ClosureRuntime.mem_setOfNodup _ _ _

/-- The final table search uses the same fully counted residual predicate.
The complement list is materialized once and retained with its uniqueness proof. -/
def finalCutWithCost (E : ResidualSearch.Enumeration V) (T : FlowTable (capacityOf cs) s t) :
    CutOutput V :=
  letI : DecidableRel T.asFlow.residual.Adj := fun u v =>
    inferInstanceAs (Decidable (T.asFlow.amount u v < (capacityOf cs u v : ℤ)))
  let a := CountedSearch.rounds (t := t) E (residualTest cs T) (Fintype.card V)
  let keys := a.1.entries.map Sigma.fst
  let b := ClosureRuntime.absentWithCost keys E.vertices
  { vertices := b.1
    nodup := by rw [ClosureRuntime.absentWithCost_value]; exact E.nodup.filter _
    work := a.2+8*keys.length+16*b.2+8*b.1.length+8+8*Fintype.card V+8 }

theorem finalCutWithCost_value (E : ResidualSearch.Enumeration V)
    (T : FlowTable (capacityOf cs) s t) :
    (finalCutWithCost cs E T).asSet = finiteResidualCut E T.asFlow := by
  let d₀ : DecidableRel T.asFlow.residual.Adj := fun u v =>
    inferInstanceAs (Decidable (T.asFlow.amount u v < (capacityOf cs u v : ℤ)))
  have hcanon (d : DecidableRel T.asFlow.residual.Adj) :
      (letI := d; ResidualSearch.rounds E.vertices T.asFlow.residual t (Fintype.card V)) =
        (letI := d₀; ResidualSearch.rounds E.vertices T.asFlow.residual t (Fintype.card V)) := by
    have hd : d=d₀ := Subsingleton.elim _ _
    cases hd
    rfl
  ext v
  simp only [CutOutput.mem_asSet,finalCutWithCost,
    ClosureRuntime.absentWithCost_value]
  simp [finiteResidualCut,ResidualSearch.separatingCut,ResidualSearch.keys,
    ResidualSearch.searchTable,E.complete]
  rw [CountedSearch.rounds_value]
  simp only [hcanon]

/-- Final search plus key-list materialization and the actual complement pass. -/
def finalCutBound (N M Q : ℕ) : ℕ :=
  N*(N*(CountedSearch.visitBound N (8*(M+Q)+8)+4)+5)+8 +
    8*N+16*(N*(N+1))+8*N+8+8*N+8

theorem finalCutWithCost_bound (E : ResidualSearch.Enumeration V)
    (T : FlowTable (capacityOf cs) s t) :
    (finalCutWithCost cs E T).work ≤ finalCutBound (Fintype.card V) T.cells.length cs.length := by
  let : DecidableRel T.asFlow.residual.Adj := fun u v =>
    inferInstanceAs (Decidable (T.asFlow.amount u v < (capacityOf cs u v : ℤ)))
  have hs := CountedSearch.rounds_bound (t := t) E (residualTest cs T)
    (8*(T.cells.length+cs.length)+8) (residualTest_bound cs T) (Fintype.card V)
  have hk := (CountedSearch.rounds (t := t) E (residualTest cs T) (Fintype.card V)).1.length_le_card
  have ha := ClosureRuntime.absentWithCost_bound
    ((CountedSearch.rounds (t := t) E (residualTest cs T) (Fintype.card V)).1.entries.map Sigma.fst)
    E.vertices
  rw [List.length_map,E.length_eq_card] at ha
  have hb : (ClosureRuntime.absentWithCost
      ((CountedSearch.rounds (t := t) E (residualTest cs T) (Fintype.card V)).1.entries.map Sigma.fst)
      E.vertices).1.length ≤ Fintype.card V := by
    rw [ClosureRuntime.absentWithCost_value,← E.length_eq_card]
    exact List.length_filter_le _ _
  have hm := Nat.mul_le_mul_left (Fintype.card V) (Nat.add_le_add_right hk 1)
  have h : (CountedSearch.rounds (t := t) E (residualTest cs T) (Fintype.card V)).2 +
      8*(CountedSearch.rounds (t := t) E (residualTest cs T) (Fintype.card V)).1.entries.length +
      16*(ClosureRuntime.absentWithCost
        ((CountedSearch.rounds (t := t) E (residualTest cs T) (Fintype.card V)).1.entries.map Sigma.fst)
        E.vertices).2 +
      8*(ClosureRuntime.absentWithCost
        ((CountedSearch.rounds (t := t) E (residualTest cs T) (Fintype.card V)).1.entries.map Sigma.fst)
        E.vertices).1.length + 8+8*Fintype.card V+8 ≤
      finalCutBound (Fintype.card V) T.cells.length cs.length := by
    unfold finalCutBound
    omega
  convert h using 1
  simp only [finalCutWithCost,List.length_map]

/-- Complete retained network solve, from zero-flow allocation through the
final cut list. Capacity construction and subsequent core/level decoding are
separate explicit callers, not callbacks hidden in this loop. -/
def solve (E : ResidualSearch.Enumeration V) (s t : V) (k : ℕ) : CutOutput V :=
  let initial := FlowTable.materialize E (Flow.zero (capacityOf cs) s t)
  let r := runWithCost cs E initial k
  let cut := finalCutWithCost cs E r.1
  { vertices := cut.vertices
    nodup := cut.nodup
    work := 16*initial.cells.length+8*E.vertices.length+8+r.2+cut.work }

theorem solve_value (E : ResidualSearch.Enumeration V) (s t : V) (k : ℕ) :
    (solve cs E s t k).asSet = finiteResidualCut E
      (IntegralNetworkFlow.run (finiteResidualSearch E (capacityOf cs) s t)
        (Flow.zero (capacityOf cs) s t) k) := by
  change (finalCutWithCost cs E (runWithCost cs E
    (FlowTable.materialize E (Flow.zero (capacityOf cs) s t)) k).1).asSet = _
  rw [finalCutWithCost_value,runWithCost_table,FlowTable.run_refines,FlowTable.materialize_asFlow]

def solveBound (N Q k : ℕ) : ℕ :=
  16*N^2+8*N+8 + k*(stepBound N (N^2) Q+4)+1 + finalCutBound N (N^2) Q

theorem solve_bound (E : ResidualSearch.Enumeration V) (s t : V) (k : ℕ) :
    (solve cs E s t k).work ≤ solveBound (Fintype.card V) cs.length k := by
  have hr := runWithCost_bound cs E
    (FlowTable.materialize E (Flow.zero (capacityOf cs) s t)) k
  have hf := finalCutWithCost_bound cs E (runWithCost cs E
    (FlowTable.materialize E (Flow.zero (capacityOf cs) s t)) k).1
  have hi : (FlowTable.materialize E (Flow.zero (capacityOf cs) s t)).cells.length =
      (Fintype.card V)^2 := FlowTable.dense_length E _
  have hl : (runWithCost cs E (FlowTable.materialize E (Flow.zero (capacityOf cs) s t)) k).1.cells.length =
      (Fintype.card V)^2 := by rw [runWithCost_table,FlowTable.run_length,hi]
  rw [hi] at hr
  rw [hl] at hf
  simp only [solve,hi,E.length_eq_card]
  unfold solveBound
  omega

/-- A fixed-degree word-instruction bound; the slack polynomial has only
nonnegative coefficients, so this does not presume the desired runtime bound. -/
theorem solveBound_dense_polynomial (N k : ℕ) :
    solveBound N (N^2) k ≤ 256*(k+1)*(N+1)^5 := by
  let slack := k*(240*N^5+1280*N^4+2503*N^3+2482*N^2+1234*N+215) +
    240*N^5+1280*N^4+2535*N^3+2506*N^2+1227*N+223
  calc
    _ ≤ solveBound N (N^2) k + slack := Nat.le_add_right _ _
    _ = _ := by unfold solveBound stepBound finalCutBound CountedSearch.searchBound CountedSearch.visitBound slack; ring

theorem solve_word_polynomial (E : ResidualSearch.Enumeration V) (s t : V) (k : ℕ)
    (hc : cs.length = (Fintype.card V)^2) :
    (solve cs E s t k).work ≤ 256*(k+1)*(Fintype.card V+1)^5 := by
  have h := solve_bound cs E s t k
  rw [hc] at h
  exact h.trans (solveBound_dense_polynomial _ _)

/-- The instrumented result counter itself also has a polynomial binary
encoding length; this does not identify word and bit operation counts. -/
theorem solve_counter_bits (E : ResidualSearch.Enumeration V) (s t : V) (k : ℕ)
    (hc : cs.length = (Fintype.card V)^2) :
    Nat.size (solve cs E s t k).work ≤ Nat.size (256*(k+1)*(Fintype.card V+1)^5) :=
  Nat.size_le_size (solve_word_polynomial cs E s t k hc)

/-- The sole pre-subtraction intermediate is at most one larger in magnitude
than a retained flow cell. This covers transient arithmetic as well as storage. -/
theorem update_intermediate_bits (T : FlowTable (capacityOf cs) s t)
    (C : ℕ) (hc : ∀ u v, capacityOf cs u v ≤ C)
    (e : V × V) (z : ℤ) (hz : (e,z) ∈ T.cells) (es : List (V × V)) :
    1+Nat.size (z+(FlowTable.signal es e).1).natAbs ≤ 1+Nat.size (C+1) := by
  have hz' := T.cell_natAbs_le C hc e z hz
  have hs : (FlowTable.signal es e).1.natAbs ≤ 1 := by
    rw [FlowTable.signal_value]
    split <;> simp
  have ha := Int.natAbs_add_le z (FlowTable.signal es e).1
  have hb : (z+(FlowTable.signal es e).1).natAbs ≤ C+1 := by omega
  exact Nat.add_le_add_left (Nat.size_le_size hb) 1

end DirectedFlowCutGap.IntegralNetworkFlow.Tabulated.CountedFlow
