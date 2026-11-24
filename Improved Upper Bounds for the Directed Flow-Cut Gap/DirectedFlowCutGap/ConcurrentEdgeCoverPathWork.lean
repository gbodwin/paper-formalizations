import DirectedFlowCutGap.ConcurrentEdgeOracleWork

/-! Run the original joint covering recurrence while retaining the exact
charges from the binary shortest-path calls that it reaches. The
arithmetic and the selection of the bottleneck are separate work. -/
namespace DirectedFlowCutGap.ConcurrentEdgeCoverPathWork

open scoped BigOperators
open BinaryFractionalWalkOracle (Adjacency)
open RationalEdgeThresholds (Weights)
open ConcurrentEdgeOracle (Edge column pivot oracle encoded)
open ConcurrentEdgeCover (priceRow)
open ConcurrentEdgeCoverWidths (MatrixFits encoded_fits)
open ConcurrentEdgeOracleWork (measuredPaths)
open FractionalCover (Row value value_ofFn initial objective fuel)
open MultiplicityCover (Choice State)
open MultiplicityCoverWidths (RowFits weightWidth)
open BinaryFractionalWalkBounds (shortestBound)

variable {m n : ℕ}

def choice (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m)
    (c y : Row (n*n)) : Choice (n*n) × ℕ :=
  let read := measuredPaths A P y
  let q := column read.1
  (⟨q,pivot hn c q⟩,read.2)

theorem choice_value (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m) (c y : Row (n*n)) :
    (choice hn A P c y).1 = oracle hn A P c y := by
  dsimp only [choice,oracle]
  rw [ConcurrentEdgeOracleWork.paths_eq]

theorem choice_charge (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m) (c y : Row (n*n))
    {W : ℕ} (fit : RowFits y W) : (choice hn A P c y).2 ≤ m*shortestBound n (W+1) 2 :=
  ConcurrentEdgeOracleWork.charge_le A P y fit

def start (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m)
    (c : Row (n*n)) : State (n*n) × ℕ :=
  let read := choice hn A P c (initial c)
  (MultiplicityCover.start c (fun _ => read.1),read.2)

def advance (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m)
    (c : Row (n*n)) (s : State (n*n)) : State (n*n) × ℕ :=
  if 1 ≤ objective c s.weights then (s,0) else
    let read := choice hn A P c s.weights
    (MultiplicityCover.step c (fun _ => read.1) s,read.2)

theorem advance_value (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m)
    (c : Row (n*n)) (s : State (n*n)) :
    (advance hn A P c s).1 = MultiplicityCover.step c (oracle hn A P c) s := by
  by_cases stop : 1 ≤ objective c s.weights
  · simp only [advance,MultiplicityCover.step,ite_eq_left stop]
  · simp only [advance,MultiplicityCover.step,ite_eq_right stop,choice_value]

theorem advance_charge (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m)
    (c : Row (n*n)) (s : State (n*n)) {W : ℕ} (fit : RowFits s.weights W) :
    (advance hn A P c s).2 ≤ m*shortestBound n (W+1) 2 := by
  unfold advance
  split
  · exact Nat.zero_le _
  · exact choice_charge hn A P c s.weights fit

def run (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m) (c : Row (n*n)) :
    ℕ → State (n*n) × ℕ
  | 0 => start hn A P c
  | k+1 =>
    let prev := run hn A P c k
    let next := advance hn A P c prev.1
    (next.1,prev.2+next.2)

theorem run_value (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m) (c : Row (n*n)) (k : ℕ) :
    (run hn A P c k).1 = MultiplicityCover.run c (oracle hn A P c) k := by
  induction k with
  | zero =>
    simp only [run,start,MultiplicityCover.run,MultiplicityCover.start,choice_value]
  | succ k ih =>
    simp only [run,MultiplicityCover.run,advance_value,ih]

theorem run_charge (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m)
    (c : Row (n*n)) {B : ℕ} (fit : RowFits c B) {t k : ℕ} (steps : k ≤ t) :
    (run hn A P c k).2 ≤ (k+1)*(m*shortestBound n (weightWidth (n*n) B m t+1) 2) := by
  let W := weightWidth (n*n) B m t
  let bound := m*shortestBound n (W+1) 2
  have initialFit : RowFits (initial c) W := by
    intro i
    apply MultiplicityCoverWidths.fits_mono (MultiplicityCoverWidths.initial_fits c fit i)
    unfold W weightWidth
    simp
  induction k with
  | zero =>
    simpa only [run,start,Nat.zero_add,Nat.one_mul,bound] using
      choice_charge hn A P c (initial c) initialFit
  | succ k ih =>
    let prev := run hn A P c k
    have costPrev : prev.2 ≤ (k+1)*bound := ih (Nat.le_of_succ_le steps)
    have old := (MultiplicityCoverWidths.run_fits c (oracle hn A P c) fit
      (ConcurrentEdgeCoverWidths.oracle_columns hn A P c) k).weights
    have shape : RowFits prev.1.weights W := by
      change RowFits (run hn A P c k).1.weights W
      rw [run_value]
      intro i
      apply MultiplicityCoverWidths.fits_mono (old i)
      unfold W weightWidth
      gcongr
      exact Nat.le_of_succ_le steps
    have costNext : (advance hn A P c prev.1).2 ≤ bound := advance_charge hn A P c _ shape
    change prev.2+(advance hn A P c prev.1).2 ≤ (k+1+1)*bound
    rw [Nat.add_mul,Nat.one_mul]
    exact Nat.add_le_add costPrev costNext

def solve (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) : Weights n × ℕ :=
  let result := run hn A P (priceRow A c) (fuel (n*n))
  (encoded (Vector.ofFn fun i => (m : ℚ) * value result.1.best i),result.2)

theorem solve_value (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    (solve hn A c P).1 = ConcurrentEdgeCover.solve hn A c P := by
  simp only [solve,run_value,ConcurrentEdgeCover.solve,ConcurrentEdgeCover.base,MultiplicityCover.solve]

def searchBound (n m B : ℕ) : ℕ :=
  (3*(n*n)^2+1)*(m*shortestBound n (weightWidth (n*n) B m (3*(n*n)^2)+1) 2)

theorem solve_charge (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    {B : ℕ} (fit : MatrixFits c B) : (solve hn A c P).2 ≤ searchBound n m B :=
  run_charge hn A P (priceRow A c) (ConcurrentEdgeCoverWidths.priceRow_fits A c fit) le_rfl

end DirectedFlowCutGap.ConcurrentEdgeCoverPathWork
