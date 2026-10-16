import LightEFTSpanners.StoredPreparedHostOriginal

/-! Literal two-stage traversal of the original stored rational weight matrix.
A matrix access is not one oracle step: each skipped row/cell is charged. -/
namespace LightEFTSpanners.StoredWeightLookup
open Controller
inductive State where
  | rows : ℕ → ℕ → StoredRecords.Weights → State
  | cells : ℕ → List ℚ → State
  | halt : ℚ → State
  deriving DecidableEq, Repr

def transition : State → Option State
  | .rows _ _ [] => some (.halt 0)
  | .rows 0 j (row::_) => some (.cells j row)
  | .rows (i+1) j (_::rest) => some (.rows i j rest)
  | .cells _ [] => some (.halt 0)
  | .cells 0 (w::_) => some (.halt w)
  | .cells (j+1) (_::rest) => some (.cells j rest)
  | .halt _ => none

def rowValue : ℕ → List ℚ → ℚ :=
  fun j row => List.rec (motive := fun _ => ℕ → ℚ) (fun _ => 0)
    (fun w _ next i => match i with | 0 => w | k+1 => next k) row j

theorem rowValue_nil (j : ℕ) : rowValue j [] = 0 := rfl

theorem rowValue_cons_zero (w : ℚ) (ws : List ℚ) : rowValue 0 (w::ws) = w := rfl

theorem rowValue_cons_succ (j : ℕ) (w : ℚ) (ws : List ℚ) :
    rowValue (j+1) (w::ws) = rowValue j ws := rfl

def value : ℕ → ℕ → StoredRecords.Weights → ℚ :=
  fun i j W => List.rec (motive := fun _ => ℕ → ℚ) (fun _ => 0)
    (fun row _ next k => match k with | 0 => rowValue j row | k+1 => next k) W i

theorem value_nil (i j : ℕ) : value i j [] = 0 := rfl

theorem value_cons_zero (j : ℕ) (row : List ℚ) (rows : StoredRecords.Weights) :
    value 0 j (row::rows) = rowValue j row := rfl

theorem value_cons_succ (i j : ℕ) (row : List ℚ) (rows : StoredRecords.Weights) :
    value (i+1) j (row::rows) = value i j rows := rfl

def rowSteps : ℕ → List ℚ → ℕ
  | _,[] => 1
  | 0,_::_ => 1
  | j+1,_::ws => rowSteps j ws+1

def steps : ℕ → ℕ → StoredRecords.Weights → ℕ
  | _,_,[] => 1
  | 0,j,row::_ => rowSteps j row+1
  | i+1,j,_::rows => steps i j rows+1

theorem row_trace (j : ℕ) (row : List ℚ) :
    Trace transition (rowSteps j row) (.cells j row) (.halt (rowValue j row)) := by
  induction row generalizing j with
  | nil => cases j <;> exact Trace.one rfl
  | cons w ws ih =>
    cases j with
    | zero => exact Trace.one rfl
    | succ j => simpa [rowSteps,rowValue_cons_succ] using
        Trace.cons (show transition (.cells (j+1) (w::ws))=some (.cells j ws) from rfl) (ih j)

theorem lookup_trace (i j : ℕ) (W : StoredRecords.Weights) :
    Trace transition (steps i j W) (.rows i j W) (.halt (value i j W)) := by
  induction W generalizing i with
  | nil => cases i <;> exact Trace.one rfl
  | cons row rows ih =>
    cases i with
    | zero => simpa [steps,value_cons_zero] using
        Trace.cons (show transition (.rows 0 j (row::rows))=some (.cells j row) from rfl) (row_trace j row)
    | succ i => simpa [steps,value_cons_succ] using
        Trace.cons (show transition (.rows (i+1) j (row::rows))=some (.rows i j rows) from rfl) (ih i)

theorem rowSteps_le (j : ℕ) (row : List ℚ) : rowSteps j row ≤ j+1 := by
  induction row generalizing j with
  | nil => simp [rowSteps]
  | cons w ws ih =>
    cases j with
    | zero => simp [rowSteps]
    | succ j => have h := ih j; simp [rowSteps];omega

theorem steps_le (i j : ℕ) (W : StoredRecords.Weights) : steps i j W ≤ i+j+2 := by
  induction W generalizing i with
  | nil => simp [steps]
  | cons row rows ih =>
    cases i with
    | zero => have h := rowSteps_le j row; simp [steps];omega
    | succ i => have h := ih i; simp [steps];omega

theorem rowValue_eq (j : ℕ) (row : List ℚ) : rowValue j row=(row[j]?).getD 0 := by
  induction row generalizing j with
  | nil => simp [rowValue_nil]
  | cons w ws ih => cases j <;> simp [rowValue_cons_zero,rowValue_cons_succ,ih]

theorem value_eq (i j : ℕ) (W : StoredRecords.Weights) :
    value i j W=(((W[i]?).getD [])[j]?).getD 0 := by
  induction W generalizing i with
  | nil => simp [value_nil]
  | cons row rows ih => cases i <;> simp [value_cons_zero,value_cons_succ,rowValue_eq,ih]

theorem value_encoded {n : ℕ} (w : Sym2 (Fin n) → ℚ) (u v : Fin n) :
    value u.val v.val (StoredRecords.encodeWeights w)=w s(u,v) := by
  simp [value_eq,StoredRecords.encodeWeights]
end LightEFTSpanners.StoredWeightLookup
