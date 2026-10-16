import LightEFTSpanners.SampleRecordMatrix

/-! Materialize a clipped sample matrix by literal record scans and reversals.
No transition performs membership search, hidden list traversal or allocation
of an entire row. Single cons cells and natural/rational registers are atoms. -/
namespace LightEFTSpanners.SampleRecords
open LinkedDistance Controller
inductive State where
  | row : ℕ → Records → Matrix → State
  | cell : ℕ → ℕ → List Entry → List Cell → Records → Matrix → State
  | revRow : ℕ → Records → Matrix → List Cell → List Cell → State
  | revMatrix : Matrix → Matrix → State
  | halt : Matrix → State
  deriving DecidableEq, Repr
 def transition : State → Option State
  | .row _ [] out => some (.revMatrix out [])
  | .row i (r::rs) out => some (.cell i 0 r [] rs out)
  | .cell i _ [] acc rs out => some (.revRow i rs out acc [])
  | .cell i j (a::as) acc rs out => some (.cell i (j+1) as (value i j a::acc) rs out)
  | .revRow i rs out [] row => some (.row (i+1) rs (row::out))
  | .revRow i rs out (x::xs) row => some (.revRow i rs out xs (x::row))
  | .revMatrix [] out => some (.halt out)
  | .revMatrix (r::rs) out => some (.revMatrix rs (r::out))
  | .halt _ => none
 theorem cell_trace (i j : ℕ) (r : List Entry) (acc : List Cell) (rs : Records) (out : Matrix) :
    Trace transition (r.length+1) (.cell i j r acc rs out)
      (.revRow i rs out ((rowValues i j r).reverse++acc) []) := by
  induction r generalizing j acc with
  | nil => exact Trace.one rfl
  | cons a as ih =>
    simpa [rowValues,List.reverse_cons,List.append_assoc] using
      Trace.cons (show transition (.cell i j (a::as) acc rs out)=
        some (.cell i (j+1) as (value i j a::acc) rs out) from rfl) (ih (j+1) (value i j a::acc))
 theorem reverse_row_trace (i : ℕ) (rs : Records) (out : Matrix) (r acc : List Cell) :
    Trace transition (r.length+1) (.revRow i rs out r acc)
      (.row (i+1) rs ((r.reverse++acc)::out)) := by
  induction r generalizing acc with
  | nil => exact Trace.one rfl
  | cons a as ih =>
    simpa [List.reverse_cons,List.append_assoc] using
      Trace.cons (show transition (.revRow i rs out (a::as) acc)=
        some (.revRow i rs out as (a::acc)) from rfl) (ih (a::acc))
 theorem reverse_matrix_trace (R acc : Matrix) :
    Trace transition (R.length+1) (.revMatrix R acc) (.halt (R.reverse++acc)) := by
  induction R generalizing acc with
  | nil => exact Trace.one rfl
  | cons a as ih =>
    simpa [List.reverse_cons,List.append_assoc] using
      Trace.cons (show transition (.revMatrix (a::as) acc)=some (.revMatrix as (a::acc)) from rfl)
        (ih (a::acc))
end LightEFTSpanners.SampleRecords
