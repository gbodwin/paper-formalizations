import LightEFTSpanners.StoredComponentDiscovery

namespace LightEFTSpanners.StoredZeroWeights
open Controller
inductive State where
  | row : ℕ → List ℚ → State
  | rows : ℕ → List ℚ → StoredRecords.Weights → State
  | halt : StoredRecords.Weights → State
  deriving DecidableEq, Repr

def transition (n : ℕ) : State → Option State
  | .row 0 acc => some (.rows n acc [])
  | .row (k+1) acc => some (.row k (0::acc))
  | .rows 0 _ acc => some (.halt acc)
  | .rows (k+1) row acc => some (.rows k row (row::acc))
  | .halt _ => none

theorem row_trace (n k : ℕ) (acc : List ℚ) :
    Trace (transition n) (k+1) (.row k acc) (.rows n (List.replicate k 0++acc) []) := by
  induction k generalizing acc with
  | zero => exact Trace.one rfl
  | succ k ih =>
    simpa [List.replicate_succ',List.append_assoc,Nat.add_assoc] using
      Trace.cons (show transition n (.row (k+1) acc)=some (.row k (0::acc)) from rfl) (ih (0::acc))

theorem rows_trace (n k : ℕ) (row : List ℚ) (acc : StoredRecords.Weights) :
    Trace (transition n) (k+1) (.rows k row acc) (.halt (List.replicate k row++acc)) := by
  induction k generalizing acc with
  | zero => exact Trace.one rfl
  | succ k ih =>
    simpa [List.replicate_succ',List.append_assoc,Nat.add_assoc] using
      Trace.cons (show transition n (.rows (k+1) row acc)=some (.rows k row (row::acc)) from rfl)
        (ih (row::acc))

def matrix (n : ℕ) : StoredRecords.Weights := List.replicate n (List.replicate n 0)

theorem construct_trace (n : ℕ) :
    Trace (transition n) (2*n+2) (.row n []) (.halt (matrix n)) := by
  have a := row_trace n n []
  have b := rows_trace n n (List.replicate n 0) []
  simp only [List.append_nil] at a b
  simpa [matrix,Nat.two_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using a.trans b

theorem matrix_encode (n : ℕ) : matrix n=StoredRecords.encodeWeights (fun _ : Sym2 (Fin n) => 0) := by
  simp [matrix,StoredRecords.encodeWeights]
end LightEFTSpanners.StoredZeroWeights
