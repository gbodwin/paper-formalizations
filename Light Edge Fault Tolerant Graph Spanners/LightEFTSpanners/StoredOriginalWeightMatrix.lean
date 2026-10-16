import LightEFTSpanners.StoredOriginalWeightEncoding

namespace LightEFTSpanners.StoredOriginalWeightMatrix
open Controller
inductive State where
  | rows : ℕ → ℕ → StoredRecords.Weights → State
  | cells : ℕ → ℕ → ℕ → ℕ → List ℚ → StoredRecords.Weights → State
  | lookup : ℕ → ℕ → ℕ → ℕ → List ℚ → StoredRecords.Weights → StoredOriginalWeightLookup.State → State
  | reverseRow : ℕ → ℕ → List ℚ → List ℚ → StoredRecords.Weights → State
  | reverse : StoredRecords.Weights → StoredRecords.Weights → State
  | halt : StoredRecords.Weights → State
  deriving DecidableEq, Repr

def transition (n : ℕ) (bank : StoredOriginalWeightLookup.Bank) : State → Option State
  | .rows _ 0 acc => some (.reverse acc [])
  | .rows i (k+1) acc => some (.cells i 0 n k [] acc)
  | .cells i _ 0 k row acc => some (.reverseRow i k row [] acc)
  | .cells i j (l+1) k row acc => some (.lookup i j l k row acc (.scan bank))
  | .lookup i j l k row acc (.halt c) => some (.cells i (j+1) l k (c::row) acc)
  | .lookup i j l k row acc s => (StoredOriginalWeightLookup.transition (i,j) s).map (.lookup i j l k row acc)
  | .reverseRow i k [] row acc => some (.rows (i+1) k (row::acc))
  | .reverseRow i k (c::cs) row acc => some (.reverseRow i k cs (c::row) acc)
  | .reverse [] out => some (.halt out)
  | .reverse (row::rows) out => some (.reverse rows (row::out))
  | .halt _ => none

def row (bank : StoredOriginalWeightLookup.Bank) (i : ℕ) : ℕ → ℕ → List ℚ :=
  fun j k => Nat.rec (motive := fun _ => ℕ → List ℚ) (fun _ => [])
    (fun _ next col => StoredOriginalWeightLookup.value (i,col) bank::next (col+1)) k j

theorem row_zero (bank : StoredOriginalWeightLookup.Bank) (i j : ℕ) :
    row bank i j 0 = [] := rfl

theorem row_succ (bank : StoredOriginalWeightLookup.Bank) (i j k : ℕ) :
    row bank i j (k+1) = StoredOriginalWeightLookup.value (i,j) bank::row bank i (j+1) k := rfl


def rows (bank : StoredOriginalWeightLookup.Bank) (n : ℕ) : ℕ → ℕ → StoredRecords.Weights
  | _,0 => []
  | i,k+1 => row bank i 0 n::rows bank n (i+1) k

theorem row_length (bank : StoredOriginalWeightLookup.Bank) (i j k : ℕ) : (row bank i j k).length=k := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih => simp [row_succ,ih]

theorem rows_length (bank : StoredOriginalWeightLookup.Bank) (n i k : ℕ) : (rows bank n i k).length=k := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp [rows,ih]
end LightEFTSpanners.StoredOriginalWeightMatrix
