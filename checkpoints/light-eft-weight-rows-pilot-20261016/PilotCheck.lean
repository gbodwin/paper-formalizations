import LightEFTSpanners.StoredOriginalWeightMatrix
open LightEFTSpanners
open StoredOriginalWeightMatrix
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredOriginalWeightMatrix.rows
  let some c := env.find? name | throwError "rows missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "rows not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `Nat.rec do throwError "Nat.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: rows safe, total, computable, explicit Nat.rec, no partial companion"
example (bank : StoredOriginalWeightLookup.Bank) (n i : ℕ) : rows bank n i 0 = [] := rfl
example (bank : StoredOriginalWeightLookup.Bank) (n i k : ℕ) :
    rows bank n i (k+1) = row bank i 0 n::rows bank n (i+1) k := rfl
private def bank : StoredOriginalWeightLookup.Bank :=
  [((0,0),1),((0,1),2),((2,0),-3/2),((1,1),-4),((1,2),5/3),((2,2),0),((0,1),99)]
#eval do
  let checks := [
    decide (rows [] 0 0 0 = []),
    decide (rows bank 3 0 0 = []),
    decide (rows bank 5 999999999999999999999 0 = []),
    decide (rows [] 0 0 3 = [[],[],[]]),
    decide (rows bank 0 999999999999999999999 3 = [[],[],[]]),
    decide (rows [] 2 7 3 = [[0,0],[0,0],[0,0]]),
    decide (rows bank 3 0 3 = [[1,2,-3/2],[2,-4,5/3],[-3/2,5/3,0]]),
    decide (rows bank 2 1 2 = [[2,-4],[-3/2,5/3]]),
    decide (rows bank 1 0 4 = [[1],[2],[-3/2],[0]]),
    decide (rows bank 3 2 2 = [[-3/2,5/3,0],[0,0,0]]),
    decide (rows bank 4 0 2 = [[1,2,-3/2,0],[2,-4,5/3,0]]),
    decide (rows bank 2 5 2 = [[0,0],[0,0]]),
    decide (rows [((0,0),-5/2)] 2 0 2 = [[-5/2,0],[0,0]]),
    decide (rows [((0,1),0),((1,0),9)] 2 0 2 = [[0,0],[0,0]]),
    decide (rows [((0,1),-2),((1,0),9)] 2 0 2 = [[0,-2],[-2,0]]),
    decide (rows [((100000000000000000000,0),-7),((1,100000000000000000001),8)]
      2 100000000000000000000 2 = [[-7,0],[0,8]]),
    decide (rows [((0,0),999999999999999999999/11)] 2 0 1 = [[999999999999999999999/11,0]]),
    decide (rows bank 0 0 16 = List.replicate 16 []),
    decide (rows [] 2 0 16 = List.replicate 16 [0,0]),
    decide (rows bank 1 1 1 = [[2]])]
  unless checks.all id do throw (IO.userError "Complete rational matrix fixtures failed")
  IO.println s!"PASS: {checks.length} full-matrix fixtures: zero count, zero width retaining empty rows, arbitrary start, independent width/count, per-row increment, inner/outer order, signed rationals, reversal, duplicate priority and large indices"
