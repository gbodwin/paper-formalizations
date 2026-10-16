import LightEFTSpanners.StoredOriginalWeightMatrix
open LightEFTSpanners
open StoredOriginalWeightMatrix
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredOriginalWeightMatrix.row
  let some c := env.find? name | throwError "row missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "row not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `Nat.rec do throwError "Nat.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: row safe, total, computable, explicit Nat.rec, no partial companion"
example (bank : StoredOriginalWeightLookup.Bank) (i j : ℕ) : row bank i j 0 = [] := rfl
example (bank : StoredOriginalWeightLookup.Bank) (i j k : ℕ) :
    row bank i j (k+1) = StoredOriginalWeightLookup.value (i,j) bank::row bank i (j+1) k := rfl
private def bank : StoredOriginalWeightLookup.Bank :=
  [((2,0),-1/3),((1,2),5/2),((2,2),0),((2,3),-7),((4,2),11/3),((2,0),99)]
#eval do
  let checks := [
    decide (row [] 0 0 0 = []),
    decide (row bank 2 0 0 = []),
    decide (row bank 999999999999999999999 888888888888888888888 0 = []),
    decide (row [] 7 8 4 = [0,0,0,0]),
    decide (row bank 2 0 1 = [-1/3]),
    decide (row bank 2 0 5 = [-1/3,5/2,0,-7,11/3]),
    decide (row bank 2 1 3 = [5/2,0,-7]),
    decide (row bank 2 3 3 = [-7,11/3,0]),
    decide (row bank 2 4 3 = [11/3,0,0]),
    decide (row bank 0 0 4 = [0,0,-1/3,0]),
    decide (row bank 1 2 1 = [5/2]),
    decide (row bank 3 2 1 = [-7]),
    decide (row bank 4 2 1 = [11/3]),
    decide (row [((0,0),-5/2)] 0 0 3 = [-5/2,0,0]),
    decide (row [((0,1),0),((1,0),9)] 0 0 3 = [0,0,0]),
    decide (row [((0,1),-9),((1,0),7)] 0 0 3 = [0,-9,0]),
    decide (row [((100000000000000000000,7),-2/3),((8,100000000000000000000),4/5)]
      100000000000000000000 7 3 = [-2/3,4/5,0]),
    decide (row [((0,100000000000000000000),-3),((100000000000000000001,0),2)]
      0 100000000000000000000 3 = [-3,2,0]),
    decide (row [] 79 100 32 = List.replicate 32 0),
    decide (row [((7,8),999999999999999999999/11)] 7 7 3 = [0,999999999999999999999/11,0])]
  unless checks.all id do throw (IO.userError "Complete rational row fixtures failed")
  IO.println s!"PASS: {checks.length} full-row fixtures: zero length, arbitrary row/column indices, per-cell increment, exact order, signed rationals, reversal, duplicate priority, zero first match, missing cells and large indices"
