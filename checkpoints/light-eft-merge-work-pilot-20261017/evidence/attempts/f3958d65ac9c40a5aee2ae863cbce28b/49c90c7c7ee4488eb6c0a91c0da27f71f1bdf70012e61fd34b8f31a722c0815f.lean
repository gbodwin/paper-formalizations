import LightEFTSpanners.StoredWeightMergeTrace
open LightEFTSpanners.StoredWeightMerge
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredWeightMerge.work
  let some c := env.find? name | throwError "work missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "work not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: work safe, total, computable, explicit List.rec, no partial companion"
example (bank : LightEFTSpanners.StoredOriginalWeightLookup.Bank) (ys : List LightEFTSpanners.StoredEdges.Edge) : work bank [] ys = ys.length+2 := rfl
example (bank : LightEFTSpanners.StoredOriginalWeightLookup.Bank) (xs : List LightEFTSpanners.StoredEdges.Edge) : work bank xs [] = xs.length+2 := by cases xs <;> rfl
example (bank : LightEFTSpanners.StoredOriginalWeightLookup.Bank) (x y : LightEFTSpanners.StoredEdges.Edge)
    (xs ys : List LightEFTSpanners.StoredEdges.Edge) :
    work bank (x::xs) (y::ys) = LightEFTSpanners.StoredWeightComparison.steps bank x y+2+
      if LightEFTSpanners.StoredWeightComparison.result bank x y then work bank xs (y::ys) else work bank (x::xs) ys := rfl
#eval do
  let checks := [
    decide (work [] [] [] = 2),
    decide (work [] [] [(0,1),(2,3)] = 4),
    decide (work [] [(0,1),(2,3)] [] = 4),
    decide (work [] [(0,1)] [(2,3)] = 10),
    decide (work [] [(0,1),(0,1)] [(2,3)] = 17),
    decide (work [] [(0,1)] [(2,3),(2,3)] = 11),
    decide (work [((0,1),2),((2,3),1)] [(0,1)] [(2,3)] = 11),
    decide (work [((0,1),1),((2,3),2)] [(0,1)] [(2,3)] = 11),
    decide (work [((0,1),2),((2,3),1)] [(0,1),(0,1)] [(2,3)] = 19),
    decide (work [((0,1),1),((2,3),2)] [(0,1),(0,1)] [(2,3)] = 12),
    decide (work [((0,1),2),((2,3),2)] [(0,1),(0,1)] [(2,3)] = 19),
    decide (work [((0,1),-3/2),((2,3),-2)] [(0,1),(0,1)] [(2,3)] = 19),
    decide (work [((0,1),-3/2),((2,3),-1)] [(0,1),(0,1)] [(2,3)] = 12),
    decide (work [((0,1),2),((2,3),1)] [(1,0),(1,0)] [(2,3)] = 19),
    decide (work [((0,1),1),((0,1),99),((2,3),2)] [(0,1),(0,1)] [(2,3)] = 13),
    decide (work [((4,5),9)] [(0,1),(0,1)] [(2,3)] = 21),
    decide (work [((0,1),2),((2,3),1)] [(2,3),(0,1),(4,5)] [(0,1),(2,3)] = 38),
    decide (work [((7,7),-1),((0,1),-2)] [(7,7),(7,7)] [(0,1)] = 19),
    decide (work [((100000000000000000000,99999999999999999999),3),((0,1),1)] [(100000000000000000000,99999999999999999999),(100000000000000000000,99999999999999999999)] [(1,0)] = 19),
    decide (work [] [(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1),(0,1)] [(2,3)] = 115),
    decide (work [] [(0,1)] [(2,3),(2,3),(2,3),(2,3),(2,3),(2,3),(2,3),(2,3),(2,3),(2,3),(2,3),(2,3),(2,3),(2,3),(2,3),(2,3)] = 25),
    decide (work [((0,1),2),((2,3),1)] [(0,1),(2,3),(0,1)] [(2,3),(0,1),(2,3)] = 30),
    decide (work [] [] [(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7),(7,7)] = 34),
    decide (work [((4,5),-8),((4,5),-8),((4,5),-8),((4,5),-8),((4,5),-8),((4,5),-8),((4,5),-8),((4,5),-8),((4,5),-8),((4,5),-8),((4,5),-8),((4,5),-8),((4,5),-8),((4,5),-8),((4,5),-8),((4,5),-8)] [(0,1)] [(2,3)] = 42)]
  unless checks.all id do throw (IO.userError "Exact merge work-count fixtures failed")
  IO.println s!"PASS: {checks.length} complete merge work-count fixtures; empty sides, left/right shrinking, ties choose left, negatives, duplicate bank keys, reversed edges, missing keys, unsorted lists, huge naturals and long lists"
