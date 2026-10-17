import LightEFTSpanners.LinkedDistanceTrace
open LightEFTSpanners.LinkedDistance
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.LinkedDistance.rowTicks
  let some c := env.find? name | throwError "rowTicks missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "rowTicks not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: rowTicks safe, total, computable, explicit List.rec, no partial companion"
example (d ds : List LightEFTSpanners.LinkedDistance.Cell) : rowTicks d [] ds = 0 := rfl
example (d r : List LightEFTSpanners.LinkedDistance.Cell) (rs : LightEFTSpanners.LinkedDistance.Matrix) :
    rowTicks d (r::rs) [] = 0 := rfl
example (d r : List LightEFTSpanners.LinkedDistance.Cell) (rs : LightEFTSpanners.LinkedDistance.Matrix)
    (a : LightEFTSpanners.LinkedDistance.Cell) (as : List LightEFTSpanners.LinkedDistance.Cell) :
    rowTicks d (r::rs) (a::as) = min r.length d.length+3+rowTicks d rs as := rfl
example (d : List LightEFTSpanners.LinkedDistance.Cell) (rs : LightEFTSpanners.LinkedDistance.Matrix)
    (a : LightEFTSpanners.LinkedDistance.Cell) (as : List LightEFTSpanners.LinkedDistance.Cell) :
    rowTicks d ([]::rs) (a::as) = 3+rowTicks d rs as := rfl
namespace RowTicksCases
example : rowTicks [] [] [] = 0 := by rfl
example : rowTicks [] [] [some (-3/7)] = 0 := by rfl
example : rowTicks [] [] [some (-3/7),none] = 0 := by rfl
example : rowTicks [] [] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 0 := by rfl
example : rowTicks [] [[]] [] = 0 := by rfl
example : rowTicks [] [[]] [some (-3/7)] = 3 := by rfl
example : rowTicks [] [[]] [some (-3/7),none] = 3 := by rfl
example : rowTicks [] [[]] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 3 := by rfl
example : rowTicks [] [[],[],[]] [] = 0 := by rfl
example : rowTicks [] [[],[],[]] [some (-3/7)] = 3 := by rfl
example : rowTicks [] [[],[],[]] [some (-3/7),none] = 6 := by rfl
example : rowTicks [] [[],[],[]] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 9 := by rfl
example : rowTicks [] [[none],[some (-3/7),none,some (-1/7),none],[],[some (-3/7),none]] [] = 0 := by rfl
example : rowTicks [] [[none],[some (-3/7),none,some (-1/7),none],[],[some (-3/7),none]] [some (-3/7)] = 3 := by rfl
example : rowTicks [] [[none],[some (-3/7),none,some (-1/7),none],[],[some (-3/7),none]] [some (-3/7),none] = 6 := by rfl
example : rowTicks [] [[none],[some (-3/7),none,some (-1/7),none],[],[some (-3/7),none]] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 12 := by rfl
example : rowTicks [] [[none,some (-2/7),none,some (0/7),none],[some (-3/7)]] [] = 0 := by rfl
example : rowTicks [] [[none,some (-2/7),none,some (0/7),none],[some (-3/7)]] [some (-3/7)] = 3 := by rfl
example : rowTicks [] [[none,some (-2/7),none,some (0/7),none],[some (-3/7)]] [some (-3/7),none] = 6 := by rfl
example : rowTicks [] [[none,some (-2/7),none,some (0/7),none],[some (-3/7)]] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 6 := by rfl
example : rowTicks [] [[none,some (-2/7)],[],[none,some (-2/7),none,some (0/7),none,some (2/7)],[some (-3/7)],[none,some (-2/7),none]] [] = 0 := by rfl
example : rowTicks [] [[none,some (-2/7)],[],[none,some (-2/7),none,some (0/7),none,some (2/7)],[some (-3/7)],[none,some (-2/7),none]] [some (-3/7)] = 3 := by rfl
example : rowTicks [] [[none,some (-2/7)],[],[none,some (-2/7),none,some (0/7),none,some (2/7)],[some (-3/7)],[none,some (-2/7),none]] [some (-3/7),none] = 6 := by rfl
example : rowTicks [] [[none,some (-2/7)],[],[none,some (-2/7),none,some (0/7),none,some (2/7)],[some (-3/7)],[none,some (-2/7),none]] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 15 := by rfl
example : rowTicks [none] [] [] = 0 := by rfl
example : rowTicks [none] [] [some (-3/7)] = 0 := by rfl
example : rowTicks [none] [] [some (-3/7),none] = 0 := by rfl
example : rowTicks [none] [] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 0 := by rfl
example : rowTicks [none] [[]] [] = 0 := by rfl
example : rowTicks [none] [[]] [some (-3/7)] = 3 := by rfl
example : rowTicks [none] [[]] [some (-3/7),none] = 3 := by rfl
example : rowTicks [none] [[]] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 3 := by rfl
example : rowTicks [none] [[],[],[]] [] = 0 := by rfl
example : rowTicks [none] [[],[],[]] [some (-3/7)] = 3 := by rfl
example : rowTicks [none] [[],[],[]] [some (-3/7),none] = 6 := by rfl
example : rowTicks [none] [[],[],[]] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 9 := by rfl
example : rowTicks [none] [[none],[some (-3/7),none,some (-1/7),none],[],[some (-3/7),none]] [] = 0 := by rfl
example : rowTicks [none] [[none],[some (-3/7),none,some (-1/7),none],[],[some (-3/7),none]] [some (-3/7)] = 4 := by rfl
example : rowTicks [none] [[none],[some (-3/7),none,some (-1/7),none],[],[some (-3/7),none]] [some (-3/7),none] = 8 := by rfl
example : rowTicks [none] [[none],[some (-3/7),none,some (-1/7),none],[],[some (-3/7),none]] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 15 := by rfl
example : rowTicks [none] [[none,some (-2/7),none,some (0/7),none],[some (-3/7)]] [] = 0 := by rfl
example : rowTicks [none] [[none,some (-2/7),none,some (0/7),none],[some (-3/7)]] [some (-3/7)] = 4 := by rfl
example : rowTicks [none] [[none,some (-2/7),none,some (0/7),none],[some (-3/7)]] [some (-3/7),none] = 8 := by rfl
example : rowTicks [none] [[none,some (-2/7),none,some (0/7),none],[some (-3/7)]] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 8 := by rfl
example : rowTicks [none] [[none,some (-2/7)],[],[none,some (-2/7),none,some (0/7),none,some (2/7)],[some (-3/7)],[none,some (-2/7),none]] [] = 0 := by rfl
example : rowTicks [none] [[none,some (-2/7)],[],[none,some (-2/7),none,some (0/7),none,some (2/7)],[some (-3/7)],[none,some (-2/7),none]] [some (-3/7)] = 4 := by rfl
example : rowTicks [none] [[none,some (-2/7)],[],[none,some (-2/7),none,some (0/7),none,some (2/7)],[some (-3/7)],[none,some (-2/7),none]] [some (-3/7),none] = 7 := by rfl
example : rowTicks [none] [[none,some (-2/7)],[],[none,some (-2/7),none,some (0/7),none,some (2/7)],[some (-3/7)],[none,some (-2/7),none]] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 19 := by rfl
example : rowTicks [none,some (-2/7),none] [] [] = 0 := by rfl
example : rowTicks [none,some (-2/7),none] [] [some (-3/7)] = 0 := by rfl
example : rowTicks [none,some (-2/7),none] [] [some (-3/7),none] = 0 := by rfl
example : rowTicks [none,some (-2/7),none] [] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 0 := by rfl
example : rowTicks [none,some (-2/7),none] [[]] [] = 0 := by rfl
example : rowTicks [none,some (-2/7),none] [[]] [some (-3/7)] = 3 := by rfl
example : rowTicks [none,some (-2/7),none] [[]] [some (-3/7),none] = 3 := by rfl
example : rowTicks [none,some (-2/7),none] [[]] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 3 := by rfl
example : rowTicks [none,some (-2/7),none] [[],[],[]] [] = 0 := by rfl
example : rowTicks [none,some (-2/7),none] [[],[],[]] [some (-3/7)] = 3 := by rfl
example : rowTicks [none,some (-2/7),none] [[],[],[]] [some (-3/7),none] = 6 := by rfl
example : rowTicks [none,some (-2/7),none] [[],[],[]] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 9 := by rfl
example : rowTicks [none,some (-2/7),none] [[none],[some (-3/7),none,some (-1/7),none],[],[some (-3/7),none]] [] = 0 := by rfl
example : rowTicks [none,some (-2/7),none] [[none],[some (-3/7),none,some (-1/7),none],[],[some (-3/7),none]] [some (-3/7)] = 4 := by rfl
example : rowTicks [none,some (-2/7),none] [[none],[some (-3/7),none,some (-1/7),none],[],[some (-3/7),none]] [some (-3/7),none] = 10 := by rfl
example : rowTicks [none,some (-2/7),none] [[none],[some (-3/7),none,some (-1/7),none],[],[some (-3/7),none]] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 18 := by rfl
example : rowTicks [none,some (-2/7),none] [[none,some (-2/7),none,some (0/7),none],[some (-3/7)]] [] = 0 := by rfl
example : rowTicks [none,some (-2/7),none] [[none,some (-2/7),none,some (0/7),none],[some (-3/7)]] [some (-3/7)] = 6 := by rfl
example : rowTicks [none,some (-2/7),none] [[none,some (-2/7),none,some (0/7),none],[some (-3/7)]] [some (-3/7),none] = 10 := by rfl
example : rowTicks [none,some (-2/7),none] [[none,some (-2/7),none,some (0/7),none],[some (-3/7)]] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 10 := by rfl
example : rowTicks [none,some (-2/7),none] [[none,some (-2/7)],[],[none,some (-2/7),none,some (0/7),none,some (2/7)],[some (-3/7)],[none,some (-2/7),none]] [] = 0 := by rfl
example : rowTicks [none,some (-2/7),none] [[none,some (-2/7)],[],[none,some (-2/7),none,some (0/7),none,some (2/7)],[some (-3/7)],[none,some (-2/7),none]] [some (-3/7)] = 5 := by rfl
example : rowTicks [none,some (-2/7),none] [[none,some (-2/7)],[],[none,some (-2/7),none,some (0/7),none,some (2/7)],[some (-3/7)],[none,some (-2/7),none]] [some (-3/7),none] = 8 := by rfl
example : rowTicks [none,some (-2/7),none] [[none,some (-2/7)],[],[none,some (-2/7),none,some (0/7),none,some (2/7)],[some (-3/7)],[none,some (-2/7),none]] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 24 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [] [] = 0 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [] [some (-3/7)] = 0 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [] [some (-3/7),none] = 0 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 0 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [[]] [] = 0 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [[]] [some (-3/7)] = 3 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [[]] [some (-3/7),none] = 3 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [[]] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 3 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [[],[],[]] [] = 0 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [[],[],[]] [some (-3/7)] = 3 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [[],[],[]] [some (-3/7),none] = 6 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [[],[],[]] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 9 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [[none],[some (-3/7),none,some (-1/7),none],[],[some (-3/7),none]] [] = 0 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [[none],[some (-3/7),none,some (-1/7),none],[],[some (-3/7),none]] [some (-3/7)] = 4 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [[none],[some (-3/7),none,some (-1/7),none],[],[some (-3/7),none]] [some (-3/7),none] = 11 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [[none],[some (-3/7),none,some (-1/7),none],[],[some (-3/7),none]] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 19 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [[none,some (-2/7),none,some (0/7),none],[some (-3/7)]] [] = 0 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [[none,some (-2/7),none,some (0/7),none],[some (-3/7)]] [some (-3/7)] = 8 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [[none,some (-2/7),none,some (0/7),none],[some (-3/7)]] [some (-3/7),none] = 12 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [[none,some (-2/7),none,some (0/7),none],[some (-3/7)]] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 12 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [[none,some (-2/7)],[],[none,some (-2/7),none,some (0/7),none,some (2/7)],[some (-3/7)],[none,some (-2/7),none]] [] = 0 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [[none,some (-2/7)],[],[none,some (-2/7),none,some (0/7),none,some (2/7)],[some (-3/7)],[none,some (-2/7),none]] [some (-3/7)] = 5 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [[none,some (-2/7)],[],[none,some (-2/7),none,some (0/7),none,some (2/7)],[some (-3/7)],[none,some (-2/7),none]] [some (-3/7),none] = 8 := by rfl
example : rowTicks [none,some (-2/7),none,some (0/7),none,some (2/7)] [[none,some (-2/7)],[],[none,some (-2/7),none,some (0/7),none,some (2/7)],[some (-3/7)],[none,some (-2/7),none]] [some (-3/7),none,some (-1/7),none,some (1/7),none,some (3/7)] = 27 := by rfl
end RowTicksCases
run_cmd Lean.logInfo "PASS: 96 kernel-checked exact natural-count fixtures and 4 exact equations; arbitrary d, ragged matrices, unequal list lengths, stop at either end, empty-row overhead and paired order"
