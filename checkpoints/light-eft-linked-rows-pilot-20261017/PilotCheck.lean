import LightEFTSpanners.LinkedDistanceKernel
open LightEFTSpanners.LinkedDistance
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.LinkedDistance.rows
  let some c := env.find? name | throwError "rows missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "rows not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: rows safe, total, computable, explicit List.rec, no partial companion"
example (d ds : List LightEFTSpanners.LinkedDistance.Cell) : rows d [] ds = [] := rfl
example (d r : List LightEFTSpanners.LinkedDistance.Cell) (rs : LightEFTSpanners.LinkedDistance.Matrix) :
    rows d (r::rs) [] = [] := rfl
example (d r : List LightEFTSpanners.LinkedDistance.Cell) (rs : LightEFTSpanners.LinkedDistance.Matrix)
    (a : LightEFTSpanners.LinkedDistance.Cell) (as : List LightEFTSpanners.LinkedDistance.Cell) :
    rows d (r::rs) (a::as) = scan r d a :: rows d rs as := rfl
example (d r : List LightEFTSpanners.LinkedDistance.Cell) (a b : LightEFTSpanners.LinkedDistance.Cell) :
    rows d [[],r] [a,b] = [a,scan r d b] := rfl
namespace RowsCases
example : rows [] [] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [] [some (5/7)] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [] [some (5/7),some (-9)] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [[]] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [[]] [some (5/7)] = [some (5/7)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [[]] [some (5/7),some (-9)] = [some (5/7)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [[]] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [some (5/7)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [[],[],[]] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [[],[],[]] [some (5/7)] = [some (5/7)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [[],[],[]] [some (5/7),some (-9)] = [some (5/7),some (-9)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [[],[],[]] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [some (5/7),some (-9),none] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [[some (0)],[some (5/7),some (-9),none,some (-3/2)],[],[none,some (-3/2)]] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [[some (0)],[some (5/7),some (-9),none,some (-3/2)],[],[none,some (-3/2)]] [some (5/7)] = [some (5/7)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [[some (0)],[some (5/7),some (-9),none,some (-3/2)],[],[none,some (-3/2)]] [some (5/7),some (-9)] = [some (5/7),some (-9)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [[some (0)],[some (5/7),some (-9),none,some (-3/2)],[],[none,some (-3/2)]] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [some (5/7),some (-9),none,some (-3/2)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [[some (0),some (5/7),some (-9),none,some (-3/2)],[some (5/7)]] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [[some (0),some (5/7),some (-9),none,some (-3/2)],[some (5/7)]] [some (5/7)] = [some (5/7)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [[some (0),some (5/7),some (-9),none,some (-3/2)],[some (5/7)]] [some (5/7),some (-9)] = [some (5/7),some (-9)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [[some (0),some (5/7),some (-9),none,some (-3/2)],[some (5/7)]] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [some (5/7),some (-9)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [[some (0),some (5/7)],[],[some (-9),none,some (-3/2),some (0),some (5/7),some (-9)],[none],[some (-3/2),some (0),some (5/7)]] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [[some (0),some (5/7)],[],[some (-9),none,some (-3/2),some (0),some (5/7),some (-9)],[none],[some (-3/2),some (0),some (5/7)]] [some (5/7)] = [some (5/7)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [[some (0),some (5/7)],[],[some (-9),none,some (-3/2),some (0),some (5/7),some (-9)],[none],[some (-3/2),some (0),some (5/7)]] [some (5/7),some (-9)] = [some (5/7),some (-9)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [] [[some (0),some (5/7)],[],[some (-9),none,some (-3/2),some (0),some (5/7),some (-9)],[none],[some (-3/2),some (0),some (5/7)]] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [some (5/7),some (-9),none,some (-3/2),some (0)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [] [some (5/7)] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [] [some (5/7),some (-9)] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [[]] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [[]] [some (5/7)] = [some (5/7)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [[]] [some (5/7),some (-9)] = [some (5/7)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [[]] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [some (5/7)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [[],[],[]] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [[],[],[]] [some (5/7)] = [some (5/7)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [[],[],[]] [some (5/7),some (-9)] = [some (5/7),some (-9)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [[],[],[]] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [some (5/7),some (-9),none] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [[some (0)],[some (5/7),some (-9),none,some (-3/2)],[],[none,some (-3/2)]] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [[some (0)],[some (5/7),some (-9),none,some (-3/2)],[],[none,some (-3/2)]] [some (5/7)] = [some (-3/2)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [[some (0)],[some (5/7),some (-9),none,some (-3/2)],[],[none,some (-3/2)]] [some (5/7),some (-9)] = [some (-3/2),some (-9)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [[some (0)],[some (5/7),some (-9),none,some (-3/2)],[],[none,some (-3/2)]] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [some (-3/2),some (-9),none,some (-3/2)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [[some (0),some (5/7),some (-9),none,some (-3/2)],[some (5/7)]] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [[some (0),some (5/7),some (-9),none,some (-3/2)],[some (5/7)]] [some (5/7)] = [some (-3/2)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [[some (0),some (5/7),some (-9),none,some (-3/2)],[some (5/7)]] [some (5/7),some (-9)] = [some (-3/2),some (-9)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [[some (0),some (5/7),some (-9),none,some (-3/2)],[some (5/7)]] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [some (-3/2),some (-9)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [[some (0),some (5/7)],[],[some (-9),none,some (-3/2),some (0),some (5/7),some (-9)],[none],[some (-3/2),some (0),some (5/7)]] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [[some (0),some (5/7)],[],[some (-9),none,some (-3/2),some (0),some (5/7),some (-9)],[none],[some (-3/2),some (0),some (5/7)]] [some (5/7)] = [some (-3/2)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [[some (0),some (5/7)],[],[some (-9),none,some (-3/2),some (0),some (5/7),some (-9)],[none],[some (-3/2),some (0),some (5/7)]] [some (5/7),some (-9)] = [some (-3/2),some (-9)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2)] [[some (0),some (5/7)],[],[some (-9),none,some (-3/2),some (0),some (5/7),some (-9)],[none],[some (-3/2),some (0),some (5/7)]] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [some (-3/2),some (-9),some (-21/2),some (-3/2),some (-3)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [] [some (5/7)] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [] [some (5/7),some (-9)] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [[]] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [[]] [some (5/7)] = [some (5/7)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [[]] [some (5/7),some (-9)] = [some (5/7)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [[]] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [some (5/7)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [[],[],[]] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [[],[],[]] [some (5/7)] = [some (5/7)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [[],[],[]] [some (5/7),some (-9)] = [some (5/7),some (-9)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [[],[],[]] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [some (5/7),some (-9),none] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [[some (0)],[some (5/7),some (-9),none,some (-3/2)],[],[none,some (-3/2)]] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [[some (0)],[some (5/7),some (-9),none,some (-3/2)],[],[none,some (-3/2)]] [some (5/7)] = [some (-3/2)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [[some (0)],[some (5/7),some (-9),none,some (-3/2)],[],[none,some (-3/2)]] [some (5/7),some (-9)] = [some (-3/2),some (-9)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [[some (0)],[some (5/7),some (-9),none,some (-3/2)],[],[none,some (-3/2)]] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [some (-3/2),some (-9),none,some (-3/2)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [[some (0),some (5/7),some (-9),none,some (-3/2)],[some (5/7)]] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [[some (0),some (5/7),some (-9),none,some (-3/2)],[some (5/7)]] [some (5/7)] = [some (-58/7)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [[some (0),some (5/7),some (-9),none,some (-3/2)],[some (5/7)]] [some (5/7),some (-9)] = [some (-58/7),some (-9)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [[some (0),some (5/7),some (-9),none,some (-3/2)],[some (5/7)]] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [some (-58/7),some (-9)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [[some (0),some (5/7)],[],[some (-9),none,some (-3/2),some (0),some (5/7),some (-9)],[none],[some (-3/2),some (0),some (5/7)]] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [[some (0),some (5/7)],[],[some (-9),none,some (-3/2),some (0),some (5/7),some (-9)],[none],[some (-3/2),some (0),some (5/7)]] [some (5/7)] = [some (-3/2)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [[some (0),some (5/7)],[],[some (-9),none,some (-3/2),some (0),some (5/7),some (-9)],[none],[some (-3/2),some (0),some (5/7)]] [some (5/7),some (-9)] = [some (-3/2),some (-9)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7)] [[some (0),some (5/7)],[],[some (-9),none,some (-3/2),some (0),some (5/7),some (-9)],[none],[some (-3/2),some (0),some (5/7)]] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [some (-3/2),some (-9),some (-21/2),some (-3/2),some (-3)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [] [some (5/7)] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [] [some (5/7),some (-9)] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [[]] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [[]] [some (5/7)] = [some (5/7)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [[]] [some (5/7),some (-9)] = [some (5/7)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [[]] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [some (5/7)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [[],[],[]] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [[],[],[]] [some (5/7)] = [some (5/7)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [[],[],[]] [some (5/7),some (-9)] = [some (5/7),some (-9)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [[],[],[]] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [some (5/7),some (-9),none] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [[some (0)],[some (5/7),some (-9),none,some (-3/2)],[],[none,some (-3/2)]] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [[some (0)],[some (5/7),some (-9),none,some (-3/2)],[],[none,some (-3/2)]] [some (5/7)] = [some (-3/2)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [[some (0)],[some (5/7),some (-9),none,some (-3/2)],[],[none,some (-3/2)]] [some (5/7),some (-9)] = [some (-3/2),some (-21/2)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [[some (0)],[some (5/7),some (-9),none,some (-3/2)],[],[none,some (-3/2)]] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [some (-3/2),some (-21/2),none,some (-3/2)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [[some (0),some (5/7),some (-9),none,some (-3/2)],[some (5/7)]] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [[some (0),some (5/7),some (-9),none,some (-3/2)],[some (5/7)]] [some (5/7)] = [some (-58/7)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [[some (0),some (5/7),some (-9),none,some (-3/2)],[some (5/7)]] [some (5/7),some (-9)] = [some (-58/7),some (-9)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [[some (0),some (5/7),some (-9),none,some (-3/2)],[some (5/7)]] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [some (-58/7),some (-9)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [[some (0),some (5/7)],[],[some (-9),none,some (-3/2),some (0),some (5/7),some (-9)],[none],[some (-3/2),some (0),some (5/7)]] [] = [] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [[some (0),some (5/7)],[],[some (-9),none,some (-3/2),some (0),some (5/7),some (-9)],[none],[some (-3/2),some (0),some (5/7)]] [some (5/7)] = [some (-3/2)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [[some (0),some (5/7)],[],[some (-9),none,some (-3/2),some (0),some (5/7),some (-9)],[none],[some (-3/2),some (0),some (5/7)]] [some (5/7),some (-9)] = [some (-3/2),some (-9)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : rows [some (-3/2),some (0),some (5/7),some (-9),none,some (-3/2)] [[some (0),some (5/7)],[],[some (-9),none,some (-3/2),some (0),some (5/7),some (-9)],[none],[some (-3/2),some (0),some (5/7)]] [some (5/7),some (-9),none,some (-3/2),some (0),some (5/7),some (-9)] = [some (-3/2),some (-9),some (-21/2),some (-3/2),some (-3)] := by norm_num [rows, scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
end RowsCases
run_cmd Lean.logInfo "PASS: 96 kernel-checked complete optional-rational list fixtures and 4 exact equations; fixed d reused for every row, ragged rows, independent accumulators, paired order, empty rows and both truncation directions"
