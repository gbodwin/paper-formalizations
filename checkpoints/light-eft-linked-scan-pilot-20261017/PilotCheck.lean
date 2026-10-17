import LightEFTSpanners.LinkedDistanceKernel
open LightEFTSpanners.LinkedDistance
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.LinkedDistance.scan
  let some c := env.find? name | throwError "scan missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "scan not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: scan safe, total, computable, explicit List.rec, no partial companion"
example (d : List LightEFTSpanners.LinkedDistance.Cell) (z : LightEFTSpanners.LinkedDistance.Cell) : scan [] d z = z := rfl
example (a z : LightEFTSpanners.LinkedDistance.Cell) (as : List LightEFTSpanners.LinkedDistance.Cell) : scan (a::as) [] z = z := rfl
example (a b z : LightEFTSpanners.LinkedDistance.Cell) (as bs : List LightEFTSpanners.LinkedDistance.Cell) :
    scan (a::as) (b::bs) z = scan as bs (LightEFTSpanners.RationalDistance.best (addCell a b) z) := rfl
example (a b c d z : LightEFTSpanners.LinkedDistance.Cell) :
    scan [a,b] [c,d] z = LightEFTSpanners.RationalDistance.best (addCell b d)
      (LightEFTSpanners.RationalDistance.best (addCell a c) z) := rfl
namespace ScanCases
example : scan [none] [none] (none) = none := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [none] [none] (some (0)) = some (0) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [none] [none] (some (-3/2)) = some (-3/2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [none] [none] (some (5/7)) = some (5/7) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [none] [some (0)] (none) = none := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [none] [some (0)] (some (0)) = some (0) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [none] [some (0)] (some (-3/2)) = some (-3/2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [none] [some (0)] (some (5/7)) = some (5/7) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [none] [some (-3/2)] (none) = none := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [none] [some (-3/2)] (some (0)) = some (0) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [none] [some (-3/2)] (some (-3/2)) = some (-3/2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [none] [some (-3/2)] (some (5/7)) = some (5/7) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [none] [some (5/7)] (none) = none := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [none] [some (5/7)] (some (0)) = some (0) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [none] [some (5/7)] (some (-3/2)) = some (-3/2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [none] [some (5/7)] (some (5/7)) = some (5/7) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (0)] [none] (none) = none := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (0)] [none] (some (0)) = some (0) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (0)] [none] (some (-3/2)) = some (-3/2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (0)] [none] (some (5/7)) = some (5/7) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (0)] [some (0)] (none) = some (0) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (0)] [some (0)] (some (0)) = some (0) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (0)] [some (0)] (some (-3/2)) = some (-3/2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (0)] [some (0)] (some (5/7)) = some (0) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (0)] [some (-3/2)] (none) = some (-3/2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (0)] [some (-3/2)] (some (0)) = some (-3/2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (0)] [some (-3/2)] (some (-3/2)) = some (-3/2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (0)] [some (-3/2)] (some (5/7)) = some (-3/2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (0)] [some (5/7)] (none) = some (5/7) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (0)] [some (5/7)] (some (0)) = some (0) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (0)] [some (5/7)] (some (-3/2)) = some (-3/2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (0)] [some (5/7)] (some (5/7)) = some (5/7) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (-3/2)] [none] (none) = none := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (-3/2)] [none] (some (0)) = some (0) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (-3/2)] [none] (some (-3/2)) = some (-3/2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (-3/2)] [none] (some (5/7)) = some (5/7) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (-3/2)] [some (0)] (none) = some (-3/2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (-3/2)] [some (0)] (some (0)) = some (-3/2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (-3/2)] [some (0)] (some (-3/2)) = some (-3/2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (-3/2)] [some (0)] (some (5/7)) = some (-3/2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (-3/2)] [some (-3/2)] (none) = some (-3) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (-3/2)] [some (-3/2)] (some (0)) = some (-3) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (-3/2)] [some (-3/2)] (some (-3/2)) = some (-3) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (-3/2)] [some (-3/2)] (some (5/7)) = some (-3) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (-3/2)] [some (5/7)] (none) = some (-11/14) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (-3/2)] [some (5/7)] (some (0)) = some (-11/14) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (-3/2)] [some (5/7)] (some (-3/2)) = some (-3/2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (-3/2)] [some (5/7)] (some (5/7)) = some (-11/14) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (5/7)] [none] (none) = none := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (5/7)] [none] (some (0)) = some (0) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (5/7)] [none] (some (-3/2)) = some (-3/2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (5/7)] [none] (some (5/7)) = some (5/7) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (5/7)] [some (0)] (none) = some (5/7) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (5/7)] [some (0)] (some (0)) = some (0) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (5/7)] [some (0)] (some (-3/2)) = some (-3/2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (5/7)] [some (0)] (some (5/7)) = some (5/7) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (5/7)] [some (-3/2)] (none) = some (-11/14) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (5/7)] [some (-3/2)] (some (0)) = some (-11/14) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (5/7)] [some (-3/2)] (some (-3/2)) = some (-3/2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (5/7)] [some (-3/2)] (some (5/7)) = some (-11/14) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (5/7)] [some (5/7)] (none) = some (10/7) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (5/7)] [some (5/7)] (some (0)) = some (0) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (5/7)] [some (5/7)] (some (-3/2)) = some (-3/2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (5/7)] [some (5/7)] (some (5/7)) = some (5/7) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [] [] (none) = none := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [] [some (-100)] (some (5/7)) = some (5/7) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (-100)] [] (some (-3/2)) = some (-3/2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [none,none] [none,none] (none) = none := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (1),some (-100)] [some (2)] (none) = some (3) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (1)] [some (2),some (-100)] (none) = some (3) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (1),some (-100)] [some (2)] (some (-5)) = some (-5) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (1)] [some (2),some (-100)] (some (-5)) = some (-5) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (4),some (-3),some (2)] [some (1),some (1),some (-8)] (none) = some (-6) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (4),some (-3),some (2)] [some (1),some (1),some (-8)] (some (-9)) = some (-9) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [none,some (-7/3),some (2)] [some (-100),some (1/3),none] (none) = some (-2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (-7/3),none,some (2)] [some (1/3),some (-100),some (-5/2)] (some (1)) = some (-2) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (1),some (1),some (1)] [some (-1),some (-1),some (-1)] (some (0)) = some (0) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (2),some (-5),some (7)] [some (3),some (5),some (-10)] (none) = some (-3) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [some (-5),some (7),some (2)] [some (5),some (-10),some (3)] (none) = some (-3) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
example : scan [none,some (1),none] [some (-100),none,some (-100)] (some (5/7)) = some (5/7) := by norm_num [scan, addCell, LightEFTSpanners.RationalDistance.best, min_def]
end ScanCases
run_cmd Lean.logInfo "PASS: 80 kernel-checked complete optional-rational output fixtures and 4 exact equations; arbitrary initial accumulator, both truncation directions, unreachable cells, negative and fractional sums, ties and paired progression"
