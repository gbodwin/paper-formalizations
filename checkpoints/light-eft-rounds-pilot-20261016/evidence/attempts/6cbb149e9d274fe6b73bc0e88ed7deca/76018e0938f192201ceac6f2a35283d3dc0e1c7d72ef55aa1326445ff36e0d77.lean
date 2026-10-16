import LightEFTSpanners.LinkedDistanceKernel
open LightEFTSpanners.LinkedDistance
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.LinkedDistance.rounds
  let some c := env.find? name | throwError "rounds missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "rounds not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `Nat.rec do throwError "Nat.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: rounds safe, total, computable, explicit Nat.rec, no partial companion"
example (M : Matrix) (d : List Cell) : rounds M 0 d = d := rfl
example (M : Matrix) (k : ℕ) (d : List Cell) :
    rounds M (k+1) d = rounds M k (rows d M d) := rfl
private def negativeCycle : Matrix := [[none,some (-1)],[some (-1),none]]
#eval do
  unless decide (rounds [] 0 [none,some 7] = [none,some 7]) &&
      decide (rounds [[some (-1)]] 0 [some 0] = [some 0]) &&
      decide (rounds [] 1 [some 3] = []) &&
      decide (rounds [] 5 [some 3,none] = []) &&
      decide (rounds [[some 2]] 4 [] = []) &&
      decide (rounds [[]] 3 [some 3,some 4] = [some 3]) &&
      decide (rounds [[],[]] 2 [some 3] = [some 3]) &&
      decide (rounds [[some (-2),some (-100)]] 2 [some 0] = [some (-4)]) &&
      decide (rounds [[some (-2)],[some 7],[some 99]] 2 [some 0,none] = [some (-4),some 5]) &&
      decide (rounds negativeCycle 1 [some 0,none] = [some 0,some (-1)]) &&
      decide (rounds negativeCycle 2 [some 0,none] = [some (-2),some (-1)]) &&
      decide (rounds negativeCycle 3 [some 0,none] = [some (-2),some (-3)]) &&
      decide (rounds [[none,none],[none,none]] 3 [none,none] = [none,none]) &&
      decide (rounds [[some (-1/2)]] 3 [some 0] = [some (-3/2)]) &&
      decide (rounds [] 5 [] = []) &&
      decide (rounds [[some 3]] 5 [some 0] = [some 0]) &&
      decide (rounds [[some 0]] 5 [some (-5)] = [some (-5)]) do
    throw (IO.userError "Full-list rounds fixtures failed")
  IO.println "PASS: 17 full-list fixtures: zero/empty, ragged truncation, missing cells, arbitrary negative/fractional cells and multiple rounds"
