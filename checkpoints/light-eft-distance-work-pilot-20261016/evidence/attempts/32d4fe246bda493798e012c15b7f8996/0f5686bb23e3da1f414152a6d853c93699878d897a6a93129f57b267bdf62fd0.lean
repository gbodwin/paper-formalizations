import LightEFTSpanners.RationalDistanceWork
open LightEFTSpanners.RationalDistance
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  for (name, recursor) in [(`LightEFTSpanners.RationalDistance.scanWork, `List.rec),
      (`LightEFTSpanners.RationalDistance.tableWork, `Nat.rec)] do
    let some c := env.find? name | throwError "Missing {name}"
    if c.isUnsafe || c.isPartial || isNoncomputable env name then
      throwError "{name} not safe, total and computable"
    if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains: {name}"
    let .defnInfo d := c | throwError "Not a definition: {name}"
    unless d.value.getUsedConstants.contains recursor do throwError "Required recursor absent: {name}"
    if d.value.getUsedConstants.contains name then throwError "Self-reference: {name}"
    logInfo m!"PASS: {name} safe, total, computable, explicit {recursor}, no partial companion"
  let some old := env.find? `LightEFTSpanners.RationalDistance.table._unsafe_rec |
    throwError "Separate table companion unexpectedly absent"
  unless old.isPartial do throwError "Separate table companion changed"
  logInfo "PASS: RationalDistance.table partial companion remains explicitly outside this pilot"

private def d2 (a b : Option ℚ) : Vector (Option ℚ) 2 :=
  Vector.ofFn fun i => if i=0 then a else b
private def sw (G : SimpleGraph (Fin 2)) [DecidableRel G.Adj]
    (weight : ℚ) (d : Vector (Option ℚ) 2) (u : Fin 2) (l : List (Fin 2)) :=
  scanWork G (fun _ => weight) d u l
private def tw (G : SimpleGraph (Fin 2)) [DecidableRel G.Adj] (weight : ℚ) (k : ℕ) :=
  tableWork G (fun _ => weight) (0 : Fin 2) k
#eval do
  unless decide (sw ⊥ 3 (d2 (some 7) none) 0 [] = (some 7,1)) &&
      decide (sw ⊥ 3 (d2 (some 7) none) 1 [] = (none,1)) &&
      decide (sw ⊥ 3 (d2 (some 7) none) 1 [0,1] = (none,13)) &&
      decide (sw ⊤ 3 (d2 (some 0) none) 1 [0] = (some 3,7)) &&
      decide (sw ⊤ 3 (d2 (some 0) none) 0 [1] = (some 0,7)) &&
      decide (sw ⊤ 3 (d2 (some 10) (some 2)) 0 [1] = (some 5,7)) &&
      decide (sw ⊤ 3 (d2 (some 10) (some 2)) 0 [1,1] = (some 5,13)) &&
      decide (sw ⊤ (-3) (d2 (some 10) (some 2)) 0 [1] = (some (-1),7)) &&
      decide (sw ⊤ 0 (d2 (some 10) (some 2)) 0 [1] = (some 2,7)) do
    throw (IO.userError "scanWork full-pair boundary fixtures failed")
  unless decide (tw ⊥ 3 0 = (d2 (some 0) none,2)) &&
      decide (tw ⊥ 3 2 = (d2 (some 0) none,58)) &&
      decide (tw ⊤ 3 1 = (d2 (some 0) (some 3),30)) &&
      decide (tw ⊤ 3 2 = (d2 (some 0) (some 3),58)) &&
      decide (tw ⊤ 0 1 = (d2 (some 0) (some 0),30)) &&
      decide (tableWork (⊥ : SimpleGraph (Fin 1)) (fun _ => 3) 0 0 =
        (Vector.ofFn (fun _ => some (0 : ℚ)),1)) &&
      decide (tableWork (⊥ : SimpleGraph (Fin 1)) (fun _ => 3) 0 3 =
        (Vector.ofFn (fun _ => some (0 : ℚ)),25)) do
    throw (IO.userError "tableWork full-vector/counter boundary fixtures failed")
  unless decide (stepWork (⊥ : SimpleGraph (Fin 0)) (fun _ => 0)
      (Vector.ofFn fun _ => (none : Option ℚ)) =
      (Vector.ofFn (fun _ => (none : Option ℚ)),0)) do
    throw (IO.userError "Empty-vector step boundary fixture failed")
  IO.println "PASS: 9 full Option/counter scan fixtures, 7 full vector/counter table fixtures, 1 empty-vector step fixture"
