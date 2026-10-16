import LightEFTSpanners.RationalDistanceTable
open LightEFTSpanners.RationalDistance
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.RationalDistance.table
  let some c := env.find? name | throwError "table missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "table not safe, total, computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "table partial companion remains"
  let .defnInfo d := c | throwError "table not a definition"
  unless d.value.getUsedConstants.contains `Nat.rec do throwError "Explicit Nat.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: table safe, total, computable, explicit Nat.rec, no partial companion"

example {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (target : Fin n) (k : ℕ) (u : Fin n) (b : ℚ) :
    Below (table G w target k)[u.val] b ↔
      ∃ p : G.Walk u target, p.length≤k ∧ cost w p≤b :=
  below_table_iff G w target k u b
example (target : Fin 0) (k : ℕ) :
    table (⊥ : SimpleGraph (Fin 0)) (fun _ => -1) target k =
      Vector.ofFn (fun _ => (none : Option ℚ)) := Fin.elim0 target

private def d2 (a b : Option ℚ) : Vector (Option ℚ) 2 :=
  Vector.ofFn fun i => if i=0 then a else b
private def tt (G : SimpleGraph (Fin 2)) [DecidableRel G.Adj]
    (weight : ℚ) (target : Fin 2) (k : ℕ) := table G (fun _ => weight) target k
#eval do
  unless decide (tt ⊥ 3 0 0 = d2 (some 0) none) &&
      decide (tt ⊥ (-3) 0 4 = d2 (some 0) none) &&
      decide (tt ⊤ 3 0 1 = d2 (some 0) (some 3)) &&
      decide (tt ⊤ 0 0 2 = d2 (some 0) (some 0)) &&
      decide (tt ⊤ (-1) 0 1 = d2 (some 0) (some (-1))) &&
      decide (tt ⊤ (-1) 0 2 = d2 (some (-2)) (some (-1))) &&
      decide (tt ⊤ (-1) 0 3 = d2 (some (-2)) (some (-3))) &&
      decide (tt ⊤ (-1) 0 4 = d2 (some (-4)) (some (-3))) &&
      decide (tt ⊤ (-2) 1 3 = d2 (some (-6)) (some (-4))) &&
      decide (tt ⊤ (-1/2) 0 2 = d2 (some (-1)) (some (-1/2))) &&
      decide (table (⊥ : SimpleGraph (Fin 1)) (fun _ => -5) 0 0 =
        Vector.ofFn (fun _ => some (0 : ℚ))) &&
      decide (table (⊥ : SimpleGraph (Fin 1)) (fun _ => -5) 0 5 =
        Vector.ofFn (fun _ => some (0 : ℚ))) do
    throw (IO.userError "Full table-vector boundary fixtures failed")
  let empty : Vector (Option ℚ) 0 := Vector.ofFn fun _ => none
  unless decide (step (⊥ : SimpleGraph (Fin 0)) (fun _ => -3) empty = empty) &&
      decide (Nat.rec empty (fun _ prev => step (⊥ : SimpleGraph (Fin 0)) (fun _ => -3) prev) 5 = empty) do
    throw (IO.userError "Empty-vector recurrence boundary fixtures failed")
  IO.println "PASS: 12 full table-vector fixtures (including negative/fractional weights), 2 empty-vector step/recurrence fixtures"
