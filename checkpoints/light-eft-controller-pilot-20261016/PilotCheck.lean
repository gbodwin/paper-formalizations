import LightEFTSpanners.ControllerTrace
open LightEFTSpanners.Controller

example {S : Type*} (step : S → Option S) : ℕ → S → S := run step
example {S : Type*} (step : S → Option S) (s : S) : run step 0 s = s := rfl
example {S : Type*} (step : S → Option S) (n : ℕ) (s : S) :
    run step (n+1) s = (match step s with | none => s | some t => run step n t) := rfl

open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let some c := env.find? `LightEFTSpanners.Controller.run | throwError "run missing"
  if c.isUnsafe || c.isPartial then throwError "run is not safe and total"
  if isNoncomputable env c.name then throwError "run became noncomputable"
  if (env.find? `LightEFTSpanners.Controller.run._unsafe_rec).isSome then
    throwError "Pilot partial companion still exists"
  let .defnInfo v := c | throwError "run is not a definition"
  unless v.value.getUsedConstants.contains `Nat.rec do throwError "Explicit Nat.rec absent"
  if v.value.getUsedConstants.contains c.name then throwError "run body refers to itself"
  logInfo "PASS: run is safe, total, computable, explicitly Nat.rec, and has no partial companion"

#eval do
  let step := fun n : Nat => if n < 3 then some (n+1) else none
  unless run step 0 0 == 0 && run step 2 0 == 2 && run step 7 0 == 3 &&
      run (fun _ : Nat => none) 9 5 == 5 && run (fun n : Nat => some n) 9 5 == 5 do
    throw (IO.userError "Controller execution fixture failed")
  IO.println "PASS: five executable controller fixtures (zero, advance, stop, immediate stop, stationary step)"
