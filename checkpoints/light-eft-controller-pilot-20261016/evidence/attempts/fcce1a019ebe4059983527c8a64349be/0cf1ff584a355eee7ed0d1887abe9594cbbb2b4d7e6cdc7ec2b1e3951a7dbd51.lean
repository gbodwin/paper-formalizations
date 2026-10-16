import LightEFTSpanners.ControllerTrace

/- This file is compiled against the preserved pre-pilot object set, NOT the repaired
aggregate. The replacement body below is byte-for-byte the pilot's Nat.rec body. -/
namespace ControllerPilotComparison
 def replacement {S : Type*} (step : S → Option S) : ℕ → S → S :=
  Nat.rec (motive := fun _ => S → S) (fun s => s)
    (fun _ previous s => match step s with | none => s | some t => previous t)
 theorem replacement_eq_prior {S : Type*} (step : S → Option S) :
    replacement step = LightEFTSpanners.Controller.run step := by
  funext n s
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    change (match step s with | none => s | some t => replacement step n t) =
      (match step s with | none => s | some t => LightEFTSpanners.Controller.run step n t)
    cases step s with
    | none => rfl
    | some t => exact ih t
end ControllerPilotComparison
#print axioms ControllerPilotComparison.replacement_eq_prior
