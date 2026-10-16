import LightEFTSpanners.LinkedDistanceMachine
namespace LightEFTSpanners.LinkedDistance.RunPilotComparison
def run (size : ℕ) (M : Matrix) (source target : ℕ) (budget : ℚ) : ℕ → State → State :=
  Nat.rec (motive := fun _ => State → State) (fun s => s)
    (fun _ previous s => match transition size M source target budget s with
      | none => s
      | some t => previous t)
 theorem run_eq_prior (size : ℕ) (M : Matrix) (source target : ℕ) (budget : ℚ)
    (k : ℕ) (s : State) :
    run size M source target budget k s =
      LightEFTSpanners.LinkedDistance.run size M source target budget k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    cases he : transition size M source target budget s with
    | none => simp [run,LightEFTSpanners.LinkedDistance.run,he]
    | some t => simpa only [run,LightEFTSpanners.LinkedDistance.run,he] using ih t
#print axioms run_eq_prior
end LightEFTSpanners.LinkedDistance.RunPilotComparison
