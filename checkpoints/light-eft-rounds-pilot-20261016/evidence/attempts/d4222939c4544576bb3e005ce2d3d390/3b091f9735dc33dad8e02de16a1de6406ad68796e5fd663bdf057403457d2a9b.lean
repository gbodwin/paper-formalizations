import LightEFTSpanners.LinkedDistanceKernel
namespace LightEFTSpanners.LinkedDistance.RoundsPilotComparison
def rounds (M : Matrix) : ℕ → List Cell → List Cell :=
  Nat.rec (motive := fun _ => List Cell → List Cell) (fun d => d)
    (fun _ previous d => previous (rows d M d))
 theorem rounds_eq_prior (M : Matrix) (k : ℕ) (d : List Cell) :
    rounds M k d = LightEFTSpanners.LinkedDistance.rounds M k d := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    simp only [rounds]
    simp only [LightEFTSpanners.LinkedDistance.rounds]
    exact ih (rows d M d)
#print axioms rounds_eq_prior
end LightEFTSpanners.LinkedDistance.RoundsPilotComparison
