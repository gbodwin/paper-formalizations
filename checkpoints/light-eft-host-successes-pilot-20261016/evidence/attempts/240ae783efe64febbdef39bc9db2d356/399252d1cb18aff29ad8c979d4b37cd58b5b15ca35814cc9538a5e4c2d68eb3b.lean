import LightEFTSpanners.StoredHostMachine
namespace LightEFTSpanners.StoredHosts.SuccessesComparison
def successes (vote : Input → Bool) : List Input → ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun R _ rest => (if vote R then 1 else 0)+rest)
theorem successes_eq_prior (vote : Input → Bool) (rs : List Input) :
    successes vote rs = LightEFTSpanners.StoredHosts.successes vote rs := by
  induction rs with
  | nil => rfl
  | cons R rs ih =>
    exact congrArg (fun rest => (if vote R then 1 else 0)+rest) ih
#print axioms successes_eq_prior
end LightEFTSpanners.StoredHosts.SuccessesComparison
