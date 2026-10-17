import LightEFTSpanners.StoredCandidateTrace
namespace LightEFTSpanners.StoredCandidates.WorkComparison
def work {n : ℕ} (Q : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ)
    (h : ℕ) : List (TypedInput n) → List (Fin n × Fin n) → ℕ :=
  List.rec (motive := fun _ => List (Fin n × Fin n) → ℕ) (fun _ => 1)
    (fun R _ next E => (R.hosts.map fun H => StoredHosts.hostBound Q E H+2).sum+3+
      next (updated Q E w h R))

theorem work_nil {n : ℕ} (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (h : ℕ) :
    work Q w h [] E = 1 := rfl

theorem work_cons {n : ℕ} (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (h : ℕ)
    (R : TypedInput n) (rs : List (TypedInput n)) :
    work Q w h (R::rs) E = (R.hosts.map fun H => StoredHosts.hostBound Q E H+2).sum+3+
      work Q w h rs (updated Q E w h R) := rfl

theorem work_eq_prior {n : ℕ} (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ)
    (h : ℕ) (rs : List (TypedInput n)) :
    work Q w h rs E = LightEFTSpanners.StoredCandidates.work Q w h rs E := by
  induction rs generalizing E with
  | nil => rfl
  | cons R rs ih =>
    exact congrArg (fun rest => (R.hosts.map fun H => StoredHosts.hostBound Q E H+2).sum+3+rest)
      (ih (updated Q E w h R))
#print axioms work_eq_prior
end LightEFTSpanners.StoredCandidates.WorkComparison
