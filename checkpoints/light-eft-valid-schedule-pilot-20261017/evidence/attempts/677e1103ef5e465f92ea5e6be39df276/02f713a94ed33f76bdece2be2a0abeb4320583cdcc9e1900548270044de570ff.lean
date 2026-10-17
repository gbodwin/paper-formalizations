import LightEFTSpanners.StoredCandidateRefinement
namespace LightEFTSpanners.StoredCandidates.ScheduleComparison
variable {n : ℕ} {J : Type*} [DecidableEq J]
def ValidSchedule (Q : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (t : ℚ)
    (eligible : Sym2 (Fin n) → Finset J) (host : J → Finset (Sym2 (Fin n)))
    (tape : SampledGreedy.Tape (Fin n) J) (h : ℕ) :
    List (TypedInput n) → List (Fin n × Fin n) → Prop :=
  List.rec (motive := fun _ => List (Fin n × Fin n) → Prop) (fun _ => True)
    (fun R _ next E => R.budget=t*w s(R.edge.1,R.edge.2) ∧
      HostRepresentation E eligible host tape R ∧ next (updated Q E w h R))

theorem ValidSchedule_nil (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (t : ℚ)
    (eligible : Sym2 (Fin n) → Finset J) (host : J → Finset (Sym2 (Fin n)))
    (tape : SampledGreedy.Tape (Fin n) J) (h : ℕ) :
    ValidSchedule Q w t eligible host tape h [] E ↔ True := Iff.rfl

theorem ValidSchedule_cons (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (t : ℚ)
    (eligible : Sym2 (Fin n) → Finset J) (host : J → Finset (Sym2 (Fin n)))
    (tape : SampledGreedy.Tape (Fin n) J) (h : ℕ) (R : TypedInput n) (rs : List (TypedInput n)) :
    ValidSchedule Q w t eligible host tape h (R::rs) E ↔
      R.budget=t*w s(R.edge.1,R.edge.2) ∧ HostRepresentation E eligible host tape R ∧
      ValidSchedule Q w t eligible host tape h rs (updated Q E w h R) := Iff.rfl

theorem schedule_iff_prior (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (t : ℚ)
    (eligible : Sym2 (Fin n) → Finset J) (host : J → Finset (Sym2 (Fin n)))
    (tape : SampledGreedy.Tape (Fin n) J) (h : ℕ) (rs : List (TypedInput n)) :
    ValidSchedule Q w t eligible host tape h rs E ↔
      LightEFTSpanners.StoredCandidates.ValidSchedule Q w t eligible host tape h rs E := by
  induction rs generalizing E with
  | nil => exact Iff.rfl
  | cons R rs ih =>
    exact and_congr Iff.rfl (and_congr Iff.rfl (ih (updated Q E w h R)))
#print axioms schedule_iff_prior
end LightEFTSpanners.StoredCandidates.ScheduleComparison
