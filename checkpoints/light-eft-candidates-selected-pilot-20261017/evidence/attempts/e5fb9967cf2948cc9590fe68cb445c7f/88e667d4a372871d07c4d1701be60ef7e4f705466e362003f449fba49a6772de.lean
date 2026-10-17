import LightEFTSpanners.StoredCandidateTrace
namespace LightEFTSpanners.StoredCandidates.SelectedComparison
def selected {n : ℕ} (Q : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ)
    (h : ℕ) : List (TypedInput n) → List (Fin n × Fin n) → List (Fin n × Fin n) :=
  List.rec (motive := fun _ => List (Fin n × Fin n) → List (Fin n × Fin n)) (fun E => E)
    (fun R _ next E => next (updated Q E w h R))

theorem selected_nil {n : ℕ} (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (h : ℕ) :
    selected Q w h [] E = E := rfl

theorem selected_cons {n : ℕ} (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (h : ℕ)
    (R : TypedInput n) (rs : List (TypedInput n)) :
    selected Q w h (R::rs) E = selected Q w h rs (updated Q E w h R) := rfl

theorem selected_eq_prior {n : ℕ} (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ)
    (h : ℕ) (rs : List (TypedInput n)) :
    selected Q w h rs E = LightEFTSpanners.StoredCandidates.selected Q w h rs E := by
  induction rs generalizing E with
  | nil => rfl
  | cons R rs ih => exact ih (updated Q E w h R)
#print axioms selected_eq_prior
end LightEFTSpanners.StoredCandidates.SelectedComparison
