import LightEFTSpanners.ExecutableVoting
namespace LightEFTSpanners.ExecutableVoting
variable {n : ℕ} {J : Type*} [DecidableEq J]
 def replacement (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) J)
    (h : ℕ) : List (Sym2 (Fin n)) → Finset (Sym2 (Fin n)) :=
  List.rec Q (fun e _ E =>
    if h≤(votes Q w hw t eligible host tape E e).card then insert e E else E)
 theorem replacement_eq_prior (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) J)
    (h : ℕ) (l : List (Sym2 (Fin n))) :
    replacement Q w hw t eligible host tape h l = edges Q w hw t eligible host tape h l := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    simp only [replacement] at ih ⊢
    simp only [edges]
    rw [ih]
#print axioms replacement_eq_prior
end LightEFTSpanners.ExecutableVoting
