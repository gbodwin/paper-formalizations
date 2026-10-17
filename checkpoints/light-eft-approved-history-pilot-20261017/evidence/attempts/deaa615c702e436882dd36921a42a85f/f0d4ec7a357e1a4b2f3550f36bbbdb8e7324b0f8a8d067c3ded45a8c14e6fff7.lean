import LightEFTSpanners.FinitePartitionRefinement
import Mathlib.Logic.Function.Iterate

namespace LightEFTSpanners.MultigraphCuts
open Finset SimpleGraph

/-- A genuinely decreasing natural measure bounds the first stable iterate. -/
theorem exists_fixed_iterate_of_decrease {A : Type*} (step : A → A) (measure : A → ℕ)
    (hdrop : ∀ a,step a≠a → measure (step a)<measure a) (a : A) :
    ∃ n≤measure a,step ((step^[n]) a)=(step^[n]) a := by
  generalize hN : measure a=N
  induction N using Nat.strong_induction_on generalizing a with
  | h N ih =>
    by_cases hf : step a=a
    · exact ⟨0,by omega,by simpa using hf⟩
    · have hlt : measure (step a)<N := by simpa [hN] using hdrop a hf
      obtain ⟨n,hn,hfix⟩ := ih (measure (step a)) hlt (step a) rfl
      refine ⟨n+1,by omega,?_⟩
      simpa only [Function.iterate_succ_apply] using hfix

variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

/-- The explicit least-color iteration reaches a partition whose every block
is genuinely connected in every color. The bound counts actual within-block
ordered vertex pairs and is independent of any packing-existence assumption. -/
theorem exists_stable_color_refinement {k : ℕ} (H : Fin k → SimpleGraph V)
    (R : Setoid V) :
    ∃ n≤(relatedPairs R).card,∀ c,
      componentRefinement (H c) ((refinementStep H)^[n] R)=
        (refinementStep H)^[n] R := by
  obtain ⟨n,hn,hfix⟩ := exists_fixed_iterate_of_decrease (refinementStep H)
    (fun S => (relatedPairs S).card) (refinementStep_measure_lt H) R
  exact ⟨n,hn,(refinementStep_eq_iff H _).mp hfix⟩

omit [Fintype V] in
theorem refinement_iterate_le {k : ℕ} (H : Fin k → SimpleGraph V) (R : Setoid V) (n : ℕ) :
    (refinementStep H)^[n] R≤R := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (refinementStep_le H _).trans ih

omit [Fintype V] in
/-- Every common connected refinement of the initial partition remains below
all stages. Thus the terminal partition has not arbitrarily thrown away the
connectivity structure by substituting the singleton partition. -/
theorem common_refinement_le_iterates {k : ℕ} (H : Fin k → SimpleGraph V)
    {Q R : Setoid V} (hQR : Q≤R)
    (hQ : ∀ c,componentRefinement (H c) Q=Q) (n : ℕ) :
    Q≤(refinementStep H)^[n] R := by
  classical
  induction n with
  | zero => exact hQR
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    unfold refinementStep
    split
    · rw [← hQ _]
      exact componentRefinement_mono _ ih
    · exact ih

/-- An explicit quadratic vertex bound on the number of refinement rounds. -/
theorem stable_refinement_quadratic_bound {k : ℕ} (H : Fin k → SimpleGraph V)
    (R : Setoid V) :
    ∃ n≤Fintype.card V*Fintype.card V,
      (refinementStep H)^[n] R≤R ∧
      (∀ c,componentRefinement (H c) ((refinementStep H)^[n] R)=
        (refinementStep H)^[n] R) ∧
      (∀ Q : Setoid V,Q≤R → (∀ c,componentRefinement (H c) Q=Q) →
        Q≤(refinementStep H)^[n] R) := by
  classical
  obtain ⟨n,hn,hfixed⟩ := exists_stable_color_refinement H R
  have hcard : (relatedPairs R).card≤Fintype.card V*Fintype.card V := by
    simpa using (card_le_univ (s:=relatedPairs R))
  exact ⟨n,hn.trans hcard,refinement_iterate_le H R n,hfixed,
    fun Q hQR hQ => common_refinement_le_iterates H hQR hQ n⟩
end LightEFTSpanners.MultigraphCuts
