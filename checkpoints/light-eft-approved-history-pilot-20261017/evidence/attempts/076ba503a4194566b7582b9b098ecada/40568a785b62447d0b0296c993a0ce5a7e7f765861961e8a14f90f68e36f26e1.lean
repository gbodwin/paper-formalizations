import LightEFTSpanners.VotingAdmissionHistory
namespace LightEFTSpanners.SampledGreedy.HistoryComparison
open Finset
variable {V J : Type*} [DecidableEq V]
attribute [local instance] Classical.propDecidable
def ApprovedHistory (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ) (f h : ℕ)
    (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V)) :
    List (Sym2 V × Finset J) → Prop :=
  List.rec (motive := fun _ => Prop) True
    (fun r rs next => next ∧ r.2⊆eligible r.1 ∧ h≤r.2.card ∧
      ∀ j∈r.2,1/4≤testProbability Q (Q∪(rs.map Prod.fst).toFinset) (host j) w t f r.1)

theorem ApprovedHistory_nil (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ) (f h : ℕ)
    (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V)) :
    ApprovedHistory Q w t f h eligible host [] ↔ True := Iff.rfl

theorem ApprovedHistory_cons (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ) (f h : ℕ)
    (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V))
    (e : Sym2 V) (A : Finset J) (rs : List (Sym2 V × Finset J)) :
    ApprovedHistory Q w t f h eligible host ((e,A)::rs) ↔
      ApprovedHistory Q w t f h eligible host rs ∧ A⊆eligible e ∧ h≤A.card ∧
      ∀ j∈A,1/4≤testProbability Q (Q∪(rs.map Prod.fst).toFinset) (host j) w t f e := Iff.rfl

theorem history_iff_prior (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ) (f h : ℕ)
    (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V))
    (rs : List (Sym2 V × Finset J)) :
    ApprovedHistory Q w t f h eligible host rs ↔
      LightEFTSpanners.SampledGreedy.ApprovedHistory Q w t f h eligible host rs := by
  induction rs with
  | nil => exact Iff.rfl
  | cons r rs ih => exact and_congr ih Iff.rfl
#print axioms history_iff_prior
end LightEFTSpanners.SampledGreedy.HistoryComparison
