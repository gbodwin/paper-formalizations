import LightEFTSpanners.StoredCandidateOriginal
import LightEFTSpanners.FreshVotingTapes

namespace LightEFTSpanners.StoredCandidates

/-- Stored candidate records from a fixed assignment bank. Constructing this
input list is not charged by the candidate interpreter's transition theorem. -/
def assignmentRecords {n : ℕ} {J : Type*} (w : Sym2 (Fin n) → ℚ) (t : ℚ)
    (js : Sym2 (Fin n) → List J)
    (input : Sym2 (Fin n) → J → StoredHosts.TypedInput n)
    (es : List (Fin n × Fin n)) : List (TypedInput n) :=
  es.map fun e => ⟨e,t*w s(e.1,e.2),(js s(e.1,e.2)).map (input s(e.1,e.2))⟩

/-- The original assignment tape is independent of the reached selected set.
Consequently static input identities suffice at every actual reached state. -/
theorem assignment_schedule {n m : ℕ} {J : Type*} [DecidableEq J]
    (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (t : ℚ)
    (eligible : Sym2 (Fin n) → Finset J) (host : J → Finset (Sym2 (Fin n)))
    (a : SampledGreedy.Assignment (Fin n) J m) (h : ℕ)
    (js : Sym2 (Fin n) → List J)
    (input : Sym2 (Fin n) → J → StoredHosts.TypedInput n)
    (es : List (Fin n × Fin n))
    (hj : ∀ e∈es,(js s(e.1,e.2)).Nodup)
    (he : ∀ e∈es,(js s(e.1,e.2)).toFinset=eligible s(e.1,e.2))
    (hh : ∀ e∈es,∀ j∈js s(e.1,e.2),host j=StoredSample.edgeSet (input s(e.1,e.2) j).edges)
    (hd : ∀ e∈es,∀ j∈js s(e.1,e.2),
      ((input s(e.1,e.2) j).draws.map StoredSample.edgeSet)=List.ofFn (a s(e.1,e.2) j)) :
    ValidSchedule Q w t eligible host (SampledGreedy.assignmentTape a) h
      (assignmentRecords w t js input es) E := by
  induction es generalizing E with
  | nil => trivial
  | cons e es ih =>
    refine ⟨rfl,?_,?_⟩
    · refine ⟨js s(e.1,e.2),input s(e.1,e.2),hj e (by simp),he e (by simp),rfl,?_,?_⟩
      · exact hh e (by simp)
      · intro j hm
        exact (hd e (by simp) j hm).symm
    · apply ih
      · intro d hm; exact hj d (List.mem_cons_of_mem e hm)
      · intro d hm; exact he d (List.mem_cons_of_mem e hm)
      · intro d hm; exact hh d (List.mem_cons_of_mem e hm)
      · intro d hm; exact hd d (List.mem_cons_of_mem e hm)
end LightEFTSpanners.StoredCandidates
