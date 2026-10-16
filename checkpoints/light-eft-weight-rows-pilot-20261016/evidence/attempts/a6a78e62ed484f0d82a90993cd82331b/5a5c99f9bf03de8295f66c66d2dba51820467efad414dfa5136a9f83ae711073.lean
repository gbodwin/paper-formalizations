import LightEFTSpanners.EmpiricalVotingGreedy

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset
variable {V J : Type*} [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- A finite sample assignment. The actual tape ignores its state argument;
the test itself clips these original identities to the reached graph. -/
abbrev Assignment (V J : Type*) (m : ℕ) := Sym2 V → J → Fin m → Finset (Sym2 V)

def assignmentTape {m : ℕ} (a : Assignment V J m) : Tape V J :=
  fun _ e j => List.ofFn (a e j)

 theorem edges_congr_on (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ)
    (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V))
    (a b : Tape V J) (h : ℕ) (l : List (Sym2 V))
    (hab : ∀ E e, e∈l → ∀ j, a E e j=b E e j) :
    edges Q w t eligible host a h l=edges Q w t eligible host b h l := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    have he := ih (fun E d hd j => hab E d (List.mem_cons_of_mem e hd) j)
    have hv (E) : votes Q w t eligible host a E e=votes Q w t eligible host b E e := by
      unfold votes
      congr 1
      funext j
      rw [hab E e (List.mem_cons_self) j]
    simp only [edges,he,hv]

 theorem accurate_congr_on (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ) (f : ℕ)
    (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V))
    (a b : Tape V J) (h : ℕ) (l : List (Sym2 V))
    (hab : ∀ E e, e∈l → ∀ j, a E e j=b E e j) :
    AccurateTrace Q w t f eligible host a h l ↔ AccurateTrace Q w t f eligible host b h l := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    have htail : ∀ E d,d∈es → ∀ j,a E d j=b E d j :=
      fun E d hd j => hab E d (List.mem_cons_of_mem e hd) j
    have he := edges_congr_on Q w t eligible host a b h es htail
    simp only [AccurateTrace,ih htail,he]
    constructor <;> rintro ⟨ht,hj⟩ <;> refine ⟨ht,?_⟩ <;> intro j hje
    · simpa only [hab _ e (List.mem_cons_self) j] using hj j hje
    · simpa only [hab _ e (List.mem_cons_self) j] using hj j hje

/-- Replacing the current candidate's samples leaves every earlier reached
state unchanged, because the sorted candidate input has no repetitions. -/
theorem assignment_update_prefix {m : ℕ} (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ)
    (t : ℝ) (f : ℕ) (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V))
    (a : Assignment V J m) (e : Sym2 V) (b : J → Fin m → Finset (Sym2 V))
    (h : ℕ) (l : List (Sym2 V)) (he : e∉l) :
    edges Q w t eligible host (assignmentTape (Function.update a e b)) h l=
      edges Q w t eligible host (assignmentTape a) h l ∧
    (AccurateTrace Q w t f eligible host (assignmentTape (Function.update a e b)) h l ↔
      AccurateTrace Q w t f eligible host (assignmentTape a) h l) := by
  have ha : ∀ E d,d∈l → ∀ j,assignmentTape (Function.update a e b) E d j=assignmentTape a E d j := by
    intro E d hd j
    have hde : d≠e := fun hx => he (hx ▸ hd)
    simp [assignmentTape,Function.update_of_ne hde]
  exact ⟨edges_congr_on Q w t eligible host _ _ h l ha,
    accurate_congr_on Q w t f eligible host _ _ h l ha⟩
end LightEFTSpanners.SampledGreedy
