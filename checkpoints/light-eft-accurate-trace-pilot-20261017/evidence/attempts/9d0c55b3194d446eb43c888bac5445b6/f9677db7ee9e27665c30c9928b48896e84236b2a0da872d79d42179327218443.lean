import LightEFTSpanners.AlgorithmSampleProbability

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset LightSpanners
variable {V J : Type*} [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Every entry is an actual finite list of sampled edge sets at the queried
current state, candidate and host. Random generation is a separate obligation. -/
abbrev Tape (V J : Type*) := Finset (Sym2 V) → Sym2 V → J → List (Finset (Sym2 V))

/-- The literal fraction of samples failing the weighted-distance edge test.
An empty list has the explicit total real-division value zero. -/
noncomputable def estimate (Q E T : Finset (Sym2 V)) (w : Sym2 V → ℝ)
    (t : ℝ) (e : Sym2 V) (draws : List (Finset (Sym2 V))) : ℝ :=
  ((draws.filter fun S => decide (¬Covered (testSample Q E T S) w t e)).length:ℝ)/draws.length

noncomputable def votes (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ)
    (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V)) (tape : Tape V J)
    (E : Finset (Sym2 V)) (e : Sym2 V) : Finset J :=
  (eligible e).filter fun j => 3/8≤estimate Q E (host j) w t e (tape E e j)

/-- Literal threshold-voting edge recursion. h=1 has the same insertion test
as Algorithm2's first accepting host; integer h gives repaired Algorithm3.
The tail is processed first, matching the nonincreasing sorted input convention. -/
noncomputable def edges (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ)
    (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V)) (tape : Tape V J)
    (h : ℕ) : List (Sym2 V) → Finset (Sym2 V)
  | [] => Q
  | e::es => let E := edges Q w t eligible host tape h es
             if h≤(votes Q w t eligible host tape E e).card then insert e E else E

/-- Simultaneous estimator accuracy on the actual recursively reached states.
This does not postulate accuracy at states that the execution never visits. -/
def AccurateTrace (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ) (f : ℕ)
    (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V)) (tape : Tape V J)
    (h : ℕ) : List (Sym2 V) → Prop :=
  List.rec (motive := fun _ => Prop) True
    (fun e es next => next ∧ ∀ j∈eligible e,
      |estimate Q (edges Q w t eligible host tape h es) (host j) w t e
        (tape (edges Q w t eligible host tape h es) e j)-
        testProbability Q (edges Q w t eligible host tape h es) (host j) w t f e|≤1/8)

theorem AccurateTrace_nil (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ) (f : ℕ)
    (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V)) (tape : Tape V J)
    (h : ℕ) : AccurateTrace Q w t f eligible host tape h [] ↔ True := Iff.rfl

theorem AccurateTrace_cons (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ) (f : ℕ)
    (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V)) (tape : Tape V J)
    (h : ℕ) (e : Sym2 V) (es : List (Sym2 V)) :
    AccurateTrace Q w t f eligible host tape h (e::es) ↔
      AccurateTrace Q w t f eligible host tape h es ∧ ∀ j∈eligible e,
        |estimate Q (edges Q w t eligible host tape h es) (host j) w t e
          (tape (edges Q w t eligible host tape h es) e j)-
          testProbability Q (edges Q w t eligible host tape h es) (host j) w t f e|≤1/8 := Iff.rfl

-- Preserve constructor-wise unfolding for existing simp [AccurateTrace] proofs.
attribute [eqns AccurateTrace_nil AccurateTrace_cons] AccurateTrace

theorem seed_subset (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ)
    (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V)) (tape : Tape V J)
    (h : ℕ) (l : List (Sym2 V)) : Q⊆edges Q w t eligible host tape h l := by
  induction l with
  | nil => exact subset_rfl
  | cons e es ih =>
    simp only [edges]
    split_ifs
    · exact ih.trans (subset_insert _ _)
    · exact ih

theorem subset_input (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ)
    (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V)) (tape : Tape V J)
    (h : ℕ) (l : List (Sym2 V)) : edges Q w t eligible host tape h l⊆Q∪l.toFinset := by
  induction l with
  | nil => simp [edges]
  | cons e es ih =>
    simp only [edges]
    split_ifs
    · intro d hd
      rcases mem_insert.mp hd with rfl | hd
      · simp
      · have hh := ih hd
        simp only [mem_union,List.mem_toFinset] at *
        exact hh.elim Or.inl (fun hh => Or.inr (List.mem_cons_of_mem e hh))
    · exact ih.trans (by intro d hd;simpa using Or.inr hd)

 theorem one_vote_iff (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ)
    (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V)) (tape : Tape V J)
    (E : Finset (Sym2 V)) (e : Sym2 V) :
    1≤(votes Q w t eligible host tape E e).card ↔
      ∃ j∈eligible e,3/8≤estimate Q E (host j) w t e (tape E e j) := by
  rw [Nat.one_le_iff_ne_zero,card_ne_zero]
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨j,(mem_filter.mp hj).1,(mem_filter.mp hj).2⟩
  · rintro ⟨j,hj,hp⟩
    exact ⟨j,mem_filter.mpr ⟨hj,hp⟩⟩

 theorem voter_true_probability (Q E T : Finset (Sym2 V)) (w : Sym2 V → ℝ)
    (t : ℝ) (f : ℕ) (e : Sym2 V) (draws : List (Finset (Sym2 V)))
    (hvote : 3/8≤estimate Q E T w t e draws)
    (hacc : |estimate Q E T w t e draws-testProbability Q E T w t f e|≤1/8) :
    1/4≤testProbability Q E T w t f e :=
  BlockerSampling.accepted_edge_probability hvote hacc
end LightEFTSpanners.SampledGreedy
