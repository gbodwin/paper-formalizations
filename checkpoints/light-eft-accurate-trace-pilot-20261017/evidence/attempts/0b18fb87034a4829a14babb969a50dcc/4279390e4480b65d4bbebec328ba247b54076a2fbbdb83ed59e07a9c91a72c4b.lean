import LightEFTSpanners.EmpiricalVotingGreedy
namespace LightEFTSpanners.SampledGreedy.TraceComparison
open Finset
variable {V J : Type*} [DecidableEq V]
attribute [local instance] Classical.propDecidable
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

theorem trace_iff_prior (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ) (f : ℕ)
    (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V)) (tape : Tape V J)
    (h : ℕ) (es : List (Sym2 V)) :
    AccurateTrace Q w t f eligible host tape h es ↔
      LightEFTSpanners.SampledGreedy.AccurateTrace Q w t f eligible host tape h es := by
  induction es with
  | nil => exact Iff.rfl
  | cons e es ih => exact and_congr ih Iff.rfl
#print axioms trace_iff_prior
end LightEFTSpanners.SampledGreedy.TraceComparison
