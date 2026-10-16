import LightEFTSpanners.VotingGreedyCorrectness
import LightEFTSpanners.Blocking

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset LightSpanners
variable {V J : Type*} [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Literal accepted-edge records, including all hosts that voted at that time.
The tape and optimization rule are exactly those of `edges`. -/
noncomputable def history (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ)
    (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V)) (tape : Tape V J)
    (h : ℕ) : List (Sym2 V) → List (Sym2 V × Finset J)
  | [] => []
  | e::es => let E := edges Q w t eligible host tape h es
             let A := votes Q w t eligible host tape E e
             if h≤A.card then (e,A)::history Q w t eligible host tape h es
             else history Q w t eligible host tape h es

 theorem history_sublist (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ)
    (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V)) (tape : Tape V J)
    (h : ℕ) (l : List (Sym2 V)) :
    ((history Q w t eligible host tape h l).map Prod.fst).Sublist l := by
  induction l with
  | nil => exact List.Sublist.refl _
  | cons e es ih =>
    simp only [history]
    split_ifs
    · exact ih.cons_cons e
    · exact ih.cons e

/-- Compressing rejected steps leaves exactly the actual current output. -/
theorem history_edges (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ)
    (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V)) (tape : Tape V J)
    (h : ℕ) (l : List (Sym2 V)) :
    edges Q w t eligible host tape h l=
      Q∪((history Q w t eligible host tape h l).map Prod.fst).toFinset := by
  induction l with
  | nil => simp [edges,history]
  | cons e es ih =>
    simp only [edges,history]
    split_ifs <;> simp_all [union_insert]

/-- Each real accepted record has enough literal voters and their derived true
probabilities. Its prefix is the actual earlier accepted-edge set. -/
def ApprovedHistory (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ) (f h : ℕ)
    (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V)) :
    List (Sym2 V × Finset J) → Prop
  | [] => True
  | (e,A)::rs => ApprovedHistory Q w t f h eligible host rs ∧ A⊆eligible e ∧ h≤A.card ∧
      ∀ j∈A,1/4≤testProbability Q (Q∪(rs.map Prod.fst).toFinset) (host j) w t f e

 theorem history_approved (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ)
    (f h : ℕ) (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V))
    (tape : Tape V J) (l : List (Sym2 V))
    (hacc : AccurateTrace Q w t f eligible host tape h l) :
    ApprovedHistory Q w t f h eligible host (history Q w t eligible host tape h l) := by
  induction l with
  | nil => trivial
  | cons e es ih =>
    obtain ⟨hprev,hcur⟩ := hacc
    simp only [history]
    split_ifs with hv
    · refine ⟨ih hprev,filter_subset _ _,hv,?_⟩
      intro j hj
      obtain ⟨hj,hvote⟩ := mem_filter.mp hj
      have hh := voter_true_probability Q (edges Q w t eligible host tape h es) (host j)
        w t f e (tape (edges Q w t eligible host tape h es) e j) hvote (hcur j hj)
      simpa only [history_edges] using hh
    · exact ih hprev
end LightEFTSpanners.SampledGreedy
