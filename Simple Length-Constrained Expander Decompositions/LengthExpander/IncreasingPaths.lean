import LengthExpander.HikerCount
import LengthExpander.DispersionCount

namespace LengthExpander
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
attribute [local instance] Classical.propDecidable

/-- Strictly increasing labels are inherited by every contiguous subwalk. -/
theorem increasing_of_isSubwalk {index : Sym2 V → ℕ} {u v a b : V}
    {p : G.Walk u v} {q : G.Walk a b} (hp : Increasing index p)
    (hqp : q.IsSubwalk p) : Increasing index q := by
  exact List.Pairwise.sublist (hqp.edges_isInfix.sublist.map index) hp

/-- Earlier-walk exclusion forbids every nonempty short increasing closed walk. -/
theorem increasing_closed_nil {index : Sym2 V → ℕ} {s : ℕ}
    (H : EarlierFar G index s) {u : V} (p : G.Walk u u)
    (hp : Increasing index p) (hlen : p.length ≤ s+1) : p.Nil := by
  by_contra hn
  have hpos : 0 < p.length := Walk.not_nil_iff_lt_length.mp hn
  obtain ⟨a,q,ha,hq,rfl⟩ := exists_concat_of_length_succ
    (p := p) (r := p.length-1) (by omega)
  apply H a u ha q.reverse
  · simp only [Walk.length_reverse, Walk.length_concat] at *
    omega
  · intro e he
    exact (increasing_concat_iff q ha).mp hp |>.2 e (by simpa using he)

/-- At the paper's relevant lengths, monotone walks really are simple paths.
Long hiker trajectories need not be simple; the short prefix is what is used. -/
theorem increasing_isPath {index : Sym2 V → ℕ} {s : ℕ}
    (H : EarlierFar G index s) {u v : V} (p : G.Walk u v)
    (hp : Increasing index p) (hlen : p.length ≤ s+1) : p.IsPath := by
  apply Walk.isPath_iff_isSubwalk_imp_nil.mpr
  intro a q hqp
  exact increasing_closed_nil H q (increasing_of_isSubwalk hp hqp)
    ((Walk.length_le_of_isSubwalk hqp).trans hlen)

/-- Lemma 3.4 in the paper's path convention, with the precise integer threshold. -/
theorem weak_counting_path [Fintype V] [Nonempty V] {index : Sym2 V → ℕ}
    {s : ℕ} (H : IsParallelGreedy G index s) (r : ℕ)
    (hr : r ≤ s+1) (hm : Fintype.card V * r ≤ 2 * G.edgeFinset.card) :
    ∃ u v, ∃ p : G.Walk u v, Increasing index p ∧ p.IsPath ∧ p.length = r := by
  obtain ⟨u,v,p,hp,hlen⟩ := weak_counting_walk H.matching r hm
  exact ⟨u,v,p,hp,increasing_isPath H.earlierFar p hp (hlen ▸ hr),hlen⟩

end LengthExpander
