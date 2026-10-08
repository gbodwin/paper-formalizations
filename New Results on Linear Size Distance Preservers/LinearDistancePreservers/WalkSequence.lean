import LinearDistancePreservers.NativeWalkBridge
import Mathlib.Data.List.OfFn

/-! Bridges between indexed vertex sequences, native graph walks, and the
list-walk distance definition. These retain every vertex and every step. -/
namespace LinearDistancePreservers
set_option backward.isDefEq.respectTransparency.types false
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

def walkOfSequence : {m : ℕ} → (v : Fin (m+1) → V) →
    (∀ i : Fin m, G.Adj (v i.castSucc) (v i.succ)) → G.Walk (v 0) (v (Fin.last m))
  | 0, v, _ => .nil
  | m+1, v, h => .cons (h 0) (walkOfSequence (fun i => v i.succ) (fun i => h i.succ))

@[simp] theorem support_walkOfSequence {m : ℕ} (v : Fin (m+1) → V)
    (h : ∀ i : Fin m, G.Adj (v i.castSucc) (v i.succ)) :
    (walkOfSequence v h).support = List.ofFn v := by
  induction m with
  | zero => simp [walkOfSequence, List.ofFn_succ]
  | succ m ih =>
    rw [walkOfSequence, SimpleGraph.Walk.support_cons, ih]
    exact List.ofFn_succ.symm

@[simp] theorem length_walkOfSequence {m : ℕ} (v : Fin (m+1) → V)
    (h : ∀ i : Fin m, G.Adj (v i.castSucc) (v i.succ)) :
    (walkOfSequence v h).length = m := by
  have := (walkOfSequence v h).length_support
  simpa using this.symm

theorem support_eq_ofFn {s t : V} (p : G.Walk s t) :
    p.support = List.ofFn (fun i : Fin (p.length+1) => p.getVert i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    rw [List.getElem_ofFn, p.support_getElem_eq_getVert]

/-- A list walk in a simple graph is a native walk with exactly that list
as support. No loop erasure or path shortening occurs in this bridge. -/
theorem native_of_list_walk {s t : V} {l : List V}
    (h : WeightedDigraph.IsWalk G.Adj s t l) :
    ∃ p : G.Walk s t, p.support = l := by
  induction l generalizing s with
  | nil => cases h.1
  | cons a l ih =>
    have ha : a = s := by simpa using h.1
    subst s
    cases l with
    | nil =>
      have ht : a = t := by simpa using h.2.1
      subst t
      exact ⟨.nil, rfl⟩
    | cons b l =>
      have hab : G.Adj a b := h.2.2 (a,b) (by simp)
      have htail : WeightedDigraph.IsWalk G.Adj b t (b :: l) := by
        refine ⟨rfl, by simpa using h.2.1, ?_⟩
        intro e he
        exact h.2.2 e (by simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]; exact Or.inr he)
      obtain ⟨p, hp⟩ := ih htail
      exact ⟨.cons hab p, by simp [hp]⟩

/-- Native walk costs can be computed by indexing the consecutive vertices. -/
theorem darts_sum_eq {M : Type*} [AddCommMonoid M] (f : V → V → M)
    {s t : V} (p : G.Walk s t) :
    (p.darts.map fun d => f d.fst d.snd).sum =
      ∑ i : Fin p.length, f (p.getVert i.val) (p.getVert (i.val+1)) := by
  induction p with
  | nil => exact (Fin.sum_univ_zero _).symm
  | cons h p ih =>
    rw [SimpleGraph.Walk.length_cons, Fin.sum_univ_succ]
    simpa only [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons,
      SimpleGraph.Walk.getVert_zero, SimpleGraph.Walk.getVert_cons_succ,
      Fin.val_zero, Fin.val_succ] using congrArg (fun z => f _ _ + z) ih

end LinearDistancePreservers
