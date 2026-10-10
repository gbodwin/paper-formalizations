import GreedyShortcuts.DirectedMap

/-! Native bounded walk substitution for cited preprocessing reductions.
A relation on a smaller vertex set is expanded into actual original-graph
walks. No reachability or hopbound conclusion is imported as an axiom. -/
namespace GreedyShortcuts.DirectedLift

open SimpleGraph DirectedPaths
open LinearDistancePreservers.ConsistentTiebreaking
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem edge_walk {G : V → V → Prop} {s t : V} (h : G s t) :
    ∃ p : DWalk s t,Allowed G p ∧ p.length ≤ 1 := by
  by_cases he : s = t
  · subst t
    exact ⟨.nil,allowed_nil G s,by simp⟩
  · exact ⟨.cons (by simpa using he) .nil,by simp [h],by simp⟩

/-- Substitute a bounded actual G-walk for every directed K-edge. -/
theorem bounded (f : W → V) {G : V → V → Prop} {K : W → W → Prop}
    (L : ℕ) (hstep : ∀ a b,K a b → ∃ q : DWalk (f a) (f b),Allowed G q ∧ q.length ≤ L)
    {s t : W} (p : DWalk s t) (hp : Allowed K p) :
    ∃ q : DWalk (f s) (f t),Allowed G q ∧ q.length ≤ L*p.length := by
  induction p with
  | nil => exact ⟨.nil,allowed_nil _ _,by simp⟩
  | @cons s u t ha p ih =>
    have hh := (allowed_cons K ha p).mp hp
    obtain ⟨q,hq,hqL⟩ := hstep s u hh.1
    obtain ⟨r,hr,hrL⟩ := ih hh.2
    refine ⟨q.append r,(allowed_append G q r).mpr ⟨hq,hr⟩,?_⟩
    simp only [Walk.length_append,Walk.length_cons,Nat.mul_add,Nat.mul_one]
    omega

/-- Reachability alone also lifts, with no injectivity requirement on f. -/
theorem reachable (f : W → V) {G : V → V → Prop} {K : W → W → Prop}
    (hstep : ∀ a b,K a b → Reachable G (f a) (f b)) {s t : W}
    (hr : Reachable K s t) : Reachable G (f s) (f t) := by
  obtain ⟨p,hp⟩ := hr
  induction p with
  | nil => exact reachable_refl _ _
  | @cons s u t ha p ih =>
    have hh := (allowed_cons K ha p).mp hp
    exact reachable_trans (hstep s u hh.1) (ih hh.2)

end GreedyShortcuts.DirectedLift
