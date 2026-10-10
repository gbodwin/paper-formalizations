import LengthExpander.Metric
import LengthExpander.ParallelGreedy
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! Replace the edges of a demand-copy walk by actual short base-graph walks.
This is the metric component of the reversed matching-order argument. -/
namespace LengthExpander
open SimpleGraph
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- A walk of r copy edges, each representing distance at most h in the
base graph, represents base distance at most rh. No graph-homomorphism
assumption is used: a demand pair need not be a base edge. -/
theorem near_of_copy_walk (π : W → V) (w : EdgeLength V) (h : ℝ)
    {u v : W} (p : H.Walk u v)
    (hedge : ∀ x y, H.Adj x y → s(x,y) ∈ p.edges → Near G w h (π x) (π y)) :
    Near G w ((p.length : ℝ) * h) (π u) (π v) := by
  induction p with
  | nil => exact ⟨.nil,by simp⟩
  | @cons u z v huz p ih =>
    have hp := ih (fun x y hxy he => hedge x y hxy (by simp [he]))
    have hu := hedge u z huz (by simp)
    have ht := near_triangle hu hp
    convert ht using 1 <;> simp [Nat.cast_add,Nat.cast_one,add_mul,add_comm]

/-- A purely graph-and-metric criterion for the parallel-greedy property.
Each new edge is far, while every earlier labeled edge remains h-near in
that same metric. All distance claims use genuine base-graph walks. -/
theorem parallelGreedy_of_matching_metrics (π : W → V)
    (index : Sym2 W → ℕ) (s : ℕ) (h : ℝ) (hh : 0 ≤ h)
    (matching : MatchingLabels H index)
    (metric : Sym2 W → EdgeLength V)
    (far : ∀ u v, H.Adj u v → Far G (metric s(u,v)) (s*h) (π u) (π v))
    (near : ∀ u v, H.Adj u v → ∀ x y, H.Adj x y →
      index s(x,y) < index s(u,v) → Near G (metric s(u,v)) h (π x) (π y)) :
    IsParallelGreedy H index s := by
  refine ⟨matching,?_⟩
  intro u v huv p hlen hearlier
  have hn := near_of_copy_walk π (metric s(u,v)) h p
    (fun x y hxy he => near u v huv x y hxy (hearlier _ he))
  obtain ⟨q,hq⟩ := hn
  have hbound : (p.length : ℝ)*h ≤ (s : ℝ)*h :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hh
  exact (not_lt_of_ge (hq.trans hbound)) (far u v huv q)

end LengthExpander
