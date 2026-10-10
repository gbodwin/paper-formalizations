import LengthExpander.ParallelGreedy
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace LengthExpander
open Finset SimpleGraph
variable {V : Type*} [Fintype V]

noncomputable def monotoneWalks (G : SimpleGraph V) (index : Sym2 V → ℕ)
    (r : ℕ) (u v : V) : Finset (G.Walk u v) := by
  classical
  exact (G.finsetWalkLength r u v).filter (Increasing index)

@[simp] theorem mem_monotoneWalks {G : SimpleGraph V} {index : Sym2 V → ℕ}
    {r : ℕ} {u v : V} {p : G.Walk u v} :
    p ∈ monotoneWalks G index r u v ↔ p.length = r ∧ Increasing index p := by
  classical
  simp [monotoneWalks, mem_finsetWalkLength_iff]

theorem monotoneWalks_card_le_one {G : SimpleGraph V} {index : Sym2 V → ℕ}
    {s r : ℕ} (H : IsParallelGreedy G index s) (hr : 2*r ≤ s+1) (u v : V) :
    (monotoneWalks G index r u v).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro p hp q hq
  obtain ⟨hlp,hp⟩ := mem_monotoneWalks.mp hp
  obtain ⟨hlq,hq⟩ := mem_monotoneWalks.mp hq
  exact increasing_walk_unique H hr p q hp hq hlp hlq

noncomputable def monotoneCount (G : SimpleGraph V) (index : Sym2 V → ℕ) (r : ℕ) : ℕ :=
  ∑ u, ∑ v, (monotoneWalks G index r u v).card

/-- The exact n² upper bound used in Section 3.3. -/
theorem monotoneCount_le_square {G : SimpleGraph V} {index : Sym2 V → ℕ}
    {s r : ℕ} (H : IsParallelGreedy G index s) (hr : 2*r ≤ s+1) :
    monotoneCount G index r ≤ Fintype.card V ^ 2 := by
  calc
    monotoneCount G index r ≤ ∑ _u : V, ∑ _v : V, (1 : ℕ) := by
      exact sum_le_sum fun u _ => sum_le_sum fun v _ => monotoneWalks_card_le_one H hr u v
    _ = Fintype.card V ^ 2 := by simp [pow_two]

end LengthExpander
