import GreedyShortcuts.DAGBalance

/-! Large targets are already satisfied by the input graph, and the actual
algorithm inserts nothing. This removes the nontrivial-range restriction. -/
namespace GreedyShortcuts.DAGAllTargets

open DirectedPaths GraphGreedy
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem output_empty_of_card_le (G : V → V → Prop) (β : ℕ) (hβ : 1 ≤ β)
    (hn : Fintype.card V ≤ β) : output G β hβ = ∅ := by
  let A := system G β hβ
  have hz : A.potential (A.run 0).val = 0 := by
    apply (potential_eq_zero G β ∅).mpr
    intro e he
    exact (hopDist_le_card _ _ _).trans hn
  have hh := congrArg Subtype.val (A.run_stable 0 hz (candidates G).card)
  simpa [A,output] using hh

/-- The explicit DAG theorem for every positive integer target, including
β≥n where the actual output is empty. -/
theorem output_card_log_bound {G : V → V → Prop} (hG : CanonicalSegments.Acyclic G)
    (β : ℕ) (hβ : 1 ≤ β) (hn : 2 ≤ Fintype.card V) :
    ((output G β hβ).card : ℝ) ≤
      4*Real.logb 2 (Fintype.card V:ℝ) *
        (16385*(Fintype.card V:ℝ)^(3/(2:ℝ))/(β:ℝ)^(3/(2:ℝ)) +
          147456*(Fintype.card V:ℝ)^2/(β:ℝ)^3) := by
  by_cases hb : β ≤ Fintype.card V
  · exact DAGBalance.output_card_log_bound hG β hβ hb hn
  · rw [output_empty_of_card_le G β hβ (by omega)]
    simp only [Finset.card_empty,Nat.cast_zero]
    have hl : 0 ≤ Real.logb 2 (Fintype.card V:ℝ) := by
      exact (Nat.cast_nonneg (Nat.log 2 (Fintype.card V))).trans (Real.natLog_le_logb _ _)
    positivity

end GreedyShortcuts.DAGAllTargets
