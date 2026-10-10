import GreedyShortcuts.ChainRelativeProgress
import GreedyShortcuts.FiniteThresholdDecay

/-! A proved weaker size bound for Algorithm 2. At the paper's cover/target
scales this has n^(4/3) times a logarithm, rather than the open near-linear
bound. The actual raw-sum greedy and stopping criterion are unchanged. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset DirectedPaths
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- A complete finite output-size theorem obtained from the proved quadratic
progress rate, with its dependence on chain count and target explicit. -/
theorem output_card_quadratic (D : ℕ) (hD : 3 ≤ D) :
    (T.output D (by omega)).card ≤ 
      (Nat.log 2 (Fintype.card V*Fintype.card I^2)+1)*
      (25*(Fintype.card V*Fintype.card I)/D+1) := by
  let A := T.algorithm D (by omega)
  apply A.final_card_of_relative_blocks _ _ (Nat.zero_lt_succ _)
  · intro S hbad
    have hr := T.step_relative_progress D hD S hbad
    have hcard := Nat.mul_le_mul_left 25 T.important_card
    have hblocks : 25*T.important.card/D+1 ≤ 
        25*(Fintype.card V*Fintype.card I)/D+1 :=
      Nat.add_le_add_right (Nat.div_le_div_right hcard) 1
    exact hr.trans (Nat.mul_le_mul_right _ hblocks)
  · exact (T.potential_le ∅).trans_lt (Nat.lt_pow_succ_log_self (by decide) _)

end GreedyShortcuts.ChainDistance.Context
