import SlackSparsification.PlusSixComplete
import SlackSparsification.SubsetPlusTwoFold

/-! Integration of the accepted conditional +6 construction with the proved
uniform subset +2 existence theorem at constant 16. -/
namespace SlackSparsification
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Pairwise additive +6 existence with the subset +2 premise discharged.
This includes empty vertex types, empty demand sets, and disconnected graphs. -/
theorem exists_plus_six_complete_unconditional (G : SimpleGraph V) (P : Finset (V × V)) :
    ∃ H : SimpleGraph V, IsAdditiveSpanner G H P 6 ∧
      (H.edgeFinset.card : ℝ) ≤
        (106 * Fintype.card V / (1 - (3 / 4 : ℝ) ^ (1 / 4 : ℝ))) *
          (P.card : ℝ) ^ (1 / 4 : ℝ) := by
  simpa only [show (10 + 6 * (16 : ℝ)) = 106 by norm_num] using
    exists_plus_six_complete G 16 (by norm_num)
      (SubsetPlusTwo.uniform_subset_plus_two G) P

end SlackSparsification
