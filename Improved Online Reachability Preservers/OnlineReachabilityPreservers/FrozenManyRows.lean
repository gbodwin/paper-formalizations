import OnlineReachabilityPreservers.FrozenMatchedPartners
import OnlineReachabilityPreservers.FrozenSmallBudgets

/-! Original-average cleaning when the unrestricted maximum has enough rows. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "Before" => SourceAudit.BeforeIn

/-- Opposite-intersection pruning gains half an incidence per nonempty
row. At least one nonempty row per twelve incidences reaches the
threshold for frozen cleaning at the original widths. -/
theorem regularization_list_frozen_of_many_nonempty_paths {half : Bool} {k n p : ℕ}
    (cutoff : k = 4 ∨ (k = 6 ∧ half = false)) (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (many : (∑ i, (paths i).length) ≤ 12*(univ.filter fun i => paths i ≠ []).card) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 288*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  have three : 3 ≤ k := by rcases cutoff with rfl | ⟨rfl, _⟩ <;> decide
  have free : HalfBridgeFree (Before paths) k := by
    cases half
    · exact (show BridgeFree (Before paths) k from allowed).halfFree
    · exact allowed
  have retained := removeOppositeIntersections_mass_with_nonempty_paths simple free three
  exact regularization_list_frozen_of_large_unique_sublists cutoff paths (removeOppositeIntersections paths)
    simple allowed (removeOppositeIntersections_sublist paths)
    (fun {_ _ _ _} different xi xj yi yj =>
      removeOppositeIntersections_unique simple free (by omega) different xi xj yi yj)
    hn hp dense long (by omega)

/-- A sufficiently large path budget makes the unrestricted extremum cleanable
at the original averages. The ordered-pair bound gives mean path length
at most twelve, and every indexed row in a maximizing family is nonempty. -/
theorem localOrderExtremal_frozen_of_large_path_budget (n p k : ℕ) (half : Bool)
    (cutoff : k = 4 ∨ (k = 6 ∧ half = false)) (hn : 0 < n) (hp : 0 < p) (large : n*n-n ≤ 66*p) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ localOrderAdmissible half k paths ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → localOrderAdmissible half k other →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
        M ≤ 288*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨paths, simple, allowed, maximal, dense, long⟩ := localOrderExtremal_isDense n p k half hn hp
  let M := ∑ i, (paths i).length
  have two : 2 ≤ k := by rcases cutoff with rfl | ⟨rfl, _⟩ <;> decide
  have free : HalfBridgeFree (Before paths) k := by
    cases half
    · exact (show BridgeFree (Before paths) k from allowed).halfFree
    · exact allowed
  have square : M^2 ≤ p*(2*(n*n-n)+M) := listMass_square_le_halfTwo paths simple free two
  have cap : M ≤ 12*p := by
    by_contra! tooLarge
    have limit : M^2 ≤ p*(132*p+M) := square.trans (Nat.mul_le_mul_left _ (by omega))
    have limitReal : (M:ℝ)^2 ≤ (p:ℝ)*(132*(p:ℝ)+M) := by exact_mod_cast limit
    have above : 0 < (M:ℝ)-12*p := sub_pos.mpr (by exact_mod_cast tooLarge)
    have pPos : (0:ℝ) < p := by exact_mod_cast hp
    have gain : 0 < (M:ℝ)+11*p := by positivity
    nlinarith only [mul_pos above gain, limitReal]
  have nonempty := localOrderMaximizer_nonempty hn paths allowed maximal simple
  have support : (univ.filter fun i => paths i ≠ []).card = p := by simp [nonempty]
  refine ⟨paths, simple, allowed, maximal, regularization_list_frozen_of_many_nonempty_paths cutoff paths simple allowed
    hn hp dense long ?_⟩
  rw [support]
  exact cap

end OnlineReachabilityPreservers
