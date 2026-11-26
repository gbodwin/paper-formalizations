import OnlineReachabilityPreservers.SteinerBinaryEarlyPolynomialWork
import OnlineReachabilityPreservers.SteinerFinTraceReplayWork

/-! Bound the complete measured replay using only input sizes. -/

namespace OnlineReachabilityPreservers

/-- The full replay allowance depends on the original vertex and arc
counts, raw list length, forest height, and demand count. -/
def finSteinerBinaryPhasesReplaySizeBudget (n m raw height p : ℕ) : ℕ :=
  finSteinerMeasuredThinReplayWorkBudget n m raw height p+(p+1)*steinerBinaryLateCallWorkBudget n m p+2+
    finSteinerWeightPlanWorkPolynomial n height+(7*n+12)+7+
    (p+1)*finSteinerBinaryEarlySearchWorkBudget n m height p+
    (p+1)^3*finSteinerBinaryEarlyMetricSizeBudget n height (earlySeedArrayReadWordBudget height) p

theorem finSteinerBinaryPhasesReplayWorkBudget_le_size {n : ℕ} (G : Arcs (Fin n)) (raw height p : ℕ) :
    finSteinerBinaryPhasesReplayWorkBudget G raw height p ≤
      finSteinerBinaryPhasesReplaySizeBudget n G.card raw height p := by
  unfold finSteinerBinaryPhasesReplaySizeBudget finSteinerBinaryPhasesReplayWorkBudget
  dsimp only
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (finSteinerBinaryEarlyMetricWorkBudget_le_size G height _ p)) _

/-- Every feasible prefix matches the fixed-budget reference. The
evaluation count is unchanged and the eight recorded work fields admit a
single uniform allowance in the input sizes. -/
theorem completeFinSteinerReplayWithBinaryPhasesWork_input_sizes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithBinaryPhasesWork G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      out.2.2 = (completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D).2.2 ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        finSteinerBinaryPhasesReplaySizeBudget n m raw.length height D.length := by
  obtain ⟨prefixes,count⟩ := completeFinSteinerReplayWithBinaryPhasesWork_prefixes G raw same height m hm bits D feasible
  have size := finSteinerBinaryPhasesReplayWorkBudget_le_size G raw.length height D.length
  rw [← hm] at size
  exact ⟨prefixes,count,(completeFinSteinerReplayWithBinaryPhasesWork_tally_le G raw same height m hm bits D feasible).trans size⟩

end OnlineReachabilityPreservers
