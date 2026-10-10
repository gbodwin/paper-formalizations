import DirectedFlowCutGap.BinaryHeavyPrefix
import DirectedFlowCutGap.FiniteRoundingCertificate
import DirectedFlowCutGap.StatefulHeavyValidity
import DirectedFlowCutGap.StatefulHeavyRate
import DirectedFlowCutGap.StatefulHeavyPathwise

/-! The original weighted heavy query is driven by one finite independent
bit prefix. The same complete output and ledger carry original cut validity,
source-shaped quality and the established declared-operation certificate.
Materializing raw rational arrays, building the prefix/fuel and simulating
physical storage/runtime remain separate from this finite law. -/
namespace DirectedFlowCutGap.FiniteHeavyCertificate
noncomputable section
open EncodedUnitCostReplication BinarySamplerMetadata

abbrev executePrefix {n : ℕ} (D : Input n) (extra : ℕ) (state : Ledger) (xs : List (Fin 2)) :=
  (((BinaryHeavyPrefix.run BinaryTrackedPrefix.next D extra).run state).run xs).1

/-- Every supplied stream, including an exhausted one, returns a valid
original cut. The zero fallback is covered by the actual fair-bit support. -/
theorem pathwise_valid {n : ℕ} (D : Input n) (extra : ℕ) (state : Ledger) (xs : List (Fin 2)) :
    IsIntegralCut D.graph (selectedSet (executePrefix D extra state xs).1.mask)
      (thresholdDemands D.graph D.weight) :=
  StatefulHeavyValidity.heavy_valid D extra state
    (BinaryHeavyPrefix.actual_supported D extra state xs)

/-- All declared charges, including bad-quality paths, belong to this same
finite-list execution. No sampling success condition is required. -/
theorem pathwise_charge {n : ℕ} (D : Input n) (extra : ℕ) (state : Ledger) (xs : List (Fin 2)) :
    (executePrefix D extra state xs).2.operations=
        state.operations+(executePrefix D extra state xs).1.sampling ∧
      (executePrefix D extra state xs).1.operations≤StatefulHeavyQuery.chargeBound D extra state :=
  StatefulHeavyPathwise.heavy_charge D extra state
    (BinaryHeavyPrefix.actual_supported D extra state xs)

/-- One uniform constant works for all inputs and entering ledgers. Quality,
validity and declared charge are an event on that same finite-stream result. -/
theorem uniform_confidence :
    ∀ δ : ℝ,0<δ → ∃ K : ℝ,0<K ∧
      ∀ (n : ℕ) (_hn : 0<n) (D : Input n) (k : ℕ) (state : Ledger),
      ((FiniteBinaryPrefix.prefixLaw (BinaryHeavyPrefix.budget D (3*k))).toOuterMeasure
        {xs | ¬StatefulHeavyRate.Good D K δ (3*k) state
          (executePrefix D (3*k) state xs)}).toReal ≤ ((1:ℝ)/2)^k := by
  intro δ hδ
  obtain ⟨K,hK,hgood⟩ := StatefulHeavyRate.uniform_confidence δ hδ
  refine ⟨K,hK,?_⟩
  intro n hn D k state
  have h := hgood n hn D k state
  rw [← BinaryHeavyPrefix.output_law D (3*k) state,PMF.toOuterMeasure_map_apply] at h
  exact h

end
end DirectedFlowCutGap.FiniteHeavyCertificate
