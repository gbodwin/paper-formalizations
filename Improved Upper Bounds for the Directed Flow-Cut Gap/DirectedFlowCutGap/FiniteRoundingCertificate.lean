import DirectedFlowCutGap.BinaryRepeatedPrefix
import DirectedFlowCutGap.StatefulRoundingCertificate

/-! Joint validity, full repeated declared charge and selected-size confidence
for the actual finite-list bit reader. The complete output/ledger law is used;
no independence or cost/output decoupling is introduced. Prefix generation,
raw-input/fuel preparation and physical-machine simulation remain separate. -/
namespace DirectedFlowCutGap.FiniteRoundingCertificate
noncomputable section
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
open BinaryArithmetic BinarySamplerMetadata BinaryRetainedTape RetainedGridState
open StatefulRoundingCertificate
variable {n L : ℕ}

abbrev executePrefix (fuel cutoff : Bits) (hcut : value cutoff=L)
    (adjacency : PairFlags n) (hL : 0<L) (extra : ℕ) (state : Ledger) (xs : List (Fin 2)) :=
  (((EncodedRoundingRepetition.run (callback BinaryTrackedPrefix.next fuel cutoff hcut hL)
    adjacency hL extra).run state).run xs).1

/-- Even an exhausted supplied list follows supported zero-bit fallbacks, so
validity and the same-record declared bounds hold for every actual execution. -/
theorem pathwise [NeZero L] (fuel cutoff : Bits) (hcut : value cutoff=L)
    (adjacency : PairFlags n) (hL : 0<L) (extra : ℕ) (state : Ledger) (xs : List (Fin 2)) :
    Certificate fuel cutoff adjacency L extra state
      (executePrefix fuel cutoff hcut adjacency hL extra state xs) :=
  StatefulRoundingCertificate.run_certificate fuel cutoff hcut adjacency hL extra state
    (BinaryRepeatedPrefix.actual_supported fuel cutoff hcut adjacency hL extra state xs)

/-- The constant precedes graph, input threshold, ledger and confidence.
The event is evaluated on one actual output obtained from one finite prefix. -/
theorem uniform_confidence :
    ∀ ε : ℝ,0<ε → ∃ C : ℝ,0<C ∧
      ∀ (n L : ℕ) [NeZero L] (fuel cutoff : Bits) (hcut : value cutoff=L)
        (adjacency : PairFlags n) (hL : 0<L) (k : ℕ) (state : Ledger)
        (_hfuel : FairBitConfidence.trials (AllRegimeBoundedTapeLaw.drawBudget n) 2≤value fuel),
        let threshold := Nat.ceil (2*max 1
          (C*(n:ℝ)^ε*AdaptiveCost.sizeFactor (Fin n) (L:ℝ≥0)))
        ((FiniteBinaryPrefix.prefixLaw ((3*k+1)*BinaryEntryTrees.budget n fuel cutoff)).toOuterMeasure
          {xs | ¬(Certificate fuel cutoff adjacency L (3*k) state
              (executePrefix fuel cutoff hcut adjacency hL (3*k) state xs) ∧
            (executePrefix fuel cutoff hcut adjacency hL (3*k) state xs).1.selected.vertices.length≤threshold)}).toReal
          ≤ ((1:ℝ)/2)^k := by
  intro ε hε
  obtain ⟨C,hC,hjoint⟩ := StatefulRoundingCertificate.uniform_joint_confidence ε hε
  refine ⟨C,hC,?_⟩
  intro n L _ fuel cutoff hcut adjacency hL k state hfuel
  have h := hjoint n L fuel cutoff hcut adjacency hL k state hfuel
  dsimp only [] at h ⊢
  rw [← BinaryRepeatedPrefix.output_law fuel cutoff hcut adjacency hL (3*k) state,
    PMF.toOuterMeasure_map_apply] at h
  exact h

end
end DirectedFlowCutGap.FiniteRoundingCertificate
