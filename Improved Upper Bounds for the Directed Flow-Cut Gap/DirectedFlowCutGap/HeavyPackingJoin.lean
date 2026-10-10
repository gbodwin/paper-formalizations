import DirectedFlowCutGap.HeavyCutProvider
import DirectedFlowCutGap.BinaryWeightedPackingConfidence
import DirectedFlowCutGap.FairBitConfidence

/-! The actual heavy-query pointwise contract feeds the existing adaptive
binary packing and final original-weight selection. Every provider invocation
uses a fresh local physical ledger, whose metadata is retained in its answer;
this is not a shared-ledger stateful controller. Raw-array materialization,
confidence-word preparation and physical storage/runtime remain unpriced here.
The nonempty-cut branch is explicit. -/
namespace DirectedFlowCutGap.HeavyPackingJoin
noncomputable section
open scoped BigOperators ENNReal NNReal
open BinaryArithmetic BinaryFractionalRows BinarySamplerMetadata
open BinaryZeroAvoidingProvider BinaryZeroAvoidingSelector HeavyCutProvider

/-- Positive original support is always a valid threshold cut. -/
theorem support_valid {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n) :
    SupportValid w (columns adjacency w) := by
  have he : ZeroAvoidingSelector.positiveSupport (tableValue w) =
      ZeroAvoidingSelector.vertexSupport (input adjacency w w).weight := by
    ext i
    simp only [ZeroAvoidingSelector.mem_positiveSupport,ZeroAvoidingSelector.vertexSupport,
      Finset.mem_filter,Finset.mem_univ,true_and]
    rw [← input_weight adjacency w w i]
    norm_cast
  change IsIntegralCut (input adjacency w w).graph
    (ZeroAvoidingSelector.positiveSupport (tableValue w))
    (thresholdDemands (input adjacency w w).graph (input adjacency w w).weight)
  rw [he]
  exact ZeroAvoidingSelector.vertexSupport_threshold _ _

/-- Confidence grows with both the bounded number of adaptive calls and the
original rational-input width. This numerical quantity is explicit. -/
def oracleExponent (n B : ℕ) : ℕ :=
  FairBitConfidence.trials (3*n^2+1) (WeightedFailureBudget.exponent n B+1)

theorem oracle_budget (n B : ℕ) :
    (3*n^2+1 : ℕ)*((1:ℝ)/2)^(oracleExponent n B) ≤
      WeightedFailureBudget.tolerance n B/2 := by
  have h := FairBitConfidence.accumulated_failure (3*n^2+1)
    (WeightedFailureBudget.exponent n B+1)
  simpa [oracleExponent,WeightedFailureBudget.tolerance,pow_succ,div_pow,one_pow,div_div,div_eq_mul_inv] using h

def run {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n) (B : ℕ)
    (hempty : (∅ : FractionalCover.Column n) ∉ columns adjacency w)
    (resources width : Bits) : PMF (BinaryWeightedPacking.Output w (columns adjacency w)) :=
  BinaryWeightedPackingConfidence.run w (columns adjacency w) (support_valid adjacency w) hempty
    (HeavyCutProvider.draw adjacency w (3*oracleExponent n B) empty)
    BinaryWeightedSamplingLaw.fairBit resources width

/-- Every supported final original-weight selection is a valid original cut,
including all physical failure flags and rejection-exhaustion fallbacks. -/
theorem run_valid {n : ℕ} (hn : 0<n) (adjacency : RetainedGridState.PairFlags n)
    (w : Row n) (B : ℕ) (hempty : (∅ : FractionalCover.Column n) ∉ columns adjacency w)
    (resources width : Bits) {out : BinaryWeightedPacking.Output w (columns adjacency w)}
    (hout : out∈(run adjacency w B hempty resources width).support) :
    ∃ q : BinaryApproximatePacking.Choice n, out.selected.label=some q.mask.toList ∧
      (BinaryFractionalCore.decodeChoice q).column∈columns adjacency w ∧
      ∀ i∈(BinaryFractionalCore.decodeChoice q).column,
        0<(BinaryRational.decode (get w i)).value := by
  rw [run,BinaryWeightedPackingConfidence.run_eq_map] at hout
  obtain ⟨original,ho,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  exact BinaryWeightedPacking.run_valid w (columns adjacency w) (support_valid adjacency w) hempty
    (HeavyCutProvider.draw adjacency w (3*oracleExponent n B) empty) hn
    (BinaryWeightedPackingConfidence.fuel resources width).1 (out := original) ho

/-- No caller oracle-quality or unit-mass premise remains. The existing
adaptive failure union and final bounded binary ticket draw use the concrete
heavy-query provider on each actual penalized row. -/
theorem uniform_marginal :
    ∀ δ : ℝ, 0<δ → ∃ K : ℝ, 0<K ∧
      ∀ (n : ℕ) (_hn : 0<n) (adjacency : RetainedGridState.PairFlags n) (w : Row n)
        (B : ℕ) (_hwidth : ∀ i, (BinaryRational.decode (get w i)).Bounded B)
        (hempty : (∅ : FractionalCover.Column n) ∉ columns adjacency w)
        (resources width : Bits) (_hm : value resources=n) (_hB : value width=B) (i : Fin n),
      ((run adjacency w B hempty resources width).toOuterMeasure
        {out | out.selected.label.any (BinaryApproximatePackingSampling.coordinate i)=true}).toReal ≤
          K*(n:ℝ)^((1:ℝ)/3+δ)*(FractionalCover.value (BinaryApproximatePacking.capacities w) i : ℝ) := by
  intro δ hδ
  obtain ⟨K,hK,hquery⟩ := HeavyCutProvider.uniform_charged_failure δ hδ
  refine ⟨4*K,by positivity,?_⟩
  intro n hn adjacency w B hwidth hempty resources width hm hB i
  have h := BinaryWeightedPackingConfidence.run_marginal_four_of_charged_failure
    w (columns adjacency w) (support_valid adjacency w) hempty
    (HeavyCutProvider.draw adjacency w (3*oracleExponent n B) empty) hn B hwidth
    (show 0<K*(n:ℝ)^((1:ℝ)/3+δ) by positivity)
    (show 0≤((1:ℝ)/2)^oracleExponent n B by positivity)
    (fun c => hquery n hn adjacency w c (oracleExponent n B) empty)
    resources width hm hB (oracle_budget n B) i
  simpa only [run,mul_assoc] using h

end
end DirectedFlowCutGap.HeavyPackingJoin
