import DirectedFlowCutGap.AdaptiveVertexBound
import DirectedFlowCutGap.EdgeToVertexReduction
import DirectedFlowCutGap.EdgeRounding

/-!
# Uniform directed edge rounding bounds

The concrete dyadic reduction is applied to bounded vertex instances, with
actual size `2n(log₂n+4)` and total weight at most `4W`. A smaller exponent is
selected before every graph and weight, then the logarithmic size overhead is
absorbed into a uniform constant. The bounds below give actual integral edge
cuts for arbitrary nonnegative costs; they assert no implementation runtime.
-/

namespace DirectedFlowCutGap

noncomputable section
open scoped BigOperators NNReal ENNReal

namespace AdaptiveEdgeBound

open SubpolynomialBounds
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The finite overhead per original vertex, including both endpoint ports. -/
def overhead (n : ℕ) : ℕ := 2 * (Nat.log2 n + 4)

def gadgetSize (n : ℕ) : ℕ := n * overhead n

theorem gadgetSize_eq (n : ℕ) : gadgetSize n = 2 * n * (Nat.log2 n + 4) := by
  unfold gadgetSize overhead
  ring

theorem one_le_overhead (n : ℕ) : 1 ≤ overhead n := by
  unfold overhead
  omega

/-- The integer dyadic-label count has a uniform subpolynomial envelope. -/
theorem overhead_subpolynomial : Subpolynomial (fun n => (overhead n : ℝ)) := by
  apply ((Subpolynomial.const 2).mul
    (((Subpolynomial.const (1 / Real.log 2)).mul log_size_subpolynomial).add
      (Subpolynomial.const 4))).mono
  intro n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogsize : 0 < Real.log ((n : ℝ) + 2) := log_size_pos n
  have hlog : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log hnpos (by linarith)
  have hlabels : (Nat.log2 n : ℝ) ≤ (1 / Real.log 2) * Real.log ((n : ℝ) + 2) := by
    calc
      (Nat.log2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := Real.log2_le_logb n
      _ ≤ Real.log ((n : ℝ) + 2) / Real.log 2 :=
        div_le_div_of_nonneg_right hlog hlogtwo.le
      _ = _ := by ring
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
  unfold overhead
  push_cast
  nlinarith

/-- Absorb every fixed real power of the logarithmic overhead. Both the
exponent slack and the constant are chosen before the input graph size. -/
theorem gadget_power_uniform (a η : ℝ) (hη : 0 < η) :
    ∃ D : ℝ≥0, 0 < D ∧ ∀ n : ℕ, 1 ≤ n →
      (gadgetSize n : ℝ≥0) ^ a ≤ D * (n : ℝ≥0) ^ (a + η) := by
  obtain ⟨C, hC, hbound⟩ := (overhead_subpolynomial.pow (Nat.ceil a)) η hη
  let D : ℝ≥0 := ⟨C, hC.le⟩
  refine ⟨D, by exact_mod_cast hC, ?_⟩
  intro n hn
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hpow : (overhead n : ℝ≥0) ^ (Nat.ceil a) ≤ D * (n : ℝ≥0) ^ η := by
    have hh := hbound n hn
    rw [abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)] at hh
    exact_mod_cast hh
  have hr : (overhead n : ℝ≥0) ^ a ≤ D * (n : ℝ≥0) ^ η := by
    calc
      (overhead n : ℝ≥0) ^ a ≤ (overhead n : ℝ≥0) ^ (Nat.ceil a : ℝ) :=
        NNReal.rpow_le_rpow_of_exponent_le (by exact_mod_cast one_le_overhead n) (Nat.le_ceil a)
      _ = (overhead n : ℝ≥0) ^ (Nat.ceil a) := NNReal.rpow_natCast _ _
      _ ≤ _ := hpow
  calc
    (gadgetSize n : ℝ≥0) ^ a = (n : ℝ≥0) ^ a * (overhead n : ℝ≥0) ^ a := by
      rw [gadgetSize, Nat.cast_mul, NNReal.mul_rpow]
    _ ≤ (n : ℝ≥0) ^ a * (D * (n : ℝ≥0) ^ η) :=
      mul_le_mul_of_nonneg_left hr zero_le
    _ = D * (n : ℝ≥0) ^ (a + η) := by
      rw [NNReal.rpow_add hn0]
      ring

/-- A size estimate chosen uniformly before all vertex instances. -/
def VertexSizeEstimate (a : ℝ) (K : ℝ≥0) : Prop :=
  ∀ (U : Type u) [Fintype U] [DecidableEq U] (G : Digraph U) (w c : U → ℝ≥0),
    ∃ X : Finset U, IsIntegralCut G X (thresholdDemands G w) ∧
      cutCost c X ≤ (K * (Fintype.card U : ℝ≥0) ^ a) * weightedCost c w

/-- A mass-sensitive estimate chosen uniformly before all vertex instances. -/
def VertexWeightEstimate (a : ℝ) (K : ℝ≥0) : Prop :=
  ∀ (U : Type u) [Fintype U] [DecidableEq U] (G : Digraph U) (w c : U → ℝ≥0),
    ∃ X : Finset U, IsIntegralCut G X (thresholdDemands G w) ∧
      cutCost c X ≤ (K * (Fintype.card U : ℝ≥0) ^ a *
        totalWeight w ^ (1 / 2 : ℝ)) * weightedCost c w

/-- Size monotonicity is proved directly for an oracle on the actual finite
instances; it is not postulated for an exact-parameter gap function. -/
theorem bounded_size_oracle (a : ℝ) (ha : 0 ≤ a) (K : ℝ≥0)
    (h : VertexSizeEstimate.{u} a K) (N : ℕ) (B : ℝ≥0) :
    EdgeToVertex.BoundedVertexRoundingOracle.{u} N B (K * (N : ℝ≥0) ^ a) := by
  intro U _ _ G w c hn _hW
  obtain ⟨X, hX, hx⟩ := h U G w c
  refine ⟨X, hX, hx.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ zero_le
  exact mul_le_mul_of_nonneg_left (NNReal.rpow_le_rpow (by exact_mod_cast hn) ha) zero_le

theorem bounded_weight_oracle (a : ℝ) (ha : 0 ≤ a) (K : ℝ≥0)
    (h : VertexWeightEstimate.{u} a K) (N : ℕ) (B : ℝ≥0) :
    EdgeToVertex.BoundedVertexRoundingOracle.{u} N B
      (K * (N : ℝ≥0) ^ a * B ^ (1 / 2 : ℝ)) := by
  intro U _ _ G w c hn hW
  obtain ⟨X, hX, hx⟩ := h U G w c
  refine ⟨X, hX, hx.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ zero_le
  apply mul_le_mul'
  · exact mul_le_mul_of_nonneg_left (NNReal.rpow_le_rpow (by exact_mod_cast hn) ha) zero_le
  · exact NNReal.rpow_le_rpow hW (by norm_num)

/-- The full edge-size bound. Its constant is selected before every finite
vertex type, graph, edge weight and edge cost. -/
theorem edge_rounding_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ≥0, 0 < K ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V) (w c : V × V → ℝ≥0),
        ∃ X : Finset (V × V), X ⊆ graphEdges G ∧
          IsIntegralEdgeCut G X (edgeThresholdDemands G w) ∧
          edgeCutCost G c X ≤
            (K * (Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3 + ε)) * weightedEdgeCost G c w := by
  intro ε hε
  obtain ⟨C, hC, hvertex⟩ := AdaptiveVertexBound.vertex_rounding_uniform.{u} (ε / 2) (by positivity)
  obtain ⟨D, hD, hsize⟩ := gadget_power_uniform ((1 : ℝ) / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨4 * C * D, by positivity, ?_⟩
  intro V _ _ G w c
  by_cases hn : 1 ≤ Fintype.card V
  · obtain ⟨X, hX, hvalid, hx⟩ := EdgeToVertex.threshold_round_of_bounded_vertex_oracle G w c _
      (bounded_size_oracle ((1 : ℝ) / 3 + ε / 2) (by positivity) C hvertex
        (2 * Fintype.card V * (Nat.log2 (Fintype.card V) + 4)) (4 * totalEdgeWeight G w))
    refine ⟨X, hX, hvalid, hx.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ zero_le
    have h := hsize (Fintype.card V) hn
    rw [gadgetSize_eq, show (1 : ℝ) / 3 + ε / 2 + ε / 2 = 1 / 3 + ε by ring] at h
    calc
      4 * (C * _ ) ≤ 4 * (C * (D * (Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3 + ε))) := by gcongr
      _ = _ := by ring
  · have hz : Fintype.card V = 0 := by omega
    let : IsEmpty V := Fintype.card_eq_zero_iff.mp hz
    refine ⟨∅, Finset.empty_subset _, ?_, by simp [edgeCutCost]⟩
    intro s
    exact isEmptyElim s

/-- The full edge mass-sensitive bound, with the same quantifier order and
with empty graphs, zero weights, and zero costs included. -/
theorem edge_weight_rounding_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ≥0, 0 < K ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V) (w c : V × V → ℝ≥0),
        ∃ X : Finset (V × V), X ⊆ graphEdges G ∧
          IsIntegralEdgeCut G X (edgeThresholdDemands G w) ∧
          edgeCutCost G c X ≤ (K * (Fintype.card V : ℝ≥0) ^ ε *
            totalEdgeWeight G w ^ (1 / 2 : ℝ)) * weightedEdgeCost G c w := by
  intro ε hε
  obtain ⟨C, hC, hvertex⟩ := AdaptiveVertexBound.vertex_weight_rounding_uniform.{u} (ε / 2) (by positivity)
  obtain ⟨D, hD, hsize⟩ := gadget_power_uniform (ε / 2) (ε / 2) (by positivity)
  refine ⟨4 * C * D * (4 : ℝ≥0) ^ (1 / 2 : ℝ), by positivity, ?_⟩
  intro V _ _ G w c
  by_cases hn : 1 ≤ Fintype.card V
  · obtain ⟨X, hX, hvalid, hx⟩ := EdgeToVertex.threshold_round_of_bounded_vertex_oracle G w c _
      (bounded_weight_oracle (ε / 2) (by positivity) C hvertex
        (2 * Fintype.card V * (Nat.log2 (Fintype.card V) + 4)) (4 * totalEdgeWeight G w))
    refine ⟨X, hX, hvalid, hx.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ zero_le
    have h := hsize (Fintype.card V) hn
    rw [gadgetSize_eq, show ε / 2 + ε / 2 = ε by ring] at h
    calc
      4 * (C * _ * (4 * totalEdgeWeight G w) ^ (1 / 2 : ℝ)) ≤
          4 * (C * (D * (Fintype.card V : ℝ≥0) ^ ε) *
            (4 * totalEdgeWeight G w) ^ (1 / 2 : ℝ)) := by gcongr
      _ = _ := by rw [NNReal.mul_rpow]; ring
  · have hz : Fintype.card V = 0 := by omega
    let : IsEmpty V := Fintype.card_eq_zero_iff.mp hz
    refine ⟨∅, Finset.empty_subset _, ?_, by simp [edgeCutCost]⟩
    intro s
    exact isEmptyElim s

/-- The uniform size theorem in the all-cost edge-rounding interface. -/
theorem hasEdgeRoundingFactor_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V) (w : V × V → ℝ≥0),
        HasEdgeRoundingFactor G w (K * (Fintype.card V : ℝ) ^ ((1 : ℝ) / 3 + ε)) := by
  intro ε hε
  obtain ⟨K, hK, hround⟩ := edge_rounding_uniform.{u} ε hε
  refine ⟨K, by exact_mod_cast hK, ?_⟩
  intro V _ _ G w
  refine ⟨by positivity, ?_⟩
  intro c
  obtain ⟨X, hX, hvalid, hx⟩ := hround V G w c
  exact ⟨X, hX, hvalid, by exact_mod_cast hx⟩

/-- The uniform mass theorem in the all-cost edge-rounding interface. -/
theorem hasEdgeWeightRoundingFactor_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V) (w : V × V → ℝ≥0),
        HasEdgeRoundingFactor G w (K * (Fintype.card V : ℝ) ^ ε *
          (totalEdgeWeight G w : ℝ) ^ (1 / 2 : ℝ)) := by
  intro ε hε
  obtain ⟨K, hK, hround⟩ := edge_weight_rounding_uniform.{u} ε hε
  refine ⟨K, by exact_mod_cast hK, ?_⟩
  intro V _ _ G w
  refine ⟨by positivity, ?_⟩
  intro c
  obtain ⟨X, hX, hvalid, hx⟩ := hround V G w c
  exact ⟨X, hX, hvalid, by exact_mod_cast hx⟩

end AdaptiveEdgeBound
end
end DirectedFlowCutGap
