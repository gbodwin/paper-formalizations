import DirectedFlowCutGap.FiniteHarmonicThreshold
import DirectedFlowCutGap.AdaptiveEdgeBound

/-!
# The normalized edge sparsest-cut bridge

The demanded distances are actual directed edge-length distances.
For a finite family P with finite distances and positive sum S, the mass
parameter is explicitly W_avg = |P| W / S. It is raw total weight exactly
when the average demanded distance equals one. This supplies a rounding
theorem for every assignment, without assuming an optimizer or a runtime.

Unreachable demands are handled separately by the empty, zero-cost cut.
Zero-distance demands remain in P and its cardinality. An all-zero sum
does not define a positive-denominator fractional sparsest ratio.
-/

namespace DirectedFlowCutGap.SparsestEdgeBridge
noncomputable section
open scoped BigOperators NNReal ENNReal
open FiniteHarmonicThreshold
attribute [local instance] Classical.propDecidable
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def demandDistance (G : Digraph V) (w : V × V → ℝ≥0) (p : V × V) : ℝ≥0 :=
  (edgeDistance G w p.1 p.2).toNNReal

def distanceSum (G : Digraph V) (w : V × V → ℝ≥0) (P : Finset (V × V)) : ℝ≥0 :=
  ∑ p : P, demandDistance G w p

def averageNormalizedMass (G : Digraph V) (w : V × V → ℝ≥0) (P : Finset (V × V)) : ℝ≥0 :=
  (P.card : ℝ≥0) * totalEdgeWeight G w / distanceSum G w P

/-- The selected pairs are precisely those whose every simple directed path
meets the cut in an actual edge. -/
def separated (G : Digraph V) (P : Finset (V × V)) (X : Finset (V × V)) : Finset P :=
  Finset.univ.filter (fun p => EdgeCutsPair G X p.val.1 p.val.2)

def sparsity (G : Digraph V) (c : V × V → ℝ≥0) (P : Finset (V × V)) (X : Finset (V × V)) : ℝ≥0 :=
  edgeCutCost G c X / ((separated G P X).card : ℝ≥0)

omit [Fintype V] in
/-- Positive scaling is exact even for unreachable pairs: infinity remains
infinity. The positivity assumption rules out the 0 times infinity artifact. -/
theorem edgeDistance_scale (G : Digraph V) (w : V × V → ℝ≥0) (a : ℝ≥0)
    (ha : 0 < a) (s t : V) :
    edgeDistance G (fun v => a * w v) s t = (a : ℝ≥0∞) * edgeDistance G w s t := by
  unfold edgeDistance
  rw [ENNReal.mul_iInf_of_ne (by exact_mod_cast ha.ne') ENNReal.coe_ne_top]
  apply iInf_congr
  intro p
  simp [SimplePath.edgeWeight, Finset.mul_sum]

omit [Fintype V] in
theorem demandDistance_scale (G : Digraph V) (w : V × V → ℝ≥0) (a : ℝ≥0)
    (ha : 0 < a) (p : V × V) :
    demandDistance G (fun v => a * w v) p = a * demandDistance G w p := by
  simp [demandDistance, edgeDistance_scale G w a ha, ENNReal.toNNReal_mul]

omit [Fintype V] in
theorem distanceSum_scale (G : Digraph V) (w : V × V → ℝ≥0) (a : ℝ≥0)
    (ha : 0 < a) (P : Finset (V × V)) :
    distanceSum G (fun v => a * w v) P = a * distanceSum G w P := by
  simp [distanceSum, demandDistance_scale G w a ha, Finset.mul_sum]

omit [DecidableEq V] in
theorem totalEdgeWeight_div (G : Digraph V) (w : V × V → ℝ≥0) (τ : ℝ≥0) :
    totalEdgeWeight G (fun v => w v / τ) = totalEdgeWeight G w / τ := by
  simp [totalEdgeWeight, Finset.sum_div]

omit [DecidableEq V] in
theorem weightedEdgeCost_div (G : Digraph V) (c w : V × V → ℝ≥0) (τ : ℝ≥0) :
    weightedEdgeCost G c (fun v => w v / τ) = weightedEdgeCost G c w / τ := by
  simp [weightedEdgeCost, mul_div_assoc, Finset.sum_div]

theorem averageNormalizedMass_scale (G : Digraph V) (w : V × V → ℝ≥0)
    (a : ℝ≥0) (ha : 0 < a) (P : Finset (V × V)) :
    averageNormalizedMass G (fun v => a * w v) P = averageNormalizedMass G w P := by
  unfold averageNormalizedMass
  rw [distanceSum_scale G w a ha]
  have hW : totalEdgeWeight G (fun v => a * w v) = a * totalEdgeWeight G w := by
    simp [totalEdgeWeight, Finset.mul_sum]
  rw [hW, normalized_mass_scale _ _ _ _ ha]

/-- The fractional sparsest ratio itself is unchanged by positive scaling. -/
theorem fractional_ratio_scale (G : Digraph V) (w c : V × V → ℝ≥0)
    (a : ℝ≥0) (ha : 0 < a) (P : Finset (V × V)) :
    weightedEdgeCost G c (fun v => a * w v) / distanceSum G (fun v => a * w v) P =
      weightedEdgeCost G c w / distanceSum G w P := by
  rw [distanceSum_scale G w a ha]
  have hC : weightedEdgeCost G c (fun v => a * w v) = a * weightedEdgeCost G c w := by
    simp only [weightedEdgeCost, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _hv
    ring
  rw [hC, mul_div_mul_left _ _ ha.ne']

/-- Under sum-distance-one normalization the mass is mW, not W. -/
theorem sum_one_normalized_mass (G : Digraph V) (w : V × V → ℝ≥0)
    (P : Finset (V × V)) (hS : distanceSum G w P = 1) :
    averageNormalizedMass G w P = (P.card : ℝ≥0) * totalEdgeWeight G w := by
  simp [averageNormalizedMass, hS]

/-- Average-distance normalization makes the parameter exactly total weight. -/
theorem averageNormalizedMass_eq_totalEdgeWeight (G : Digraph V) (w : V × V → ℝ≥0)
    (P : Finset (V × V)) (hP : 0 < P.card)
    (havg : distanceSum G w P = (P.card : ℝ≥0)) :
    averageNormalizedMass G w P = totalEdgeWeight G w := by
  have hm : (P.card : ℝ≥0) ≠ 0 := by exact_mod_cast hP.ne'
  simp [averageNormalizedMass, havg, mul_div_cancel_left₀, hm]

omit [Fintype V] in
/-- Rescaling by the average demanded distance constructs that normalization. -/
theorem normalize_average_distance (G : Digraph V) (w : V × V → ℝ≥0)
    (P : Finset (V × V)) (hS : 0 < distanceSum G w P) :
    distanceSum G (fun v => ((P.card : ℝ≥0) / distanceSum G w P) * w v) P =
      (P.card : ℝ≥0) := by
  have hP : 0 < P.card := by
    by_contra hn
    have hz : P = ∅ := Finset.card_eq_zero.mp (by omega)
    subst P
    simp [distanceSum] at hS
  rw [distanceSum_scale G w _ (by positivity)]
  exact div_mul_cancel₀ _ hS.ne'

omit [Fintype V] in
/-- Membership in the scaled threshold family is exactly the original
extended distance being at least τ. This also covers unreachable pairs. -/
theorem mem_scaled_threshold (G : Digraph V) (w : V × V → ℝ≥0) (τ : ℝ≥0)
    (hτ : 0 < τ) (s t : V) :
    (s, t) ∈ edgeThresholdDemands G (fun v => w v / τ) ↔
      (τ : ℝ≥0∞) ≤ edgeDistance G w s t := by
  change (1 : ℝ≥0∞) ≤ edgeDistance G (fun v => w v / τ) s t ↔ _
  rw [← ENNReal.coe_one, coe_le_edgeDistance_iff, coe_le_edgeDistance_iff]
  apply forall_congr'
  intro p
  rw [show p.edgeWeight (fun v => w v / τ) = p.edgeWeight w / τ by
    simp [SimplePath.edgeWeight, Finset.sum_div], le_div_iff₀ hτ]
  simp

omit [Fintype V] in
theorem threshold_card_le_separated (G : Digraph V) (w : V × V → ℝ≥0)
    (P : Finset (V × V)) (hfinite : ∀ p ∈ P, edgeDistance G w p.1 p.2 ≠ ⊤)
    (τ : ℝ≥0) (hτ : 0 < τ) (X : Finset (V × V))
    (hX : IsIntegralEdgeCut G X (edgeThresholdDemands G (fun v => w v / τ))) :
    (above (fun p : P => demandDistance G w p) τ).card ≤ (separated G P X).card := by
  apply Finset.card_le_card
  intro p hp
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hX p.val.1 p.val.2 ?_⟩
  apply (mem_scaled_threshold G w τ hτ _ _).mpr
  have hd := (Finset.mem_filter.mp hp).2
  have hd' : (τ : ℝ≥0∞) ≤ (demandDistance G w p : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hd
  simpa only [demandDistance, ENNReal.coe_toNNReal (hfinite p p.property)] using hd'

/-- Concrete bridge for any valid all-lengths size rounding bound. The
concluding uniform theorem instantiates this with AdaptiveEdgeBound. -/
theorem sparsity_of_size_rounding (G : Digraph V) (c w : V × V → ℝ≥0)
    (P : Finset (V × V)) (hfinite : ∀ p ∈ P, edgeDistance G w p.1 p.2 ≠ ⊤)
    (hS : 0 < distanceSum G w P) (A : ℝ≥0)
    (hround : ∀ z : V × V → ℝ≥0, ∃ X : Finset (V × V),
      X ⊆ graphEdges G ∧ IsIntegralEdgeCut G X (edgeThresholdDemands G z) ∧ edgeCutCost G c X ≤ A * weightedEdgeCost G c z) :
    ∃ X : Finset (V × V), X ⊆ graphEdges G ∧ 0 < (separated G P X).card ∧
      sparsity G c P X ≤ A * harmonicWeight P.card * (weightedEdgeCost G c w / distanceSum G w P) := by
  obtain ⟨τ, hτ, hk, hb⟩ := exists_threshold (fun p : P => demandDistance G w p) hS
  obtain ⟨X, hactual, hX, hcost⟩ := hround (fun v => w v / τ)
  have hcount := threshold_card_le_separated G w P hfinite τ hτ X hX
  refine ⟨X, hactual, lt_of_lt_of_le hk hcount, ?_⟩
  rw [weightedEdgeCost_div] at hcost
  simpa only [sparsity, Fintype.card_coe] using sparsity_transfer A (weightedEdgeCost G c w)
    (distanceSum G w P) (harmonicWeight (Fintype.card P)) τ (edgeCutCost G c X)
    (above (fun p : P => demandDistance G w p) τ).card (separated G P X).card
    hS hτ hk hcount hb hcost

/-- The mass-sensitive bridge retains the harmonic exponent 3/2 and the
scale-invariant mass mW/S, including zero-cost fractional assignments. -/
theorem sparsity_of_weight_rounding (G : Digraph V) (c w : V × V → ℝ≥0)
    (P : Finset (V × V)) (hfinite : ∀ p ∈ P, edgeDistance G w p.1 p.2 ≠ ⊤)
    (hS : 0 < distanceSum G w P) (B : ℝ≥0)
    (hround : ∀ z : V × V → ℝ≥0, ∃ X : Finset (V × V),
      X ⊆ graphEdges G ∧ IsIntegralEdgeCut G X (edgeThresholdDemands G z) ∧
        edgeCutCost G c X ≤ (B * totalEdgeWeight G z ^ (1 / 2 : ℝ)) * weightedEdgeCost G c z) :
    ∃ X : Finset (V × V), X ⊆ graphEdges G ∧ 0 < (separated G P X).card ∧
      sparsity G c P X ≤ B * harmonicWeight P.card ^ (3 / 2 : ℝ) *
        averageNormalizedMass G w P ^ (1 / 2 : ℝ) * (weightedEdgeCost G c w / distanceSum G w P) := by
  obtain ⟨τ, hτ, hk, hb⟩ := exists_threshold (fun p : P => demandDistance G w p) hS
  obtain ⟨X, hactual, hX, hcost⟩ := hround (fun v => w v / τ)
  have hcount := threshold_card_le_separated G w P hfinite τ hτ X hX
  have hb' : distanceSum G w P ≤ harmonicWeight P.card * (τ * (P.card : ℝ≥0)) := by
    have hb0 : distanceSum G w P ≤ harmonicWeight P.card *
        (τ * ((above (fun p : P => demandDistance G w p) τ).card : ℝ≥0)) := by
      simpa only [Fintype.card_coe, distanceSum] using hb
    refine hb0.trans ?_
    apply mul_le_mul_of_nonneg_left _ zero_le
    apply mul_le_mul_of_nonneg_left _ zero_le
    have hc : (above (fun p : P => demandDistance G w p) τ).card ≤ P.card := by
      simpa only [Fintype.card_coe] using above_card_le (fun p : P => demandDistance G w p) τ
    exact_mod_cast hc
  have hm : totalEdgeWeight G (fun v => w v / τ) ≤
      harmonicWeight P.card * averageNormalizedMass G w P := by
    rw [totalEdgeWeight_div]
    exact scaled_mass_le P.card (totalEdgeWeight G w) (distanceSum G w P)
      (harmonicWeight P.card) τ hS hτ hb'
  have hcost' : edgeCutCost G c X ≤
      (B * (harmonicWeight P.card * averageNormalizedMass G w P) ^ (1 / 2 : ℝ)) *
        (weightedEdgeCost G c w / τ) := by
    rw [weightedEdgeCost_div] at hcost
    exact hcost.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (NNReal.rpow_le_rpow hm (by norm_num)) zero_le) zero_le)
  refine ⟨X, hactual, lt_of_lt_of_le hk hcount, ?_⟩
  have h := sparsity_transfer
    (B * (harmonicWeight P.card * averageNormalizedMass G w P) ^ (1 / 2 : ℝ))
    (weightedEdgeCost G c w) (distanceSum G w P) (harmonicWeight P.card) τ (edgeCutCost G c X)
    (above (fun p : P => demandDistance G w p) τ).card (separated G P X).card
    hS hτ hk hcount (by simpa only [Fintype.card_coe, distanceSum] using hb) hcost'
  refine h.trans_eq ?_
  rw [NNReal.mul_rpow, AdaptiveVertexBound.mass_three_halves]
  ring

omit [Fintype V] in
/-- An unreachable demand is already separated by the empty cut. -/
theorem unreachable_zero_sparsity (G : Digraph V) (c w : V × V → ℝ≥0)
    (P : Finset (V × V)) (p : V × V) (hp : p ∈ P)
    (hunreachable : edgeDistance G w p.1 p.2 = ⊤) :
    0 < (separated G P ∅).card ∧ sparsity G c P ∅ = 0 := by
  have hno := (edgeDistance_eq_top_iff G w p.1 p.2).mp hunreachable
  constructor
  · apply Finset.card_pos.mpr
    refine ⟨⟨p, hp⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro path
    exact (hno ⟨path⟩).elim
  · simp [sparsity, edgeCutCost]

omit [Fintype V] in
@[simp] theorem empty_demand_separation (G : Digraph V) (X : Finset (V × V)) :
    (separated G ∅ X).card = 0 := by simp [separated]

omit [Fintype V] in
/-- Under finiteness, zero sum means exactly that all actual distances vanish. -/
theorem zero_distance_sum_iff (G : Digraph V) (w : V × V → ℝ≥0) (P : Finset (V × V))
    (hfinite : ∀ p ∈ P, edgeDistance G w p.1 p.2 ≠ ⊤) :
    distanceSum G w P = 0 ↔ ∀ p ∈ P, edgeDistance G w p.1 p.2 = 0 := by
  rw [distanceSum, sum_eq_zero_iff]
  constructor
  · intro h p hp
    have hh := h ⟨p, hp⟩
    have he := ENNReal.coe_toNNReal (hfinite p hp)
    rw [show (edgeDistance G w p.1 p.2).toNNReal = 0 from hh] at he
    simpa using he.symm
  · intro h p
    simp [demandDistance, h p p.property]

omit [DecidableEq V] in
/-- Distinct ordered demand pairs have at most n squared members. -/
theorem demand_card_le_square (P : Finset (V × V)) : P.card ≤ Fintype.card V ^ 2 := by
  simpa [Fintype.card_prod, pow_two] using Finset.card_le_univ P

end
end DirectedFlowCutGap.SparsestEdgeBridge
