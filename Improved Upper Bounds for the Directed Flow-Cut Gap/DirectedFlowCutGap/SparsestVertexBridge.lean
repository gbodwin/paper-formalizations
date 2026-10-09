import DirectedFlowCutGap.FiniteHarmonicThreshold
import DirectedFlowCutGap.AdaptiveVertexBound

/-!
# The normalized vertex sparsest-cut bridge

The demanded distances are actual endpoint-excluding directed distances.
For a finite family P with finite distances and positive sum S, the mass
parameter is explicitly W_avg = |P| W / S. It is raw total weight exactly
when the average demanded distance equals one. This supplies a rounding
theorem for every assignment, without assuming an optimizer or a runtime.

Unreachable demands are handled separately by the empty, zero-cost cut.
Zero-distance demands remain in P and its cardinality. An all-zero sum
does not define a positive-denominator fractional sparsest ratio.
-/

namespace DirectedFlowCutGap.SparsestVertexBridge
noncomputable section
open scoped BigOperators NNReal ENNReal
open FiniteHarmonicThreshold
attribute [local instance] Classical.propDecidable
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def demandDistance (G : Digraph V) (w : V → ℝ≥0) (p : V × V) : ℝ≥0 :=
  (vertexDistance G w p.1 p.2).toNNReal

def distanceSum (G : Digraph V) (w : V → ℝ≥0) (P : Finset (V × V)) : ℝ≥0 :=
  ∑ p : P, demandDistance G w p

def averageNormalizedMass (G : Digraph V) (w : V → ℝ≥0) (P : Finset (V × V)) : ℝ≥0 :=
  (P.card : ℝ≥0) * totalWeight w / distanceSum G w P

/-- The selected pairs are precisely those whose every simple directed path
meets the cut at an internal vertex. -/
def separated (G : Digraph V) (P : Finset (V × V)) (X : Finset V) : Finset P :=
  Finset.univ.filter (fun p => CutsPair G X p.val.1 p.val.2)

def sparsity (G : Digraph V) (c : V → ℝ≥0) (P : Finset (V × V)) (X : Finset V) : ℝ≥0 :=
  cutCost c X / ((separated G P X).card : ℝ≥0)

omit [Fintype V] in
/-- Positive scaling is exact even for unreachable pairs: infinity remains
infinity. The positivity assumption rules out the 0 times infinity artifact. -/
theorem vertexDistance_scale (G : Digraph V) (w : V → ℝ≥0) (a : ℝ≥0)
    (ha : 0 < a) (s t : V) :
    vertexDistance G (fun v => a * w v) s t = (a : ℝ≥0∞) * vertexDistance G w s t := by
  unfold vertexDistance
  rw [ENNReal.mul_iInf_of_ne (by exact_mod_cast ha.ne') ENNReal.coe_ne_top]
  apply iInf_congr
  intro p
  simp [SimplePath.weight, Finset.mul_sum]

omit [Fintype V] in
theorem demandDistance_scale (G : Digraph V) (w : V → ℝ≥0) (a : ℝ≥0)
    (ha : 0 < a) (p : V × V) :
    demandDistance G (fun v => a * w v) p = a * demandDistance G w p := by
  simp [demandDistance, vertexDistance_scale G w a ha, ENNReal.toNNReal_mul]

omit [Fintype V] in
theorem distanceSum_scale (G : Digraph V) (w : V → ℝ≥0) (a : ℝ≥0)
    (ha : 0 < a) (P : Finset (V × V)) :
    distanceSum G (fun v => a * w v) P = a * distanceSum G w P := by
  simp [distanceSum, demandDistance_scale G w a ha, Finset.mul_sum]

omit [DecidableEq V] in
theorem totalWeight_div (w : V → ℝ≥0) (τ : ℝ≥0) :
    totalWeight (fun v => w v / τ) = totalWeight w / τ := by
  simp [totalWeight, Finset.sum_div]

omit [DecidableEq V] in
theorem weightedCost_div (c w : V → ℝ≥0) (τ : ℝ≥0) :
    weightedCost c (fun v => w v / τ) = weightedCost c w / τ := by
  simp [weightedCost, mul_div_assoc, Finset.sum_div]

theorem averageNormalizedMass_scale (G : Digraph V) (w : V → ℝ≥0)
    (a : ℝ≥0) (ha : 0 < a) (P : Finset (V × V)) :
    averageNormalizedMass G (fun v => a * w v) P = averageNormalizedMass G w P := by
  unfold averageNormalizedMass
  rw [distanceSum_scale G w a ha]
  have hW : totalWeight (fun v => a * w v) = a * totalWeight w := by
    simp [totalWeight, Finset.mul_sum]
  rw [hW, normalized_mass_scale _ _ _ _ ha]

/-- The fractional sparsest ratio itself is unchanged by positive scaling. -/
theorem fractional_ratio_scale (G : Digraph V) (w c : V → ℝ≥0)
    (a : ℝ≥0) (ha : 0 < a) (P : Finset (V × V)) :
    weightedCost c (fun v => a * w v) / distanceSum G (fun v => a * w v) P =
      weightedCost c w / distanceSum G w P := by
  rw [distanceSum_scale G w a ha]
  have hC : weightedCost c (fun v => a * w v) = a * weightedCost c w := by
    simp only [weightedCost, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _hv
    ring
  rw [hC, mul_div_mul_left _ _ ha.ne']

/-- Under sum-distance-one normalization the mass is mW, not W. -/
theorem sum_one_normalized_mass (G : Digraph V) (w : V → ℝ≥0)
    (P : Finset (V × V)) (hS : distanceSum G w P = 1) :
    averageNormalizedMass G w P = (P.card : ℝ≥0) * totalWeight w := by
  simp [averageNormalizedMass, hS]

/-- Average-distance normalization makes the parameter exactly total weight. -/
theorem averageNormalizedMass_eq_totalWeight (G : Digraph V) (w : V → ℝ≥0)
    (P : Finset (V × V)) (hP : 0 < P.card)
    (havg : distanceSum G w P = (P.card : ℝ≥0)) :
    averageNormalizedMass G w P = totalWeight w := by
  have hm : (P.card : ℝ≥0) ≠ 0 := by exact_mod_cast hP.ne'
  simp [averageNormalizedMass, havg, mul_div_cancel_left₀, hm]

omit [Fintype V] in
/-- Rescaling by the average demanded distance constructs that normalization. -/
theorem normalize_average_distance (G : Digraph V) (w : V → ℝ≥0)
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
theorem mem_scaled_threshold (G : Digraph V) (w : V → ℝ≥0) (τ : ℝ≥0)
    (hτ : 0 < τ) (s t : V) :
    (s, t) ∈ thresholdDemands G (fun v => w v / τ) ↔
      (τ : ℝ≥0∞) ≤ vertexDistance G w s t := by
  change (1 : ℝ≥0∞) ≤ vertexDistance G (fun v => w v / τ) s t ↔ _
  rw [← ENNReal.coe_one, coe_le_vertexDistance_iff, coe_le_vertexDistance_iff]
  apply forall_congr'
  intro p
  rw [show p.weight (fun v => w v / τ) = p.weight w / τ by
    simp [SimplePath.weight, Finset.sum_div], le_div_iff₀ hτ]
  simp

omit [Fintype V] in
theorem threshold_card_le_separated (G : Digraph V) (w : V → ℝ≥0)
    (P : Finset (V × V)) (hfinite : ∀ p ∈ P, vertexDistance G w p.1 p.2 ≠ ⊤)
    (τ : ℝ≥0) (hτ : 0 < τ) (X : Finset V)
    (hX : IsIntegralCut G X (thresholdDemands G (fun v => w v / τ))) :
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
concluding uniform theorem instantiates this with AdaptiveVertexBound. -/
theorem sparsity_of_size_rounding (G : Digraph V) (c w : V → ℝ≥0)
    (P : Finset (V × V)) (hfinite : ∀ p ∈ P, vertexDistance G w p.1 p.2 ≠ ⊤)
    (hS : 0 < distanceSum G w P) (A : ℝ≥0)
    (hround : ∀ z : V → ℝ≥0, ∃ X : Finset V,
      IsIntegralCut G X (thresholdDemands G z) ∧ cutCost c X ≤ A * weightedCost c z) :
    ∃ X : Finset V, 0 < (separated G P X).card ∧
      sparsity G c P X ≤ A * harmonicWeight P.card * (weightedCost c w / distanceSum G w P) := by
  obtain ⟨τ, hτ, hk, hb⟩ := exists_threshold (fun p : P => demandDistance G w p) hS
  obtain ⟨X, hX, hcost⟩ := hround (fun v => w v / τ)
  have hcount := threshold_card_le_separated G w P hfinite τ hτ X hX
  refine ⟨X, lt_of_lt_of_le hk hcount, ?_⟩
  rw [weightedCost_div] at hcost
  simpa only [sparsity, Fintype.card_coe] using sparsity_transfer A (weightedCost c w)
    (distanceSum G w P) (harmonicWeight (Fintype.card P)) τ (cutCost c X)
    (above (fun p : P => demandDistance G w p) τ).card (separated G P X).card
    hS hτ hk hcount hb hcost

/-- The mass-sensitive bridge retains the harmonic exponent 3/2 and the
scale-invariant mass mW/S, including zero-cost fractional assignments. -/
theorem sparsity_of_weight_rounding (G : Digraph V) (c w : V → ℝ≥0)
    (P : Finset (V × V)) (hfinite : ∀ p ∈ P, vertexDistance G w p.1 p.2 ≠ ⊤)
    (hS : 0 < distanceSum G w P) (B : ℝ≥0)
    (hround : ∀ z : V → ℝ≥0, ∃ X : Finset V,
      IsIntegralCut G X (thresholdDemands G z) ∧
        cutCost c X ≤ (B * totalWeight z ^ (1 / 2 : ℝ)) * weightedCost c z) :
    ∃ X : Finset V, 0 < (separated G P X).card ∧
      sparsity G c P X ≤ B * harmonicWeight P.card ^ (3 / 2 : ℝ) *
        averageNormalizedMass G w P ^ (1 / 2 : ℝ) * (weightedCost c w / distanceSum G w P) := by
  obtain ⟨τ, hτ, hk, hb⟩ := exists_threshold (fun p : P => demandDistance G w p) hS
  obtain ⟨X, hX, hcost⟩ := hround (fun v => w v / τ)
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
  have hm : totalWeight (fun v => w v / τ) ≤
      harmonicWeight P.card * averageNormalizedMass G w P := by
    rw [totalWeight_div]
    exact scaled_mass_le P.card (totalWeight w) (distanceSum G w P)
      (harmonicWeight P.card) τ hS hτ hb'
  have hcost' : cutCost c X ≤
      (B * (harmonicWeight P.card * averageNormalizedMass G w P) ^ (1 / 2 : ℝ)) *
        (weightedCost c w / τ) := by
    rw [weightedCost_div] at hcost
    exact hcost.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (NNReal.rpow_le_rpow hm (by norm_num)) zero_le) zero_le)
  refine ⟨X, lt_of_lt_of_le hk hcount, ?_⟩
  have h := sparsity_transfer
    (B * (harmonicWeight P.card * averageNormalizedMass G w P) ^ (1 / 2 : ℝ))
    (weightedCost c w) (distanceSum G w P) (harmonicWeight P.card) τ (cutCost c X)
    (above (fun p : P => demandDistance G w p) τ).card (separated G P X).card
    hS hτ hk hcount (by simpa only [Fintype.card_coe, distanceSum] using hb) hcost'
  refine h.trans_eq ?_
  rw [NNReal.mul_rpow, AdaptiveVertexBound.mass_three_halves]
  ring

omit [Fintype V] in
/-- An unreachable demand is already separated by the empty cut. -/
theorem unreachable_zero_sparsity (G : Digraph V) (c w : V → ℝ≥0)
    (P : Finset (V × V)) (p : V × V) (hp : p ∈ P)
    (hunreachable : vertexDistance G w p.1 p.2 = ⊤) :
    0 < (separated G P ∅).card ∧ sparsity G c P ∅ = 0 := by
  have hno := (vertexDistance_eq_top_iff G w p.1 p.2).mp hunreachable
  constructor
  · apply Finset.card_pos.mpr
    refine ⟨⟨p, hp⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro path
    exact (hno ⟨path⟩).elim
  · simp [sparsity, cutCost]

omit [Fintype V] in
@[simp] theorem empty_demand_separation (G : Digraph V) (X : Finset V) :
    (separated G ∅ X).card = 0 := by simp [separated]

omit [Fintype V] in
/-- Under finiteness, zero sum means exactly that all actual distances vanish. -/
theorem zero_distance_sum_iff (G : Digraph V) (w : V → ℝ≥0) (P : Finset (V × V))
    (hfinite : ∀ p ∈ P, vertexDistance G w p.1 p.2 ≠ ⊤) :
    distanceSum G w P = 0 ↔ ∀ p ∈ P, vertexDistance G w p.1 p.2 = 0 := by
  rw [distanceSum, sum_eq_zero_iff]
  constructor
  · intro h p hp
    have hh := h ⟨p, hp⟩
    have he := ENNReal.coe_toNNReal (hfinite p hp)
    rw [show (vertexDistance G w p.1 p.2).toNNReal = 0 from hh] at he
    simpa using he.symm
  · intro h p
    simp [demandDistance, h p p.property]

omit [DecidableEq V] in
/-- Distinct ordered demand pairs have at most n squared members. -/
theorem demand_card_le_square (P : Finset (V × V)) : P.card ≤ Fintype.card V ^ 2 := by
  simpa [Fintype.card_prod, pow_two] using Finset.card_le_univ P

end
end DirectedFlowCutGap.SparsestVertexBridge
