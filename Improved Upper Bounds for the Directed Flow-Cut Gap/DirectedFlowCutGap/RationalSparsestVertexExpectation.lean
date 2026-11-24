import DirectedFlowCutGap.RationalSparsestVertexRound

/-! Convert the two ideal vertex price bounds to sparsity at the
computed endpoint-safe threshold. -/
namespace DirectedFlowCutGap.RationalSparsestVertexExpectation

noncomputable section
open scoped BigOperators NNReal NNRat
open BinaryFractionalWalkOracle (Adjacency graph)
open BinaryFractionalRows (Row)
open RationalSparsestVertexDistances (weights)
open RationalSparsestVertexThreshold (choose actualDistance)
open RationalSparsestVertexRound (scaled tree)
open RationalSparsestEdgeRound (demandSet)
open EncodedUnitCostReplication (Input selectedSet)
open RetainedGridState (Flags)
open FiniteHarmonicThreshold (above harmonicWeight)
open FiniteDrawTrees (ideal)
open FiniteAmplification (expectedCost)

attribute [local instance] EncodedUniformRounding.flagsFintype

variable {m n : ℕ}

def expectedSparsity (D : Input n) (P : Finset (Fin n × Fin n))
    (mode : ChargedVertexModes.Mode) : ℝ :=
  expectedCost (ideal (tree D mode)) (fun mask => (SparsestVertexBridge.sparsity D.graph D.cost P
    (selectedSet mask) : ℝ))

def expectedPrice (D : Input n) (mode : ChargedVertexModes.Mode) : ℝ :=
  expectedCost (ideal (tree D mode)) (fun mask => (cutCost D.cost (selectedSet mask) : ℝ))

theorem ratio_le (A : Adjacency n) (w c : Row n)
    (P : Vector (Fin n × Fin n) m) (distinct : Function.Injective fun j : Fin m => P[j.val])
    {i : Fin m} {τ : ℚ≥0} (chosen : choose A w P = .threshold i τ) (mode : ChargedVertexModes.Mode) :
    let D := scaled A w c τ
    let k := (above (actualDistance A w P) (τ : ℝ≥0)).card
    expectedSparsity D (demandSet P) mode ≤ expectedPrice D mode / (k : ℝ) := by
  classical
  let D := scaled A w c τ
  let k := (above (actualDistance A w P) (τ : ℝ≥0)).card
  let p := ideal (tree D mode)
  have spec := RationalSparsestVertexThreshold.choose_spec A w P
  rw [chosen] at spec
  have kpos : (0 : ℝ) < k := by exact_mod_cast spec.2.2.2.1
  change expectedSparsity D (demandSet P) mode ≤ expectedPrice D mode / (k : ℝ)
  rw [expectedSparsity, expectedPrice, expectedCost, expectedCost, Finset.sum_div]
  apply Finset.sum_le_sum
  intro mask _
  change (p mask).toReal * (SparsestVertexBridge.sparsity D.graph D.cost (demandSet P) (selectedSet mask) : ℝ) ≤
    (p mask).toReal * (cutCost D.cost (selectedSet mask) : ℝ) / (k : ℝ)
  by_cases zero : p mask = 0
  · simp [zero]
  · have seen := (PMF.mem_support_iff p mask).mpr zero
    have valid : IsIntegralCut D.graph (selectedSet mask) (thresholdDemands D.graph D.weight) := by
      cases mode
      · exact EncodedWeightedRounding.support_valid D seen
      · exact EncodedSizeRounding.support_valid D seen
    have count := RationalSparsestVertexRound.count_le A w c P distinct chosen valid
    have realCount : (k : ℝ) ≤ ((SparsestVertexBridge.separated D.graph (demandSet P)
        (selectedSet mask)).card : ℝ) := by
      change (k : ℝ) ≤ ((SparsestVertexBridge.separated (graph A) (demandSet P)
        (selectedSet mask)).card : ℝ)
      exact_mod_cast count
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    simp only [SparsestVertexBridge.sparsity, NNReal.coe_div, NNReal.coe_natCast]
    exact div_le_div_of_nonneg_left (NNReal.coe_nonneg _) kpos realCount

private theorem transfer (A : Adjacency n) (w c : Row n)
    (P : Vector (Fin n × Fin n) m) (distinct : Function.Injective fun j : Fin m => P[j.val])
    {i : Fin m} {τ : ℚ≥0} (chosen : choose A w P = .threshold i τ) (mode : ChargedVertexModes.Mode)
    {factor : ℝ} (nonnegative : 0 ≤ factor)
    (fee : let D := scaled A w c τ
      expectedPrice D mode ≤ factor * (weightedCost D.cost D.weight : ℝ)) :
    expectedSparsity (scaled A w c τ) (demandSet P) mode ≤
      factor * (harmonicWeight m : ℝ) * ((weightedCost (weights c) (weights w) : ℝ) /
        ∑ j, (actualDistance A w P j : ℝ)) := by
  let D := scaled A w c τ
  let k := (above (actualDistance A w P) (τ : ℝ≥0)).card
  let C : ℝ := weightedCost (weights c) (weights w)
  let S : ℝ := ∑ j, (actualDistance A w P j : ℝ)
  let H : ℝ := harmonicWeight m
  have spec := RationalSparsestVertexThreshold.choose_spec A w P
  rw [chosen] at spec
  obtain ⟨_, dist, τpos, kpos, score⟩ := spec
  have cast : ((τ : ℝ≥0) : ℝ) = (τ : ℝ) := rfl
  have t : (0 : ℝ) < τ := by exact_mod_cast τpos
  have kReal : (0 : ℝ) < k := by exact_mod_cast kpos
  have Spos : 0 < S := by
    have included : (actualDistance A w P i : ℝ) ≤ S :=
      Finset.single_le_sum (fun _ _ => NNReal.coe_nonneg _) (Finset.mem_univ i)
    rw [dist, cast] at included
    exact t.trans_le included
  have budget : S ≤ H * ((τ : ℝ)*(k : ℝ)) := by
    simpa only [NNReal.coe_sum, NNReal.coe_mul, cast, NNReal.coe_natCast] using NNReal.coe_le_coe.mpr score
  have price : (weightedCost D.cost D.weight : ℝ) = C/(τ : ℝ) := by
    change (weightedCost (scaled A w c τ).cost (scaled A w c τ).weight : ℝ) = _
    rw [RationalSparsestVertexRound.scaled_price, RationalSparsestVertexRound.scaled_weight,
      SparsestVertexBridge.weightedCost_div]
    simp only [C, NNReal.coe_div, cast]
  have divide : 1/((τ : ℝ)*(k : ℝ)) ≤ H/S := by
    refine (div_le_div_iff₀ (mul_pos t kReal) Spos).mpr ?_
    simpa only [one_mul] using budget
  calc
    _ ≤ expectedPrice D mode/(k : ℝ) := ratio_le A w c P distinct chosen mode
    _ ≤ (factor*(C/(τ : ℝ)))/(k : ℝ) :=
      div_le_div_of_nonneg_right (fee.trans_eq (by rw [price])) kReal.le
    _ = (factor*C)*(1/((τ : ℝ)*(k : ℝ))) := by ring
    _ ≤ (factor*C)*(H/S) := mul_le_mul_of_nonneg_left divide (mul_nonneg nonnegative (NNReal.coe_nonneg _))
    _ = _ := by ring

theorem size_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ {m n : ℕ} (A : Adjacency n) (w c : Row n)
      (P : Vector (Fin n × Fin n) m) (_distinct : Function.Injective fun j : Fin m => P[j.val])
      {i : Fin m} {τ : ℚ≥0}, choose A w P = .threshold i τ →
      expectedSparsity (scaled A w c τ) (demandSet P) .size ≤
        K*(n : ℝ)^(1/3+ε)*(harmonicWeight m : ℝ)*((weightedCost (weights c) (weights w) : ℝ) /
          ∑ j, (actualDistance A w P j : ℝ)) := by
  intro ε positive
  obtain ⟨K,Kpos,rounding⟩ := EncodedSizeRounding.expected_cost_uniform ε positive
  refine ⟨K,Kpos,?_⟩
  intro m n A w c P distinct i τ chosen
  exact transfer A w c P distinct chosen .size (by positivity) (rounding n (scaled A w c τ))

def normalizedMass (A : Adjacency n) (w : Row n) (P : Vector (Fin n × Fin n) m) : ℝ≥0 :=
  (m : ℝ≥0) * totalWeight (weights w) / ∑ j, actualDistance A w P j

theorem scaled_mass_le (A : Adjacency n) (w c : Row n) (P : Vector (Fin n × Fin n) m)
    {i : Fin m} {τ : ℚ≥0} (chosen : choose A w P = .threshold i τ) :
    totalWeight (scaled A w c τ).weight ≤ harmonicWeight m * normalizedMass A w P := by
  have spec := RationalSparsestVertexThreshold.choose_spec A w P
  rw [chosen] at spec
  obtain ⟨_,atIndex,τpos,_,score⟩ := spec
  have tpos : (0 : ℝ≥0) < (τ : ℝ≥0) := by exact_mod_cast τpos
  have positive : 0 < ∑ j, actualDistance A w P j := by
    apply tpos.trans_le
    rw [← atIndex]
    exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i)
  have cap : ((above (actualDistance A w P) (τ : ℝ≥0)).card : ℝ≥0) ≤ m := by
    have d := FiniteHarmonicThreshold.above_card_le (actualDistance A w P) (τ : ℝ≥0)
    rw [Fintype.card_fin] at d
    exact_mod_cast d
  have sum := score.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left cap zero_le) zero_le)
  rw [RationalSparsestVertexRound.scaled_weight, SparsestVertexBridge.totalWeight_div]
  exact FiniteHarmonicThreshold.scaled_mass_le m _ _ _ _ positive tpos sum

theorem mass_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ {m n : ℕ} (A : Adjacency n) (w c : Row n)
      (P : Vector (Fin n × Fin n) m) (_distinct : Function.Injective fun j : Fin m => P[j.val])
      {i : Fin m} {τ : ℚ≥0}, choose A w P = .threshold i τ →
      expectedSparsity (scaled A w c τ) (demandSet P) .mass ≤
        K*(n : ℝ)^ε*(harmonicWeight m : ℝ)^(3/2 : ℝ)*(normalizedMass A w P : ℝ)^(1/2 : ℝ)*
          ((weightedCost (weights c) (weights w) : ℝ) / ∑ j, (actualDistance A w P j : ℝ)) := by
  intro ε positive
  obtain ⟨K,Kpos,rounding⟩ := EncodedWeightedRounding.expected_cost_uniform ε positive
  refine ⟨K,Kpos,?_⟩
  intro m n A w c P distinct i τ chosen
  let D := scaled A w c τ
  let H : ℝ := harmonicWeight m
  let M : ℝ := normalizedMass A w P
  let ratio := (weightedCost (weights c) (weights w) : ℝ) / ∑ j, (actualDistance A w P j : ℝ)
  have hH : 0 ≤ H := NNReal.coe_nonneg _
  have hM : 0 ≤ M := NNReal.coe_nonneg _
  have upper : (totalWeight D.weight : ℝ) ≤ H*M := by exact_mod_cast scaled_mass_le A w c P chosen
  let factor := K*(n : ℝ)^ε*(H*M)^(1/2 : ℝ)
  have fee : expectedPrice D .mass ≤ factor*(weightedCost D.cost D.weight : ℝ) := by
    refine (rounding n D).trans ?_
    unfold factor
    gcongr
  have estimate := transfer A w c P distinct chosen .mass (factor := factor) (by positivity) fee
  refine estimate.trans_eq ?_
  have harmonic : H^(1/2 : ℝ)*H = H^(3/2 : ℝ) := calc
    _ = H^(1/2 : ℝ)*H^(1 : ℝ) := by rw [Real.rpow_one]
    _ = _ := by
      rw [← Real.rpow_add_of_nonneg hH (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : 0 ≤ (1 : ℝ))]
      norm_num
  change factor*H*ratio = K*(n : ℝ)^ε*H^(3/2 : ℝ)*M^(1/2 : ℝ)*ratio
  rw [show factor = K*(n : ℝ)^ε*(H*M)^(1/2 : ℝ) from rfl, Real.mul_rpow hH hM]
  calc
    _ = K*(n : ℝ)^ε*(H^(1/2 : ℝ)*H)*M^(1/2 : ℝ)*ratio := by ring
    _ = _ := by rw [harmonic]

end
end DirectedFlowCutGap.RationalSparsestVertexExpectation
