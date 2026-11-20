import DirectedFlowCutGap.RationalSparsestEdgeRound

/-! Transfer the existing expected price guarantees to the sparsity of
the cut law at the threshold selected by the executable routine. -/
namespace DirectedFlowCutGap.RationalSparsestEdgeExpectation

noncomputable section
open scoped BigOperators NNReal NNRat
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open RationalSparsestEdgeThreshold (actualDistance choose)
open RationalSparsestEdgeRound (scaled tree demandSet)
open FiniteHarmonicThreshold (above harmonicWeight)
open FiniteDrawTrees (ideal)
open FiniteAmplification (expectedCost)
open EncodedEdgeRounding (expectedPrice selectedEdges)

def law {n : ℕ} (D : EncodedEdgeGadget.Input n) (mode : ChargedVertexModes.Mode) : PMF (Finset (Fin n × Fin n)) :=
  (ideal (tree D mode)).map selectedEdges

private theorem support_cut {n : ℕ} (D : EncodedEdgeGadget.Input n) (mode : ChargedVertexModes.Mode)
    {X : Finset (Fin n × Fin n)} (present : X ∈ (law D mode).support) :
    IsIntegralEdgeCut D.graph X (edgeThresholdDemands D.graph D.weight) := by
  obtain ⟨mask,seen,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp present
  cases mode
  · exact (EncodedEdgeRounding.support_valid D (fun _ => EncodedWeightedRounding.tree)
      (fun I _ h => EncodedWeightedRounding.support_valid I h) seen).2
  · exact (EncodedEdgeRounding.support_valid D (fun _ => EncodedSizeRounding.tree)
      (fun I _ h => EncodedSizeRounding.support_valid I h) seen).2

def expectedSparsity {n : ℕ} (D : EncodedEdgeGadget.Input n) (P : Finset (Fin n × Fin n))
    (mode : ChargedVertexModes.Mode) : ℝ :=
  expectedCost (law D mode) (fun X => (SparsestEdgeBridge.sparsity D.graph D.cost P X : ℝ))

theorem ratio_le {m n : ℕ} (A : Adjacency n) (w c : Weights n)
    (pairs : Vector (Fin n × Fin n) m) (distinct : Function.Injective fun j : Fin m => pairs[j.val])
    {i : Fin m} {τ : ℚ≥0} (chosen : choose A w pairs=.threshold i τ)
    (mode : ChargedVertexModes.Mode) :
    let D := scaled A w c τ
    let k := (above (actualDistance A w pairs) (τ : ℝ≥0)).card
    expectedSparsity D (demandSet pairs) mode ≤ expectedPrice D (fun r => ChargedVertexModes.round r mode)/(k : ℝ) := by
  classical
  let D := scaled A w c τ
  let k := (above (actualDistance A w pairs) (τ : ℝ≥0)).card
  have spec := RationalSparsestEdgeThreshold.choose_spec A w pairs
  rw [chosen] at spec
  have positive : 0<k := spec.2.2.2.1
  let P := demandSet pairs
  let p := law D mode
  let price (X : Finset (Fin n × Fin n)) : ℝ := edgeCutCost D.graph D.cost X
  change expectedSparsity D P mode ≤ expectedPrice D _/(k : ℝ)
  have actual : expectedPrice D (fun r => ChargedVertexModes.round r mode)=expectedCost p price := rfl
  rw [actual,expectedSparsity,expectedCost,expectedCost,Finset.sum_div]
  apply Finset.sum_le_sum
  intro X _
  change (p X).toReal * (SparsestEdgeBridge.sparsity D.graph D.cost P X : ℝ) ≤
    (p X).toReal * price X / (k : ℝ)
  by_cases atom : p X=0
  · simp [atom]
  · have valid := support_cut D mode ((PMF.mem_support_iff p X).mpr atom)
    have count := RationalSparsestEdgeRound.count_le A w c pairs distinct chosen valid
    have denominator : (k : ℝ) ≤ ((SparsestEdgeBridge.separated D.graph P X).card : ℝ) := by
      change (k : ℝ) ≤ ((SparsestEdgeBridge.separated (graph A) P X).card : ℝ)
      exact_mod_cast count
    have nonzero : (0 : ℝ)<(k : ℝ) := by exact_mod_cast positive
    have price_nonneg : 0≤price X := NNReal.coe_nonneg _
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    simp only [SparsestEdgeBridge.sparsity,NNReal.coe_div,NNReal.coe_natCast]
    exact div_le_div_of_nonneg_left price_nonneg nonzero denominator

private theorem transfer {m n : ℕ} (A : Adjacency n) (w c : Weights n)
    (pairs : Vector (Fin n × Fin n) m) (distinct : Function.Injective fun j : Fin m => pairs[j.val])
    {i : Fin m} {τ : ℚ≥0} (chosen : choose A w pairs=.threshold i τ) (mode : ChargedVertexModes.Mode)
    {factor : ℝ} (nonnegative : 0≤factor)
    (price : let D := scaled A w c τ
      expectedPrice D (fun r => ChargedVertexModes.round r mode) ≤
        factor*(weightedEdgeCost D.graph D.cost D.weight : ℝ)) :
    expectedSparsity (scaled A w c τ) (demandSet pairs) mode ≤
      factor*(harmonicWeight m : ℝ)*((weightedEdgeCost (graph A) (weights c) (weights w) : ℝ)/
        ∑ j, (actualDistance A w pairs j : ℝ)) := by
  let D := scaled A w c τ
  let k := (above (actualDistance A w pairs) (τ : ℝ≥0)).card
  let C : ℝ := weightedEdgeCost (graph A) (weights c) (weights w)
  let S : ℝ := ∑ j, (actualDistance A w pairs j : ℝ)
  let H : ℝ := harmonicWeight m
  have spec := RationalSparsestEdgeThreshold.choose_spec A w pairs
  rw [chosen] at spec
  obtain ⟨_,distance,τpos,nonempty,score⟩ := spec
  have cast : ((τ : ℝ≥0) : ℝ)=(τ : ℝ) := rfl
  have τReal : (0 : ℝ)<τ := by exact_mod_cast τpos
  have kReal : (0 : ℝ)<k := by exact_mod_cast nonempty
  have Spos : 0<S := by
    have inside : (actualDistance A w pairs i : ℝ) ≤ S :=
      Finset.single_le_sum (fun j _ => (actualDistance A w pairs j).coe_nonneg) (Finset.mem_univ i)
    rw [distance,cast] at inside
    exact τReal.trans_le inside
  have budget : S≤H*((τ : ℝ)*(k : ℝ)) := by
    have realScore := NNReal.coe_le_coe.mpr score
    simpa only [NNReal.coe_sum,NNReal.coe_mul,cast,NNReal.coe_natCast] using realScore
  have normalized : (weightedEdgeCost D.graph D.cost D.weight : ℝ)=C/(τ : ℝ) := by
    change (weightedEdgeCost (scaled A w c τ).graph (scaled A w c τ).cost (scaled A w c τ).weight : ℝ)=_
    rw [RationalSparsestEdgeRound.scaled_graph,RationalSparsestEdgeRound.scaled_price,
      RationalSparsestEdgeRound.scaled_weight,SparsestEdgeBridge.weightedEdgeCost_div]
    simp only [NNReal.coe_div,cast,C]
  have split : 1/((τ : ℝ)*(k : ℝ))≤H/S := by
    refine (div_le_div_iff₀ (mul_pos τReal kReal) Spos).mpr ?_
    simpa only [one_mul] using budget
  calc
    _ ≤ expectedPrice D (fun r => ChargedVertexModes.round r mode)/(k : ℝ) :=
      ratio_le A w c pairs distinct chosen mode
    _ ≤ (factor*(C/(τ : ℝ)))/(k : ℝ) :=
      div_le_div_of_nonneg_right (price.trans_eq (by rw [normalized])) kReal.le
    _ = (factor*C)*(1/((τ : ℝ)*(k : ℝ))) := by ring
    _ ≤ (factor*C)*(H/S) := mul_le_mul_of_nonneg_left split (mul_nonneg nonnegative (NNReal.coe_nonneg _))
    _ = _ := by ring

theorem size_uniform :
    ∀ ε : ℝ, 0<ε → ∃ K : ℝ, 0<K ∧ ∀ {m n : ℕ} (A : Adjacency n) (w c : Weights n)
      (pairs : Vector (Fin n × Fin n) m) (_distinct : Function.Injective fun j : Fin m => pairs[j.val])
      {i : Fin m} {τ : ℚ≥0}, choose A w pairs=.threshold i τ →
      expectedSparsity (scaled A w c τ) (demandSet pairs) .size ≤
        K*(n : ℝ)^(1/3+ε)*(harmonicWeight m : ℝ)*
          ((weightedEdgeCost (graph A) (weights c) (weights w) : ℝ)/
            ∑ j, (actualDistance A w pairs j : ℝ)) := by
  intro ε positive
  obtain ⟨K,Kpos,rounding⟩ := EncodedEdgeRounding.size_expected_uniform ε positive
  refine ⟨K,Kpos,?_⟩
  intro m n A w c pairs distinct i τ chosen
  exact transfer A w c pairs distinct chosen .size (by positivity) (rounding n (scaled A w c τ))

def normalizedMass {m n : ℕ} (A : Adjacency n) (w : Weights n) (pairs : Vector (Fin n × Fin n) m) : ℝ≥0 :=
  (m : ℝ≥0)*totalEdgeWeight (graph A) (weights w)/∑ j, actualDistance A w pairs j

theorem scaled_mass_le {m n : ℕ} (A : Adjacency n) (w c : Weights n)
    (pairs : Vector (Fin n × Fin n) m) {i : Fin m} {τ : ℚ≥0} (chosen : choose A w pairs=.threshold i τ) :
    totalEdgeWeight (scaled A w c τ).graph (scaled A w c τ).weight ≤
      harmonicWeight m * normalizedMass A w pairs := by
  have spec := RationalSparsestEdgeThreshold.choose_spec A w pairs
  rw [chosen] at spec
  obtain ⟨_,atIndex,τpos,_,score⟩ := spec
  have tpos : (0 : ℝ≥0)<(τ : ℝ≥0) := by exact_mod_cast τpos
  have positive : 0<∑ j, actualDistance A w pairs j := by
    apply tpos.trans_le
    rw [←atIndex]
    exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i)
  have cap : ((above (actualDistance A w pairs) (τ : ℝ≥0)).card : ℝ≥0) ≤ m := by
    have d := FiniteHarmonicThreshold.above_card_le (actualDistance A w pairs) (τ : ℝ≥0)
    rw [Fintype.card_fin] at d
    exact_mod_cast d
  have bound := score.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left cap zero_le) zero_le)
  rw [RationalSparsestEdgeRound.scaled_graph,RationalSparsestEdgeRound.scaled_weight,
    SparsestEdgeBridge.totalEdgeWeight_div]
  exact FiniteHarmonicThreshold.scaled_mass_le m _ _ _ _ positive tpos bound

theorem mass_uniform :
    ∀ ε : ℝ, 0<ε → ∃ K : ℝ, 0<K ∧ ∀ {m n : ℕ} (A : Adjacency n) (w c : Weights n)
      (pairs : Vector (Fin n × Fin n) m) (_distinct : Function.Injective fun j : Fin m => pairs[j.val])
      {i : Fin m} {τ : ℚ≥0}, choose A w pairs=.threshold i τ →
      expectedSparsity (scaled A w c τ) (demandSet pairs) .mass ≤
        K*(n : ℝ)^ε*(harmonicWeight m : ℝ)^(3/2 : ℝ)*(normalizedMass A w pairs : ℝ)^(1/2 : ℝ)*
          ((weightedEdgeCost (graph A) (weights c) (weights w) : ℝ)/
            ∑ j, (actualDistance A w pairs j : ℝ)) := by
  intro ε pos
  obtain ⟨K,Kpos,rounding⟩ := EncodedEdgeRounding.mass_expected_uniform ε pos
  refine ⟨K,Kpos,?_⟩
  intro m n A w c pairs distinct i τ chosen
  let D := scaled A w c τ
  let H : ℝ := harmonicWeight m
  let M : ℝ := normalizedMass A w pairs
  let ratio : ℝ := (weightedEdgeCost (graph A) (weights c) (weights w) : ℝ)/
    ∑ j, (actualDistance A w pairs j : ℝ)
  have hH : 0≤H := NNReal.coe_nonneg _
  have hM : 0≤M := NNReal.coe_nonneg _
  have upper : (totalEdgeWeight D.graph D.weight : ℝ) ≤ H*M := by
    exact_mod_cast scaled_mass_le A w c pairs chosen
  let factor := K*(n : ℝ)^ε*(H*M)^(1/2 : ℝ)
  have price : expectedPrice D (fun _ => EncodedWeightedRounding.tree) ≤
      factor*(weightedEdgeCost D.graph D.cost D.weight : ℝ) := by
    refine (rounding n D).trans ?_
    unfold factor
    gcongr
  have result := transfer A w c pairs distinct chosen .mass (factor := factor) (by positivity) price
  refine result.trans_eq ?_
  have harmonic : H^(1/2 : ℝ)*H=H^(3/2 : ℝ) := by
    calc
      _ = H^(1/2 : ℝ)*H^(1 : ℝ) := by rw [Real.rpow_one]
      _ = H^(3/2 : ℝ) := by
        rw [←Real.rpow_add_of_nonneg hH (by norm_num : 0≤(1/2 : ℝ)) (by norm_num : 0≤(1 : ℝ))]
        norm_num
  change factor*H*ratio = K*(n : ℝ)^ε*H^(3/2 : ℝ)*M^(1/2 : ℝ)*ratio
  rw [show factor=K*(n : ℝ)^ε*(H*M)^(1/2 : ℝ) from rfl,Real.mul_rpow hH hM]
  calc
    _ = K*(n : ℝ)^ε*(H^(1/2 : ℝ)*H)*M^(1/2 : ℝ)*ratio := by ring
    _ = _ := by rw [harmonic]

end
end DirectedFlowCutGap.RationalSparsestEdgeExpectation
