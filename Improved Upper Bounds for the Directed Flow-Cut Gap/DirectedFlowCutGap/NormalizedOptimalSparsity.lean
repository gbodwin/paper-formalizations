import DirectedFlowCutGap.NormalizedEdgeLPRound
import DirectedFlowCutGap.RationalSparsestFairTape

/-! Apply the finite-tape deviation bound to a rounded optimal normalized
rational edge assignment. -/
namespace DirectedFlowCutGap.NormalizedOptimalSparsity

noncomputable section
open scoped BigOperators NNReal NNRat
open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open RationalSparsestEdgeThreshold (choose actualDistance)
open RationalSparsestEdgeRound (Result Mask scaled round tapeBudget drawBound demandSet)
open FiniteHarmonicThreshold (harmonicWeight)
open RationalSparsestEdgeExpectation (expectedSparsity normalizedMass)
open RationalSparsestFairTape (bad)
open FiniteAmplification (probability)

def observedCut {n : ℕ} (result : ℚ × Result n) : Option (Mask n) :=
  match result.2 with
  | .cut mask _ => some mask
  | .zeroDistance => none

theorem observation {m n : ℕ} (A : Adjacency n) (c : Weights n)
    (pairs : Vector (Fin n × Fin n) m) {q : ℚ} {w : Weights n}
    (optimum : NormalizedEdgeLP.minimize A c pairs.get (m : ℚ≥0)=some (q,w))
    {i : Fin m} {τ : ℚ≥0} (threshold : choose A w pairs=.threshold i τ)
    (mode : ChargedVertexModes.Mode) (T : ℕ) (bits : Bits) :
    (NormalizedEdgeLPRound.runOptimal A c pairs mode T bits).bind observedCut =
      (round (scaled A w c τ) mode T bits).map Prod.fst := by
  simp only [NormalizedEdgeLPRound.runOptimal,optimum,Option.bind_some,RationalSparsestEdgeRound.run,threshold]
  cases round (scaled A w c τ) mode T bits <;> rfl

private theorem distance_sum_ge {m n : ℕ} (A : Adjacency n) (w : Weights n)
    (pairs : Vector (Fin n × Fin n) m)
    (normalized : ((m : ℚ≥0) : ℝ≥0) ≤
      ∑ j : Fin m, SparsestEdgeBridge.demandDistance (graph A) (weights w) (pairs.get j)) :
    (m : ℝ) ≤ ∑ j, (actualDistance A w pairs j : ℝ) := by
  have entry (j : Fin m) : pairs.get j = pairs[j.val] := by
    cases j
    rfl
  have lift := NNReal.coe_le_coe.mpr normalized
  simpa only [NNRat.cast_natCast, NNReal.coe_natCast, NNReal.coe_sum, actualDistance, entry] using lift

private theorem total_positive {n : ℕ} (A : Adjacency n) (w c : Weights n)
    (price : 0 < weightedEdgeCost (graph A) (weights c) (weights w)) :
    0 < totalEdgeWeight (graph A) (weights w) := by
  by_contra! absent
  have zero : totalEdgeWeight (graph A) (weights w) = 0 := le_antisymm absent zero_le
  have each : ∀ e ∈ graphEdges (graph A), weights w e = 0 := by
    intro e he
    have term : weights w e ≤ totalEdgeWeight (graph A) (weights w) :=
      Finset.single_le_sum (fun _ _ => zero_le) he
    rw [zero] at term
    exact le_antisymm term zero_le
  have free : weightedEdgeCost (graph A) (weights c) (weights w) = 0 := by
    unfold weightedEdgeCost
    exact Finset.sum_eq_zero (fun e he => by rw [each e he, mul_zero])
  exact (ne_of_gt price) free

theorem optimal_size_probability :
    ∀ ε : ℝ, 0<ε → ∃ K : ℝ, 0<K ∧ ∀ {m n : ℕ} (A : Adjacency n) (c : Weights n)
      (pairs : Vector (Fin n × Fin n) m)
      (_distinct : Function.Injective fun j : Fin m => pairs[j.val])
      (_reachable : ∀ j : Fin m, Nonempty (SimplePath (graph A) pairs[j.val].1 pairs[j.val].2))
      {q : ℚ} {w : Weights n}, 0<q → NormalizedEdgeLP.minimize A c pairs.get (m : ℚ≥0)=some (q,w) →
      ∀ {i : Fin m} {τ : ℚ≥0}, choose A w pairs=.threshold i τ → ∀ T : ℕ,
        let B := K*(n : ℝ)^(1/3+ε)*(harmonicWeight m : ℝ)*((q : ℝ)/(m : ℝ))
        probability ((EncodedSolverBits.fairTape (tapeBudget n T)).map
          (fun bits => (NormalizedEdgeLPRound.runOptimal A c pairs .size T bits).bind observedCut))
          (bad (scaled A w c τ) (demandSet pairs) (2*B)) ≤
            1/2+(drawBound n : ℝ)*((1 : ℝ)/2)^T := by
  intro ε positive
  obtain ⟨K,Kpos,guarantee⟩ := RationalSparsestEdgeExpectation.size_uniform ε positive
  refine ⟨K,Kpos,?_⟩
  intro m n A c pairs distinct reachable q w qpos optimum i τ threshold T
  let D := scaled A w c τ
  let H : ℝ := harmonicWeight m
  let S : ℝ := ∑ j, (actualDistance A w pairs j : ℝ)
  let factor := K*(n : ℝ)^(1/3+ε)*H
  let B := factor*((q : ℝ)/(m : ℝ))
  have mpos : 0 < m := (Nat.zero_le _).trans_lt i.isLt
  have npos : 0 < n := (Nat.zero_le _).trans_lt (pairs[i.val].1).isLt
  have positiveH : 0<H := by
    exact NNReal.coe_pos.mpr (FiniteHarmonicThreshold.harmonicWeight_pos mpos)
  have atOptimum := NormalizedEdgeLP.minimize_attained A c pairs.get (m : ℚ≥0) reachable optimum
  have price := atOptimum.2.1
  have sum : (m : ℝ) ≤ S := distance_sum_ge A w pairs atOptimum.1
  have theory := guarantee A w c pairs distinct threshold
  rw [price] at theory
  have paid : expectedSparsity D (demandSet pairs) .size≤B := by
    refine theory.trans ?_
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (by exact_mod_cast qpos.le) (by exact_mod_cast mpos) sum) (by positivity)
  simp only [observation A c pairs optimum threshold]
  exact RationalSparsestFairTape.probability_cost D (demandSet pairs) .size T B (by positivity) paid

theorem optimal_mass_probability :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ {m n : ℕ} (A : Adjacency n) (c : Weights n)
      (pairs : Vector (Fin n × Fin n) m)
      (_distinct : Function.Injective fun j : Fin m => pairs[j.val])
      (_reachable : ∀ j : Fin m, Nonempty (SimplePath (graph A) pairs[j.val].1 pairs[j.val].2))
      {q : ℚ} {w : Weights n}, 0 < q → NormalizedEdgeLP.minimize A c pairs.get (m : ℚ≥0) = some (q,w) →
      ∀ {i : Fin m} {τ : ℚ≥0}, choose A w pairs = .threshold i τ → ∀ T : ℕ,
        let B := K * (n : ℝ)^ε * (harmonicWeight m : ℝ)^(3/2 : ℝ) *
          (normalizedMass A w pairs : ℝ)^(1/2 : ℝ) * ((q : ℝ)/(m : ℝ))
        probability ((EncodedSolverBits.fairTape (tapeBudget n T)).map
          (fun bits => (NormalizedEdgeLPRound.runOptimal A c pairs .mass T bits).bind observedCut))
          (bad (scaled A w c τ) (demandSet pairs) (2*B)) ≤
            1/2+(drawBound n : ℝ)*((1 : ℝ)/2)^T := by
  intro ε positive
  obtain ⟨K,Kpos,guarantee⟩ := RationalSparsestEdgeExpectation.mass_uniform ε positive
  refine ⟨K,Kpos,?_⟩
  intro m n A c pairs distinct reachable q w qpos optimum i τ threshold T
  let D := scaled A w c τ
  let H : ℝ := harmonicWeight m
  let S : ℝ := ∑ j, (actualDistance A w pairs j : ℝ)
  let M : ℝ := normalizedMass A w pairs
  let factor := K * (n : ℝ)^ε * H^(3/2 : ℝ) * M^(1/2 : ℝ)
  let B := factor * ((q : ℝ)/(m : ℝ))
  have mpos : 0 < m := (Nat.zero_le _).trans_lt i.isLt
  have npos : 0 < n := (Nat.zero_le _).trans_lt (pairs[i.val].1).isLt
  have positiveH : 0 < H := NNReal.coe_pos.mpr (FiniteHarmonicThreshold.harmonicWeight_pos mpos)
  have atOptimum := NormalizedEdgeLP.minimize_attained A c pairs.get (m : ℚ≥0) reachable optimum
  have price := atOptimum.2.1
  have sum : (m : ℝ) ≤ S := distance_sum_ge A w pairs atOptimum.1
  have Spos : 0 < S := (show (0 : ℝ) < m by exact_mod_cast mpos).trans_le sum
  have weightedPos : 0 < weightedEdgeCost (graph A) (weights c) (weights w) := by
    apply NNReal.coe_pos.mp
    rw [price]
    exact_mod_cast qpos
  have massPos := total_positive A w c weightedPos
  have positiveM : 0 < M := by
    change (0 : ℝ) < (normalizedMass A w pairs : ℝ)
    simp only [normalizedMass, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_sum]
    exact div_pos (by positivity) Spos
  have theory := guarantee A w c pairs distinct threshold
  rw [price] at theory
  have paid : expectedSparsity D (demandSet pairs) .mass ≤ B := by
    refine theory.trans ?_
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (by exact_mod_cast qpos.le) (by exact_mod_cast mpos) sum) (by positivity)
  simp only [observation A c pairs optimum threshold]
  exact RationalSparsestFairTape.probability_cost D (demandSet pairs) .mass T B (by positivity) paid

end
end DirectedFlowCutGap.NormalizedOptimalSparsity
