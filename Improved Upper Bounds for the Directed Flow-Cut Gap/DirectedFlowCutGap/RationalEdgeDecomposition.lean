import DirectedFlowCutGap.RationalEdgeThresholds
import DirectedFlowCutGap.RationalWeakHorizon

/-!
# An explicit rational edge-family driver

The driver prepares the paper's tiny-weight modification and runs the
rational recurrence for its computed horizon. Its input-dependent
contract is the all-cost cut routine. The current encoded randomized
solver has a failure probability and requires a separate adaptive
success proof before supplying that contract.
-/

namespace DirectedFlowCutGap.RationalEdgeDecomposition

open scoped NNReal NNRat BigOperators
open BinaryFractionalWalkOracle RationalEdgeThresholds RationalWeakFamily

def weightQ {n : ℕ} (w : Weights n) (e : Fin n × Fin n) : ℚ≥0 :=
  (decodeCost (cost w) e).value

def originalWeight {n : ℕ} (adjacency : Adjacency n) (w : Weights n) (e : Fin n × Fin n) : ℚ≥0 :=
  if adjacency[e.1.val][e.2.val] then weightQ w e else 0

def modifiedWeight {n : ℕ} (adjacency : Adjacency n) (w : Weights n) (e : Fin n × Fin n) : ℚ≥0 :=
  let q := originalWeight adjacency w e
  if q ≤ (2 * (n : ℚ≥0))⁻¹ then 0 else 2 * q

def originalTotal {n : ℕ} (adjacency : Adjacency n) (w : Weights n) : ℚ≥0 :=
  ∑ e, originalWeight adjacency w e

theorem originalWeight_eq {n : ℕ} (adjacency : Adjacency n) (w : Weights n) (e : Fin n × Fin n) :
    (originalWeight adjacency w e : ℝ≥0) = actualEdgeWeight (graph adjacency) (weights w) e := by
  by_cases h : (graph adjacency).Adj e.1 e.2
  · have hh : adjacency[e.1.val][e.2.val] = true := h
    rw [actualEdgeWeight_of_adj _ _ h]
    simp [originalWeight, hh, weights, weightQ]
  · have hh : adjacency[e.1.val][e.2.val] ≠ true := h
    rw [actualEdgeWeight_of_not_adj _ _ h]
    simp [originalWeight, hh]

theorem modifiedWeight_eq {n : ℕ} (adjacency : Adjacency n) (w : Weights n) (e : Fin n × Fin n) :
    (modifiedWeight adjacency w e : ℝ≥0) =
      actualEdgeWeight (graph adjacency) (TinyEdgePreprocessing.weight (weights w)) e := by
  classical
  by_cases h : (graph adjacency).Adj e.1 e.2
  · rw [actualEdgeWeight_of_adj _ _ h]
    have hval : (originalWeight adjacency w e : ℝ≥0) = weights w e :=
      (originalWeight_eq adjacency w e).trans (actualEdgeWeight_of_adj _ _ h)
    have hcmp : originalWeight adjacency w e ≤ (2 * (n : ℚ≥0))⁻¹ ↔
        weights w e ≤ (2 * (n : ℝ≥0))⁻¹ := by
      rw [← NNRat.cast_le (K := ℝ≥0), hval]
      simp
    unfold modifiedWeight TinyEdgePreprocessing.weight
    simp only [Fintype.card_fin, hcmp]
    split <;> simp [hval]
  · rw [actualEdgeWeight_of_not_adj _ _ h]
    have hz : originalWeight adjacency w e = 0 := by
      exact_mod_cast (originalWeight_eq adjacency w e).trans (actualEdgeWeight_of_not_adj _ _ h)
    simp [modifiedWeight, hz]

theorem modified_le {n : ℕ} (adjacency : Adjacency n) (w : Weights n) (e : Fin n × Fin n) :
    modifiedWeight adjacency w e ≤ 2 * originalWeight adjacency w e := by
  unfold modifiedWeight
  dsimp only
  split
  · exact zero_le
  · rfl

theorem modified_positive {n : ℕ} (adjacency : Adjacency n) (w : Weights n)
    (e : Fin n × Fin n) (he : 0 < modifiedWeight adjacency w e) :
    (n : ℚ≥0)⁻¹ ≤ modifiedWeight adjacency w e := by
  have hp : 0 < (modifiedWeight adjacency w e : ℝ≥0) :=
    NNRat.cast_pos.mpr he
  rw [modifiedWeight_eq] at hp
  have ha : (graph adjacency).Adj e.1 e.2 := by
    by_contra hh
    rw [actualEdgeWeight_of_not_adj _ _ hh] at hp
    exact (lt_irrefl 0 hp)
  rw [actualEdgeWeight_of_adj _ _ ha] at hp
  have h := TinyEdgePreprocessing.positive_weight_lower (weights w) e hp
  have heq := (modifiedWeight_eq adjacency w e).trans
    (actualEdgeWeight_of_adj (graph adjacency) (TinyEdgePreprocessing.weight (weights w)) ha)
  rw [Fintype.card_fin, ← heq] at h
  exact (NNRat.cast_le (K := ℝ≥0)).mp (by simpa only [NNRat.cast_inv, NNRat.cast_natCast] using h)

theorem modified_feasible {n : ℕ} (adjacency : Adjacency n) (w : Weights n) :
    IsFractionalEdgeCut (graph adjacency) (fun e => (modifiedWeight adjacency w e : ℝ≥0))
      {e | e ∈ demands adjacency w} := by
  rw [isFractionalEdgeCut_iff]
  intro s t h p
  let v := TinyEdgePreprocessing.weight (weights w)
  have hthreshold := TinyEdgePreprocessing.thresholdDemands_subset (graph adjacency) (weights w)
    ((demands_iff adjacency w (s, t)).mp h)
  change 1 ≤ edgeDistance (graph adjacency) v s t at hthreshold
  have hf : 1 ≤ p.edgeWeight v := by
    apply (coe_le_edgeDistance_iff (graph adjacency) v s t 1).mp _ p
    simpa only [ENNReal.coe_one] using hthreshold
  have he : p.edgeWeight (fun e => (modifiedWeight adjacency w e : ℝ≥0)) = p.edgeWeight v := by
    unfold SimplePath.edgeWeight
    apply Finset.sum_congr rfl
    intro e he
    have ha : (graph adjacency).Adj e.1 e.2 := (mem_graphEdges _ _).mp (p.edges_subset_graphEdges he)
    exact (modifiedWeight_eq adjacency w e).trans (actualEdgeWeight_of_adj _ _ ha)
  exact he.symm ▸ hf

def Good {n : ℕ} (adjacency : Adjacency n) (w : Weights n) (X : Finset (Fin n × Fin n)) : Prop :=
  X ⊆ graphEdges (graph adjacency) ∧ IsIntegralEdgeCut (graph adjacency) X
    {e | e ∈ demands adjacency w}

def build {n : ℕ} (adjacency : Adjacency n) (w : Weights n) (α : ℚ≥0)
    (oracle : ((Fin n × Fin n) → ℚ≥0) → Finset (Fin n × Fin n)) : History (Fin n × Fin n) :=
  runEdge n (originalTotal adjacency w) α (modifiedWeight adjacency w) oracle

theorem build_spec {n : ℕ} (hn : 0 < n) (adjacency : Adjacency n) (w : Weights n) (α : ℚ≥0)
    (oracle : ((Fin n × Fin n) → ℚ≥0) → Finset (Fin n × Fin n)) (hα : 1 ≤ α)
    (hOracle : ∀ c, Good adjacency w (oracle c) ∧
      (∑ e ∈ oracle c, c e) ≤ α * ∑ e, c e * modifiedWeight adjacency w e)
    (hReal : HasEdgeRoundingFactor (graph adjacency) (TinyEdgePreprocessing.weight (weights w)) (α : ℝ)) :
    let result := build adjacency w α oracle
    (∀ X ∈ result.cuts, Good adjacency w X ∧ ∀ e ∈ X, 0 < modifiedWeight adjacency w e) ∧
      (∀ e, (result.cuts.countP (fun X => decide (e ∈ X)) : ℝ) / (result.cuts.length : ℝ) ≤
        8 * (originalWeight adjacency w e : ℝ) * α) := by
  let m := modifiedWeight adjacency w
  let W := originalTotal adjacency w
  have hw : (∑ e, m e) ≤ 2 * W := by
    unfold W originalTotal
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun e _ => modified_le adjacency w e)
  have hReal' (c : Fin n × Fin n → ℝ) (hc : ∀ e, 0 ≤ c e) : ∃ X : Finset (Fin n × Fin n),
      Good adjacency w X ∧ (∑ e ∈ X, c e) ≤ (α : ℝ) * mwPotential (fun e => (m e : ℝ)) c := by
    obtain ⟨X, ⟨hX, hcut⟩, hprice⟩ := hReal.real_cost_round c hc
    refine ⟨X, ⟨hX, fun s t hst => hcut s t (TinyEdgePreprocessing.thresholdDemands_subset _ _
      ((demands_iff adjacency w (s, t)).mp hst))⟩, ?_⟩
    have he (e : Fin n × Fin n) : (m e : ℝ) =
        (actualEdgeWeight (graph adjacency) (TinyEdgePreprocessing.weight (weights w)) e : ℝ) := by
      exact congrArg (fun x : ℝ≥0 => (x : ℝ)) (modifiedWeight_eq adjacency w e)
    simpa only [he] using hprice
  have hcard : Fintype.card (Fin n × Fin n) = n * n := by simp
  obtain ⟨hgood, hr⟩ := runEdge_spec hn hcard W α m (Good adjacency w) oracle hα hw
    (modified_positive adjacency w) hOracle hReal'
  refine ⟨hgood, ?_⟩
  intro e
  rw [build, runEdge_length]
  have he : (m e : ℝ) ≤ 2 * (originalWeight adjacency w e : ℝ) := by
    exact_mod_cast modified_le adjacency w e
  refine (hr e).trans ?_
  calc
    _ ≤ 4 * (2 * (originalWeight adjacency w e : ℝ)) * α :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num)) (NNRat.cast_nonneg _)
    _ = _ := by ring

end DirectedFlowCutGap.RationalEdgeDecomposition
