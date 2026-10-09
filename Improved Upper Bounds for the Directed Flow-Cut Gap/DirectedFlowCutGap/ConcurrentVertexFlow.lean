import DirectedFlowCutGap.ConcurrentDuality
import DirectedFlowCutGap.SparsestVertexCorollary
import DirectedFlowCutGap.PathExtraction

/-!
# Actual vertex concurrent flow and fractional sparsest optima

Path variables are actual directed simple paths of each demand. Only internal
vertices consume capacity. The attained optimum is normalized by SUM distances
one, and its raw mass must be multiplied by the demand count for the mass-sensitive
rounding bound. Reachability and positive-distance feasibility are explicit.
-/

namespace DirectedFlowCutGap.ConcurrentVertexFlow
noncomputable section
open scoped BigOperators NNReal ENNReal
attribute [local instance] Classical.propDecidable
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

abbrev Path (G : Digraph V) (P : Finset (V × V)) (d : P) :=
  SimplePath G d.val.1 d.val.2

instance pathFintype (G : Digraph V) (P : Finset (V × V)) (d : P) :
    Fintype (Path G P d) := Fintype.ofFinite _

/-- One unit of internal-vertex capacity per unit of routed path flow. -/
def incidence (G : Digraph V) (P : Finset (V × V)) (d : P) (v : V)
    (p : Path G P d) : ℕ := if v ∈ p.internalVertices then 1 else 0

abbrev Flow (G : Digraph V) (P : Finset (V × V)) := ConcurrentProfiles.Flow (Path G P)

abbrev IsConcurrent (G : Digraph V) (P : Finset (V × V)) (c : V → ℝ≥0)
    (f : Flow G P) (t : ℝ) := ConcurrentProfiles.IsConcurrent (incidence G P) (fun v => (c v : ℝ)) f t

abbrev IsAtLeastConcurrent (G : Digraph V) (P : Finset (V × V)) (c : V → ℝ≥0)
    (f : Flow G P) (t : ℝ) := ConcurrentProfiles.IsAtLeastConcurrent (incidence G P)
      (fun v => (c v : ℝ)) f t

abbrev Solution (G : Digraph V) (P : Finset (V × V)) (c : V → ℝ≥0) :=
  ConcurrentDuality.Solution (incidence G P) (fun v => (c v : ℝ))

theorem pathWeight_eq (G : Digraph V) (P : Finset (V × V)) (w : V → ℝ≥0)
    (d : P) (p : Path G P d) :
    ConcurrentDuality.pathWeight (incidence G P) (fun v => (w v : ℝ)) d p =
      (p.weight w : ℝ) := by
  simp only [ConcurrentDuality.pathWeight, incidence, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, ite_mul, one_mul, zero_mul, SimplePath.weight, NNReal.coe_sum]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- The certificate uses the existing actual directed-distance definition. -/
theorem actual_distances (G : Digraph V) (P : Finset (V × V)) (w : V → ℝ≥0)
    (hreach : ∀ d : P, Nonempty (Path G P d)) :
    ConcurrentDuality.IsDistance (incidence G P) (fun v => (w v : ℝ))
      (fun d => (SparsestVertexBridge.demandDistance G w d : ℝ)) := by
  intro d
  dsimp only
  obtain ⟨p, hp⟩ := vertexDistance_attained w (hreach d)
  have hp' : SparsestVertexBridge.demandDistance G w d = p.weight w := by
    simp [SparsestVertexBridge.demandDistance, hp]
  refine ⟨fun q => ?_, p, ?_⟩
  · rw [pathWeight_eq, hp']
    apply NNReal.coe_le_coe.mpr
    apply ENNReal.coe_le_coe.mp
    rw [← hp]
    exact vertexDistance_le_weight w q
  · rw [pathWeight_eq, hp']

omit [Fintype V] in
/-- Reachability makes every demanded distance finite for every weighting. -/
theorem finite_distances (G : Digraph V) (P : Finset (V × V)) (w : V → ℝ≥0)
    (hreach : ∀ d : P, Nonempty (Path G P d)) :
    ∀ p ∈ P, vertexDistance G w p.1 p.2 ≠ ⊤ := by
  intro p hp ht
  exact ((vertexDistance_eq_top_iff G w p.1 p.2).mp ht) (hreach ⟨p, hp⟩)

/-- An arbitrary feasible positive assignment suffices to produce the optimizer. -/
theorem exists_solution (G : Digraph V) (P : Finset (V × V)) (c w₀ : V → ℝ≥0)
    (hreach : ∀ d : P, Nonempty (Path G P d))
    (hS : 0 < SparsestVertexBridge.distanceSum G w₀ P) : Nonempty (Solution G P c) := by
  apply ConcurrentDuality.exists_solution (incidence G P) (fun v => (c v : ℝ))
    (fun v => (c v).coe_nonneg) (fun v => (w₀ v : ℝ))
    (fun d => (SparsestVertexBridge.demandDistance G w₀ d : ℝ))
    (fun v => (w₀ v).coe_nonneg) (actual_distances G P w₀ hreach)
  exact_mod_cast hS

/-- One unreachable demand gives attained zero concurrent value and a zero-cost
cut separating a positive number of demands. No infinite-distance sum is used. -/
theorem unreachable_zero_optimum (G : Digraph V) (P : Finset (V × V)) (c : V → ℝ≥0)
    (d : P) (hno : ¬ Nonempty (Path G P d)) :
    IsConcurrent G P c (fun _ _ => 0) 0 ∧
      (∀ f t, IsAtLeastConcurrent G P c f t → t = 0) ∧
      0 < (SparsestVertexBridge.separated G P ∅).card ∧
      SparsestVertexBridge.sparsity G c P ∅ = 0 := by
  let : IsEmpty (Path G P d) := ⟨fun p => hno ⟨p⟩⟩
  refine ⟨ConcurrentProfiles.zero_isConcurrent (incidence G P)
    (fun r => (c r).coe_nonneg), ?_, ?_⟩
  · intro f t hf
    exact ConcurrentProfiles.atLeast_throughput_eq_zero_of_empty_path (incidence G P) hf d
  · exact SparsestVertexBridge.unreachable_zero_sparsity G c (fun _ => 0) P d.val d.property
      ((vertexDistance_eq_top_iff G (fun _ => 0) d.val.1 d.val.2).mpr hno)

variable {G : Digraph V} {P : Finset (V × V)} {c : V → ℝ≥0}

/-- Nonnegative-real length assignment belonging to this particular optimizer. -/
def weight (S : Solution G P c) (v : V) : ℝ≥0 := ⟨S.weight v, S.weight_nonneg v⟩

theorem distance_eq (S : Solution G P c) (hreach : ∀ d : P, Nonempty (Path G P d)) :
    S.distance = fun d : P => (SparsestVertexBridge.demandDistance G (weight S) d : ℝ) :=
  ConcurrentDuality.distances_unique S.distances (actual_distances G P (weight S) hreach)

/-- Sum-one normalization concerns actual graph distances. -/
theorem distanceSum_eq_one (S : Solution G P c)
    (hreach : ∀ d : P, Nonempty (Path G P d)) :
    SparsestVertexBridge.distanceSum G (weight S) P = 1 := by
  apply NNReal.coe_injective
  simp only [SparsestVertexBridge.distanceSum, NNReal.coe_sum, NNReal.coe_one]
  rw [← distance_eq S hreach]
  exact S.distance_sum_one

theorem cost_eq (S : Solution G P c) :
    ConcurrentDuality.cost (fun v => (c v : ℝ)) S.weight = (weightedCost c (weight S) : ℝ) := by
  simp only [ConcurrentDuality.cost, IntegerPackingCovering.coveringValue, weightedCost,
    NNReal.coe_sum]
  rfl

/-- Maximum concurrent flow equals the minimum fractional ratio, using an
attained graph length assignment with sum of demanded distances exactly one. -/
theorem objectives_eq (S : Solution G P c) :
    S.throughput = (weightedCost c (weight S) : ℝ) := by
  rw [S.objectives_eq, cost_eq]

/-- Optimality is against every positive finite-distance fractional assignment. -/
theorem ratio_minimal (S : Solution G P c)
    (hreach : ∀ d : P, Nonempty (Path G P d)) (w : V → ℝ≥0)
    (hS : 0 < SparsestVertexBridge.distanceSum G w P) :
    weightedCost c (weight S) ≤ weightedCost c w / SparsestVertexBridge.distanceSum G w P := by
  apply NNReal.coe_le_coe.mp
  have h := S.ratio_minimal (fun v => (w v : ℝ))
    (fun d => (SparsestVertexBridge.demandDistance G w d : ℝ))
    (fun v => (w v).coe_nonneg) (actual_distances G P w hreach) (by exact_mod_cast hS)
  rw [cost_eq] at h
  simpa [ConcurrentDuality.cost, IntegerPackingCovering.coveringValue,
    weightedCost, SparsestVertexBridge.distanceSum, NNReal.coe_sum, NNReal.coe_mul] using h

/-- The mass of this chosen optimum after average-distance normalization. -/
def averageMass (S : Solution G P c) : ℝ≥0 := (P.card : ℝ≥0) * totalWeight (weight S)

theorem averageMass_eq (S : Solution G P c) (hreach : ∀ d : P, Nonempty (Path G P d)) :
    SparsestVertexBridge.averageNormalizedMass G (weight S) P = averageMass S := by
  simp [SparsestVertexBridge.averageNormalizedMass, distanceSum_eq_one S hreach, averageMass]

/-- Average-distance-one lengths of the same chosen optimum. -/
def averageWeight (S : Solution G P c) := fun v => (P.card : ℝ≥0) * weight S v

theorem demand_card_pos (S : Solution G P c) : 0 < P.card := by
  simpa using ConcurrentDuality.demand_card_pos S

theorem averageWeight_distanceSum (S : Solution G P c)
    (hreach : ∀ d : P, Nonempty (Path G P d)) :
    SparsestVertexBridge.distanceSum G (averageWeight S) P = (P.card : ℝ≥0) := by
  have hm : 0 < (P.card : ℝ≥0) := by exact_mod_cast demand_card_pos S
  change SparsestVertexBridge.distanceSum G (fun v => (P.card : ℝ≥0) * weight S v) P = _
  rw [SparsestVertexBridge.distanceSum_scale G (weight S) _ hm, distanceSum_eq_one S hreach,
    mul_one]

theorem averageWeight_mass (S : Solution G P c) :
    totalWeight (averageWeight S) = averageMass S := by
  simp [averageWeight, averageMass, totalWeight, Finset.mul_sum]

/-- Average normalization has value C/m, exactly equal to the common throughput. -/
theorem averageWeight_objective (S : Solution G P c) :
    S.throughput = (weightedCost c (averageWeight S) / (P.card : ℝ≥0) : ℝ≥0) := by
  rw [objectives_eq]
  have hm : (P.card : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (demand_card_pos S))
  have hc : weightedCost c (averageWeight S) = (P.card : ℝ≥0) * weightedCost c (weight S) := by
    simp [weightedCost, averageWeight, Finset.mul_sum, mul_left_comm]
  rw [hc, mul_div_cancel_left₀ _ hm]

/-- The normalized Corollary 7 bound applied to an attained concurrent-flow dual
optimum. The mass belongs to the same chosen optimizer used in the bound. -/
theorem sparsest_gap_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ≥0, 0 < K ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V)
        (P : Finset (V × V)) (c : V → ℝ≥0) (S : Solution G P c),
        (∀ d : P, Nonempty (Path G P d)) →
        ∃ X : Finset V, 0 < (SparsestVertexBridge.separated G P X).card ∧
          SparsestVertexBridge.sparsity G c P X ≤
            (K * (Fintype.card V : ℝ≥0) ^ ε *
              min ((Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3))
                (averageMass S ^ (1 / 2 : ℝ))) * weightedCost c (weight S) := by
  intro ε hε
  obtain ⟨K, hK, hbound⟩ := SparsestVertexCorollary.vertex_sparsest_min_uniform.{u} ε hε
  refine ⟨K, hK, ?_⟩
  intro V _ _ G P c S hreach
  have hsum := distanceSum_eq_one S hreach
  obtain ⟨X, hX, hb⟩ := hbound V G (weight S) c P (finite_distances G P (weight S) hreach)
    (by rw [hsum]; exact zero_lt_one)
  exact ⟨X, hX, by simpa only [hsum, div_one, averageMass_eq S hreach] using hb⟩

end
end DirectedFlowCutGap.ConcurrentVertexFlow
