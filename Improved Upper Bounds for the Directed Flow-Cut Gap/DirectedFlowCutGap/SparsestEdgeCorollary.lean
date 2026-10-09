import DirectedFlowCutGap.SparsestEdgeBridge

/-!
# Uniform normalized edge sparsest-cut bounds

The constants below precede every finite vertex type, graph, demand family,
length assignment, and cost assignment. The mass is W_avg = |P| W / Σd.
These are concrete cut-existence/rounding theorems for each assignment.
They make no claim that a particular optimizer is supplied, that a chosen
LP normalization has raw mass W_avg, or that an implementation is efficient.
-/

namespace DirectedFlowCutGap.SparsestEdgeCorollary
noncomputable section
open scoped BigOperators NNReal ENNReal
open FiniteHarmonicThreshold SparsestEdgeBridge
attribute [local instance] Classical.propDecidable
universe u

theorem edge_card_pos_of_distanceSum_pos {V : Type u} [Fintype V] [DecidableEq V]
    (G : Digraph V) (w : V × V → ℝ≥0) (P : Finset (V × V))
    (hS : 0 < distanceSum G w P) : 1 ≤ Fintype.card V := by
  by_contra hn
  have hz : Fintype.card V = 0 := by omega
  let : IsEmpty V := Fintype.card_eq_zero_iff.mp hz
  have hP : P = ∅ := Finset.eq_empty_of_forall_notMem (by intro p; exact isEmptyElim p.1)
  subst P
  simp [distanceSum] at hS

/-- The size-only edge sparsest-cut rounding corollary. -/
theorem edge_sparsest_size_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ≥0, 0 < K ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V)
        (w c : V × V → ℝ≥0) (P : Finset (V × V)),
        (∀ p ∈ P, edgeDistance G w p.1 p.2 ≠ ⊤) → 0 < distanceSum G w P →
        ∃ X : Finset (V × V), X ⊆ graphEdges G ∧ 0 < (separated G P X).card ∧
          sparsity G c P X ≤ (K * (Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3 + ε)) *
            (weightedEdgeCost G c w / distanceSum G w P) := by
  intro ε hε
  obtain ⟨A, hA, hround⟩ := AdaptiveEdgeBound.edge_rounding_uniform.{u} (ε / 2) (by positivity)
  obtain ⟨D, hD, hH⟩ := harmonic_factors_uniform (ε / 2) (by positivity)
  refine ⟨A * D, by positivity, ?_⟩
  intro V _ _ G w c P hfinite hS
  have hn := edge_card_pos_of_distanceSum_pos G w P hS
  have hn0 : (Fintype.card V : ℝ≥0) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)
  obtain ⟨X, hactual, hX, hb⟩ := sparsity_of_size_rounding G c w P hfinite hS
    (A * (Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3 + ε / 2)) (fun z => hround V G z c)
  refine ⟨X, hactual, hX, hb.trans ?_⟩
  have hH' := (hH (Fintype.card V) hn P.card (demand_card_le_square P)).1
  calc
    _ ≤ (A * (Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3 + ε / 2)) *
        (D * (Fintype.card V : ℝ≥0) ^ (ε / 2)) * (weightedEdgeCost G c w / distanceSum G w P) := by
      gcongr
    _ = _ := by
      have hp : (Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3 + ε / 2) *
          (Fintype.card V : ℝ≥0) ^ (ε / 2) =
          (Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3 + ε) := by
        rw [← NNReal.rpow_add hn0]
        congr 1
        ring
      calc
        _ = (A * D) * ((Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3 + ε / 2) *
            (Fintype.card V : ℝ≥0) ^ (ε / 2)) *
            (weightedEdgeCost G c w / distanceSum G w P) := by ring
        _ = _ := by rw [hp]

/-- The mass-sensitive edge corollary with explicit scale-invariant mass. -/
theorem edge_sparsest_weight_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ≥0, 0 < K ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V)
        (w c : V × V → ℝ≥0) (P : Finset (V × V)),
        (∀ p ∈ P, edgeDistance G w p.1 p.2 ≠ ⊤) → 0 < distanceSum G w P →
        ∃ X : Finset (V × V), X ⊆ graphEdges G ∧ 0 < (separated G P X).card ∧
          sparsity G c P X ≤ (K * (Fintype.card V : ℝ≥0) ^ ε *
            averageNormalizedMass G w P ^ (1 / 2 : ℝ)) *
            (weightedEdgeCost G c w / distanceSum G w P) := by
  intro ε hε
  obtain ⟨B, hB, hround⟩ := AdaptiveEdgeBound.edge_weight_rounding_uniform.{u} (ε / 2) (by positivity)
  obtain ⟨D, hD, hH⟩ := harmonic_factors_uniform (ε / 2) (by positivity)
  refine ⟨B * D, by positivity, ?_⟩
  intro V _ _ G w c P hfinite hS
  have hn := edge_card_pos_of_distanceSum_pos G w P hS
  have hn0 : (Fintype.card V : ℝ≥0) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)
  obtain ⟨X, hactual, hX, hb⟩ := sparsity_of_weight_rounding G c w P hfinite hS
    (B * (Fintype.card V : ℝ≥0) ^ (ε / 2)) (fun z => hround V G z c)
  refine ⟨X, hactual, hX, hb.trans ?_⟩
  have hH' := (hH (Fintype.card V) hn P.card (demand_card_le_square P)).2
  calc
    _ ≤ (B * (Fintype.card V : ℝ≥0) ^ (ε / 2)) *
        (D * (Fintype.card V : ℝ≥0) ^ (ε / 2)) *
        averageNormalizedMass G w P ^ (1 / 2 : ℝ) * (weightedEdgeCost G c w / distanceSum G w P) := by
      gcongr
    _ = _ := by
      have hp : (Fintype.card V : ℝ≥0) ^ (ε / 2) *
          (Fintype.card V : ℝ≥0) ^ (ε / 2) = (Fintype.card V : ℝ≥0) ^ ε := by
        rw [← NNReal.rpow_add hn0]
        congr 1
        ring
      calc
        _ = (B * D) * ((Fintype.card V : ℝ≥0) ^ (ε / 2) *
            (Fintype.card V : ℝ≥0) ^ (ε / 2)) *
            averageNormalizedMass G w P ^ (1 / 2 : ℝ) *
            (weightedEdgeCost G c w / distanceSum G w P) := by ring
        _ = _ := by rw [hp]

/-- One actual cut achieves the minimum of the size and normalized-mass
bounds. The common constant is fixed before every input instance. -/
theorem edge_sparsest_min_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ≥0, 0 < K ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V)
        (w c : V × V → ℝ≥0) (P : Finset (V × V)),
        (∀ p ∈ P, edgeDistance G w p.1 p.2 ≠ ⊤) → 0 < distanceSum G w P →
        ∃ X : Finset (V × V), X ⊆ graphEdges G ∧ 0 < (separated G P X).card ∧
          sparsity G c P X ≤ (K * (Fintype.card V : ℝ≥0) ^ ε *
            min ((Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3))
              (averageNormalizedMass G w P ^ (1 / 2 : ℝ))) *
            (weightedEdgeCost G c w / distanceSum G w P) := by
  intro ε hε
  obtain ⟨A, hA, hsize⟩ := edge_sparsest_size_uniform.{u} ε hε
  obtain ⟨B, hB, hweight⟩ := edge_sparsest_weight_uniform.{u} ε hε
  refine ⟨max A B, lt_of_lt_of_le hA (le_max_left _ _), ?_⟩
  intro V _ _ G w c P hfinite hS
  have hn := edge_card_pos_of_distanceSum_pos G w P hS
  have hn0 : (Fintype.card V : ℝ≥0) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)
  by_cases h : (Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3) ≤
      averageNormalizedMass G w P ^ (1 / 2 : ℝ)
  · obtain ⟨X, hactual, hX, hb⟩ := hsize V G w c P hfinite hS
    refine ⟨X, hactual, hX, hb.trans ?_⟩
    rw [min_eq_left h, NNReal.rpow_add hn0]
    calc
      _ ≤ (max A B * ((Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3) *
          (Fintype.card V : ℝ≥0) ^ ε)) * (weightedEdgeCost G c w / distanceSum G w P) := by
        gcongr
        exact le_max_left A B
      _ = _ := by ring
  · obtain ⟨X, hactual, hX, hb⟩ := hweight V G w c P hfinite hS
    refine ⟨X, hactual, hX, hb.trans ?_⟩
    rw [min_eq_right (le_of_not_ge h)]
    gcongr
    exact le_max_right A B

/-- An explicit average-distance-one formulation: here the displayed W is
exactly the raw total fractional weight of the normalized assignment. -/
theorem edge_sparsest_average_one_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ≥0, 0 < K ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V)
        (w c : V × V → ℝ≥0) (P : Finset (V × V)),
        (∀ p ∈ P, edgeDistance G w p.1 p.2 ≠ ⊤) → 0 < P.card →
        distanceSum G w P = (P.card : ℝ≥0) →
        ∃ X : Finset (V × V), X ⊆ graphEdges G ∧ 0 < (separated G P X).card ∧
          sparsity G c P X ≤ (K * (Fintype.card V : ℝ≥0) ^ ε *
            min ((Fintype.card V : ℝ≥0) ^ ((1 : ℝ) / 3))
              (totalEdgeWeight G w ^ (1 / 2 : ℝ))) *
            (weightedEdgeCost G c w / (P.card : ℝ≥0)) := by
  intro ε hε
  obtain ⟨K, hK, hb⟩ := edge_sparsest_min_uniform.{u} ε hε
  refine ⟨K, hK, ?_⟩
  intro V _ _ G w c P hfinite hP havg
  have hS : 0 < distanceSum G w P := by rw [havg]; exact_mod_cast hP
  obtain ⟨X, hactual, hX, hb⟩ := hb V G w c P hfinite hS
  refine ⟨X, hactual, hX, ?_⟩
  simpa only [averageNormalizedMass_eq_totalEdgeWeight G w P hP havg, havg] using hb

end
end DirectedFlowCutGap.SparsestEdgeCorollary
