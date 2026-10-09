import DirectedFlowCutGap.WeakDecomposition
import DirectedFlowCutGap.AdaptiveEdgeBound

/-!
# The main weak-decomposition corollary

Both asymptotic constants are chosen before every graph and weight vector.
The finite family has the explicit linear-in-vertices horizon, and the final
result covers every positive diameter by normalizing the total weight by that
diameter. Small total weights and empty graphs use the proved empty cut.
The conclusions are mathematical finite probability laws; algorithmic running
time and finite-precision execution are separate, unasserted obligations.
-/
namespace DirectedFlowCutGap
noncomputable section
open scoped BigOperators NNReal ENNReal
attribute [local instance] Classical.propDecidable

namespace WeakDecomposition
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Enlarging an actual all-cost factor does not change the demand pairs. -/
theorem edge_factor_mono {G : Digraph V} {w : V × V → ℝ≥0} {α β : ℝ}
    (h : HasEdgeRoundingFactor G w α) (hαβ : α ≤ β) :
    HasEdgeRoundingFactor G w β := by
  refine ⟨h.nonneg.trans hαβ, ?_⟩
  intro c
  obtain ⟨X, hX, hvalid, hcost⟩ := h.round c
  exact ⟨X, hX, hvalid, hcost.trans
    (mul_le_mul_of_nonneg_right hαβ (weightedEdgeCost G c w).coe_nonneg)⟩

/-- The size loss, uniformly over all finite graph instances. -/
theorem edge_size_family_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V) (w : V × V → ℝ≥0),
        ∃ X : Fin (edgeHorizon (Fintype.card V) (totalEdgeWeight G w)) → Finset (V × V),
          (∀ i, X i ⊆ graphEdges G ∧ IsIntegralEdgeCut G (X i) (edgeThresholdDemands G w)) ∧
          ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ) /
            (edgeHorizon (Fintype.card V) (totalEdgeWeight G w) : ℝ) ≤
              (C * (Fintype.card V : ℝ) ^ ((1 : ℝ) / 3 + ε)) * (w e : ℝ) := by
  intro ε hε
  obtain ⟨K, hK, hround⟩ := AdaptiveEdgeBound.hasEdgeRoundingFactor_uniform.{u} ε hε
  refine ⟨8 * max 1 K, by positivity, ?_⟩
  intro V _ _ G w
  by_cases hn : 0 < Fintype.card V
  · have hn1 : 1 ≤ (Fintype.card V : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
    have hpow : 1 ≤ (Fintype.card V : ℝ) ^ ((1 : ℝ) / 3 + ε) :=
      Real.one_le_rpow hn1 (by positivity)
    have hα : 1 ≤ max 1 K * (Fintype.card V : ℝ) ^ ((1 : ℝ) / 3 + ε) :=
      one_le_mul_of_one_le_of_one_le (le_max_left _ _) hpow
    have horacle := edge_factor_mono (hround V G (TinyEdgePreprocessing.weight w))
      (mul_le_mul_of_nonneg_right (le_max_right 1 K) (by positivity))
    obtain ⟨X, hX, _havoid, hmarginal⟩ := edge_family_of_preprocessed_factor G w _ hn hα horacle
    refine ⟨X, hX, ?_⟩
    intro e
    calc
      _ ≤ 8 * (max 1 K * (Fintype.card V : ℝ) ^ ((1 : ℝ) / 3 + ε)) * (w e : ℝ) := hmarginal e
      _ = _ := by ring
  · have hz : Fintype.card V = 0 := by omega
    let : IsEmpty V := Fintype.card_eq_zero_iff.mp hz
    refine ⟨fun _ => ∅, ?_, ?_⟩
    · intro i
      refine ⟨Finset.empty_subset _, ?_⟩
      intro s
      exact isEmptyElim s
    · intro e
      exact isEmptyElim e.1

/-- The mass-sensitive loss with a constant chosen before all instances.
The actual modified total is bounded by `2W`, and its square root is paid
explicitly in the constant. For `W < 1`, threshold demands are unreachable. -/
theorem edge_weight_family_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V) (w : V × V → ℝ≥0),
        ∃ X : Fin (edgeHorizon (Fintype.card V) (totalEdgeWeight G w)) → Finset (V × V),
          (∀ i, X i ⊆ graphEdges G ∧ IsIntegralEdgeCut G (X i) (edgeThresholdDemands G w)) ∧
          ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ) /
            (edgeHorizon (Fintype.card V) (totalEdgeWeight G w) : ℝ) ≤
              (C * (Fintype.card V : ℝ) ^ ε * (totalEdgeWeight G w : ℝ) ^ (1 / 2 : ℝ)) * (w e : ℝ) := by
  intro ε hε
  obtain ⟨K, hK, hround⟩ := AdaptiveEdgeBound.hasEdgeWeightRoundingFactor_uniform.{u} ε hε
  refine ⟨16 * max 1 K, by positivity, ?_⟩
  intro V _ _ G w
  by_cases hW : totalEdgeWeight G w < 1
  · refine ⟨fun _ => ∅, fun _ => ⟨Finset.empty_subset _,
      TinyEdgePreprocessing.empty_cut_of_total_lt_one G w hW⟩, ?_⟩
    intro e
    simp only [Finset.notMem_empty, Finset.filter_false, Finset.card_empty, Nat.cast_zero, zero_div]
    positivity
  · by_cases hn : 0 < Fintype.card V
    · have hn1 : 1 ≤ (Fintype.card V : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
      have hW1 : 1 ≤ (totalEdgeWeight G w : ℝ) := by exact_mod_cast le_of_not_gt hW
      have hpow : 1 ≤ (Fintype.card V : ℝ) ^ ε := Real.one_le_rpow hn1 hε.le
      have hroot : 1 ≤ (2 * (totalEdgeWeight G w : ℝ)) ^ (1 / 2 : ℝ) :=
        Real.one_le_rpow (by linarith) (by norm_num)
      let α : ℝ := max 1 K * (Fintype.card V : ℝ) ^ ε *
        (2 * (totalEdgeWeight G w : ℝ)) ^ (1 / 2 : ℝ)
      have hα : 1 ≤ α := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) hpow) hroot
      have hmodified := NNReal.coe_le_coe.mpr (TinyEdgePreprocessing.totalWeight_le_twice G w)
      have hfactor : K * (Fintype.card V : ℝ) ^ ε *
          (totalEdgeWeight G (TinyEdgePreprocessing.weight w) : ℝ) ^ (1 / 2 : ℝ) ≤ α := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
        · exact Real.rpow_le_rpow (by positivity) hmodified (by norm_num)
        · positivity
        · positivity
      have horacle := edge_factor_mono (hround V G (TinyEdgePreprocessing.weight w)) hfactor
      obtain ⟨X, hX, _havoid, hmarginal⟩ := edge_family_of_preprocessed_factor G w α hn hα horacle
      refine ⟨X, hX, ?_⟩
      have htwo : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (1 / 2 : ℝ) ≤ 1)
      have hrootbound : (2 * (totalEdgeWeight G w : ℝ)) ^ (1 / 2 : ℝ) ≤
          2 * (totalEdgeWeight G w : ℝ) ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
        exact mul_le_mul_of_nonneg_right htwo (by positivity)
      intro e
      calc
        _ ≤ 8 * α * (w e : ℝ) := hmarginal e
        _ ≤ 8 * (max 1 K * (Fintype.card V : ℝ) ^ ε *
            (2 * (totalEdgeWeight G w : ℝ) ^ (1 / 2 : ℝ))) * (w e : ℝ) := by
          dsimp [α]
          gcongr
        _ = _ := by ring
    · have hz : Fintype.card V = 0 := by omega
      let : IsEmpty V := Fintype.card_eq_zero_iff.mp hz
      refine ⟨fun _ => ∅, ?_, ?_⟩
      · intro i
        refine ⟨Finset.empty_subset _, ?_⟩
        intro s
        exact isEmptyElim s
      · intro e
        exact isEmptyElim e.1

/-- Both main losses hold simultaneously for a single family. The constant
is selected before the type, graph, weights, and positive target diameter.
Here `W/Δ` is the total of the normalized weight vector. -/
theorem edge_weak_decomposition_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V)
        (w : V × V → ℝ≥0) (Δ : ℝ≥0), 0 < Δ →
        ∃ X : Fin (edgeHorizon (Fintype.card V) (totalEdgeWeight G w / Δ)) → Finset (V × V),
          (∀ i, X i ⊆ graphEdges G ∧ IsIntegralEdgeCut G (X i)
            {st | (Δ : ℝ≥0∞) ≤ edgeDistance G w st.1 st.2}) ∧
          ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ) /
            (edgeHorizon (Fintype.card V) (totalEdgeWeight G w / Δ) : ℝ) ≤
              min (C * (Fintype.card V : ℝ) ^ ((1 : ℝ) / 3 + ε))
                (C * (Fintype.card V : ℝ) ^ ε * ((totalEdgeWeight G w / Δ : ℝ≥0) : ℝ) ^ (1 / 2 : ℝ)) *
                ((w e / Δ : ℝ≥0) : ℝ) := by
  intro ε hε
  obtain ⟨Cs, hCs, hs⟩ := edge_size_family_uniform.{u} ε hε
  obtain ⟨Cw, hCw, hw⟩ := edge_weight_family_uniform.{u} ε hε
  let C := max Cs Cw
  refine ⟨C, lt_of_lt_of_le hCs (le_max_left _ _), ?_⟩
  intro V _ _ G w Δ hΔ
  let w' := TinyEdgePreprocessing.normalizedWeight w Δ
  have htotal : totalEdgeWeight G w' = totalEdgeWeight G w / Δ :=
    TinyEdgePreprocessing.total_normalized_weight G w Δ
  have hdemands : edgeThresholdDemands G w' =
      {st | (Δ : ℝ≥0∞) ≤ edgeDistance G w st.1 st.2} :=
    TinyEdgePreprocessing.normalized_thresholdDemands G w Δ hΔ
  have hfamily : ∃ X : Fin (edgeHorizon (Fintype.card V) (totalEdgeWeight G w')) → Finset (V × V),
      (∀ i, X i ⊆ graphEdges G ∧ IsIntegralEdgeCut G (X i) (edgeThresholdDemands G w')) ∧
      ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ) /
        (edgeHorizon (Fintype.card V) (totalEdgeWeight G w') : ℝ) ≤
          min (C * (Fintype.card V : ℝ) ^ ((1 : ℝ) / 3 + ε))
            (C * (Fintype.card V : ℝ) ^ ε * (totalEdgeWeight G w' : ℝ) ^ (1 / 2 : ℝ)) *
            (w' e : ℝ) := by
    by_cases hmin : C * (Fintype.card V : ℝ) ^ ((1 : ℝ) / 3 + ε) ≤
        C * (Fintype.card V : ℝ) ^ ε * (totalEdgeWeight G w' : ℝ) ^ (1 / 2 : ℝ)
    · obtain ⟨X, hX, hm⟩ := hs V G w'
      refine ⟨X, hX, ?_⟩
      intro e
      rw [min_eq_left hmin]
      exact (hm e).trans (by gcongr; exact le_max_left _ _)
    · obtain ⟨X, hX, hm⟩ := hw V G w'
      refine ⟨X, hX, ?_⟩
      intro e
      rw [min_eq_right (lt_of_not_ge hmin).le]
      exact (hm e).trans (by gcongr; exact le_max_right _ _)
  rw [htotal, hdemands] at hfamily
  simpa only [w', TinyEdgePreprocessing.normalizedWeight] using hfamily

/-- Corollary 8 as an actual cut-valued probability law, with exact
zero-additive-error marginal bounds and validity of every supported cut. -/
theorem edge_weak_law_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : Digraph V)
        (w : V × V → ℝ≥0) (Δ : ℝ≥0), 0 < Δ →
        ∃ μ : PMF (Finset (V × V)),
          (∀ Y ∈ μ.support, Y ⊆ graphEdges G ∧ IsIntegralEdgeCut G Y
            {st | (Δ : ℝ≥0∞) ≤ edgeDistance G w st.1 st.2}) ∧
          ∀ e, (μ.toOuterMeasure {Y | e ∈ Y}).toReal ≤
            min (C * (Fintype.card V : ℝ) ^ ((1 : ℝ) / 3 + ε))
              (C * (Fintype.card V : ℝ) ^ ε * ((totalEdgeWeight G w / Δ : ℝ≥0) : ℝ) ^ (1 / 2 : ℝ)) *
              ((w e / Δ : ℝ≥0) : ℝ) := by
  intro ε hε
  obtain ⟨C, hC, hfamily⟩ := edge_weak_decomposition_uniform.{u} ε hε
  refine ⟨C, hC, ?_⟩
  intro V _ _ G w Δ hΔ
  obtain ⟨X, hvalid, hmarginal⟩ := hfamily V G w Δ hΔ
  exact law_of_edge_family G w Δ _ _ (edgeHorizon_pos _ _) X hvalid hmarginal

end WeakDecomposition
end
end DirectedFlowCutGap
