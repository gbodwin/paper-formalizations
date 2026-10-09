import DirectedFlowCutGap.TinyEdgePreprocessing
import DirectedFlowCutGap.BoundedSampling
import Mathlib.Probability.Distributions.Uniform

/-!
# Finite weak low-diameter decompositions

The corrected common-scale multiplicative-weights recurrence gives a uniform
finite family. Every member cuts every threshold demand, and its exact
inclusion fraction has the stated bound. For edges the horizon is linear in
the number of vertices outside a logarithm, despite using ordered pairs as
items. Artificial positive weights are confined to the potential analysis;
the proved zero-weight penalty lemma forbids selecting those coordinates.

The generic edge theorem asks for a rounding factor at the *modified* weights.
It does not identify exact flow-cut parameters at `W` and `2W`. No polynomial
execution time, implementation of the oracle, or bit-complexity result is
asserted by this finite mathematical construction.
-/
namespace DirectedFlowCutGap
noncomputable section
open scoped BigOperators NNReal ENNReal
attribute [local instance] Classical.propDecidable

namespace WeakDecomposition

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- An explicit common-scale zero-avoiding family with freely chosen horizon. -/
theorem family_of_positive_floor
    (w : E → ℝ) (α δ η : ℝ) (P : Finset E → Prop)
    (hw : ∀ e, 0 ≤ w e) (hα : 0 < α) (hδ : 0 < δ) (hη : 0 < η)
    (hfloor : ∀ e, 0 < w e → δ ≤ w e) (hscale : η ≤ δ * α)
    (horacle : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      ∃ X : Finset E, P X ∧ (∑ e ∈ X, c e) ≤ α * mwPotential w c)
    (T : ℕ) (hT : 0 < T)
    (ht : Real.log ((∑ e, max δ (w e)) / δ) ≤ η * (T : ℝ)) :
    ∃ X : Fin T → Finset E, (∀ i, P (X i)) ∧
      (∀ i e, e ∈ X i → 0 < w e) ∧
      ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ) / (T : ℝ) ≤
        4 * α * w e := by
  let Q : Finset E → Prop := fun X => P X ∧ ∀ e ∈ X, 0 < w e
  have haux : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      ∃ X : Finset E, Q X ∧ (∑ e ∈ X, c e) ≤
        α * mwPotential (fun e => max δ (w e)) c := by
    intro c hc
    obtain ⟨X, hP, havoid, hcost⟩ := mw_oracle_avoids_zero w α P hw hα.le horacle c hc
    refine ⟨X, ⟨hP, havoid⟩, hcost.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ hα.le
    exact Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (le_max_right _ _) (hc e)
  obtain ⟨X, hQ, hX⟩ := exists_mw_family_of_min_weight
    (fun e => max δ (w e)) α η δ Q hδ (fun _ => le_max_left _ _) hα hη
    hscale haux T hT ht
  refine ⟨X, fun i => (hQ i).1, fun i e he => (hQ i).2 e he, ?_⟩
  intro e
  by_cases he : 0 < w e
  · simpa [max_eq_right (hfloor e he), mul_comm, mul_left_comm] using hX e
  · have habsent : ∀ i, e ∉ X i := fun i hi => he ((hQ i).2 e hi)
    have hz : w e = 0 := le_antisymm (le_of_not_gt he) (hw e)
    simp [habsent, hz]

/-- A genuine probability law obtained by uniformly sampling the indices.
Repeated equal cuts retain their multiplicity. -/
def familyLaw {T : ℕ} (hT : 0 < T) (X : Fin T → Finset E) : PMF (Finset E) :=
  (PMF.uniformOfFinset Finset.univ
    (show (Finset.univ : Finset (Fin T)).Nonempty from ⟨⟨0, hT⟩, Finset.mem_univ _⟩)).map X

omit [Fintype E] [DecidableEq E] in
/-- Every supported cut is an actual member of the finite family. -/
theorem familyLaw_support {T : ℕ} (hT : 0 < T) (X : Fin T → Finset E)
    (P : Finset E → Prop) (hP : ∀ i, P (X i))
    {Y : Finset E} (hY : Y ∈ (familyLaw hT X).support) : P Y := by
  obtain ⟨i, _hi, hiy⟩ := (PMF.mem_support_map_iff X _ Y).mp hY
  rw [← hiy]
  exact hP i

omit [Fintype E] in
/-- The law's marginal is exactly the finite inclusion fraction. -/
theorem familyLaw_marginal {T : ℕ} (hT : 0 < T) (X : Fin T → Finset E) (e : E) :
    ((familyLaw hT X).toOuterMeasure {Y | e ∈ Y}).toReal =
      ((Finset.univ.filter fun i => e ∈ X i).card : ℝ) / (T : ℝ) := by
  rw [familyLaw, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_uniformOfFinset_apply]
  simp [ENNReal.toReal_div]

/-- The vertex version includes zero factors and an empty vertex set at the
same explicit horizon; the displayed quotient is an exact uniform marginal. -/
theorem vertex_family
    {G : Digraph E} {w : E → ℝ≥0} {α : ℝ} (h : HasVertexRoundingFactor G w α) :
    ∃ X : Fin (BoundedSampling.horizon (fun e => (w e : ℝ)) α) → Finset E,
      (∀ i, IsIntegralCut G (X i) (thresholdDemands G w)) ∧
      ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ) /
        (BoundedSampling.horizon (fun e => (w e : ℝ)) α : ℝ) ≤ 8 * α * (w e : ℝ) := by
  by_cases hn : 0 < Fintype.card E
  · by_cases hα : 0 < α
    · exact BoundedSampling.exists_vertex_family hn hα h
    · have hz : α = 0 := le_antisymm (le_of_not_gt hα) h.nonneg
      subst α
      have hempty := (hasVertexRoundingFactor_zero_iff G w).mp h
      exact ⟨fun _ => ∅, fun _ => hempty, by simp⟩
  · have hz : Fintype.card E = 0 := by omega
    let : IsEmpty E := Fintype.card_eq_zero_iff.mp hz
    refine ⟨fun _ => ∅, ?_, ?_⟩
    · intro i s
      exact isEmptyElim s
    · intro e
      exact isEmptyElim e

omit [Fintype E] in
/-- Vertex threshold normalization preserves the endpoint-excluding model. -/
theorem vertex_normalized_thresholdDemands (G : Digraph E) (w : E → ℝ≥0)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) :
    thresholdDemands G (fun e => w e / Δ) =
      {st | (Δ : ℝ≥0∞) ≤ vertexDistance G w st.1 st.2} := by
  ext st
  change (1 : ℝ≥0∞) ≤ vertexDistance G (fun e => w e / Δ) st.1 st.2 ↔
    (Δ : ℝ≥0∞) ≤ vertexDistance G w st.1 st.2
  rw [← ENNReal.coe_one, coe_le_vertexDistance_iff, coe_le_vertexDistance_iff]
  simp only [SimplePath.weight, ← Finset.sum_div, le_div_iff₀ hΔ, one_mul]

/-- Repaired vertex oracle-to-family reduction at every positive diameter,
with empty graphs, zero coordinates, and zero factors included. -/
theorem vertex_scaled_family (G : Digraph E) (w : E → ℝ≥0) (Δ : ℝ≥0)
    (hΔ : 0 < Δ) (α : ℝ) (h : HasVertexRoundingFactor G (fun e => w e / Δ) α) :
    ∃ X : Fin (BoundedSampling.horizon (fun e => ((w e / Δ : ℝ≥0) : ℝ)) α) → Finset E,
      (∀ i, IsIntegralCut G (X i) {st | (Δ : ℝ≥0∞) ≤ vertexDistance G w st.1 st.2}) ∧
      ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ) /
        (BoundedSampling.horizon (fun e => ((w e / Δ : ℝ≥0) : ℝ)) α : ℝ) ≤
          8 * α * ((w e / Δ : ℝ≥0) : ℝ) := by
  simpa only [vertex_normalized_thresholdDemands G w Δ hΔ] using vertex_family h

/-- Linear-in-vertices horizon, with no dependence on a minimum positive input weight. -/
def edgeHorizon (n : ℕ) (W : ℝ≥0) : ℕ :=
  ⌈2 * (n : ℝ) * Real.log ((n : ℝ) * (2 * (W : ℝ) + n))⌉₊ + 1

theorem edgeHorizon_pos (n : ℕ) (W : ℝ≥0) : 0 < edgeHorizon n W :=
  Nat.zero_lt_succ _

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- The masked ambient weight has exactly the actual edge total. -/
theorem sum_actualEdgeWeight (G : Digraph V) (w : V × V → ℝ≥0) :
    (∑ e, (actualEdgeWeight G w e : ℝ)) = (totalEdgeWeight G w : ℝ) := by
  simp [actualEdgeWeight, totalEdgeWeight, graphEdges, Finset.sum_filter]

/-- Corrected generic edge reduction. The oracle concerns the actual modified
weight vector; its factor is supplied explicitly and is at least one. -/
theorem edge_family_of_preprocessed_factor
    (G : Digraph V) (w : V × V → ℝ≥0) (α : ℝ)
    (hn : 0 < Fintype.card V) (hα : 1 ≤ α)
    (horacle : HasEdgeRoundingFactor G (TinyEdgePreprocessing.weight w) α) :
    ∃ X : Fin (edgeHorizon (Fintype.card V) (totalEdgeWeight G w)) → Finset (V × V),
      (∀ i, X i ⊆ graphEdges G ∧ IsIntegralEdgeCut G (X i) (edgeThresholdDemands G w)) ∧
      (∀ i e, w e ≤ (2 * (Fintype.card V : ℝ≥0))⁻¹ → e ∉ X i) ∧
      ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ) /
        (edgeHorizon (Fintype.card V) (totalEdgeWeight G w) : ℝ) ≤ 8 * α * (w e : ℝ) := by
  let n : ℝ := Fintype.card V
  have hnR : 0 < n := by dsimp [n]; exact_mod_cast hn
  let a : V × V → ℝ := fun e => (actualEdgeWeight G (TinyEdgePreprocessing.weight w) e : ℝ)
  let δ : ℝ := n⁻¹
  have hδ : 0 < δ := inv_pos.mpr hnR
  have ha (e : V × V) : 0 ≤ a e := (actualEdgeWeight G _ e).coe_nonneg
  have hfloor (e : V × V) (he : 0 < a e) : δ ≤ a e := by
    by_cases hadj : G.Adj e.1 e.2
    · have hp : 0 < TinyEdgePreprocessing.weight w e := by
        simpa [a, actualEdgeWeight, hadj] using he
      have hh := TinyEdgePreprocessing.positive_weight_lower w e hp
      simpa [a, actualEdgeWeight, hadj, δ, n] using NNReal.coe_le_coe.mpr hh
    · simp [a, actualEdgeWeight, hadj] at he
  have hsum : (∑ e, max δ (a e)) ≤ 2 * (totalEdgeWeight G w : ℝ) + n := by
    have hbound := NNReal.coe_le_coe.mpr (TinyEdgePreprocessing.totalWeight_le_twice G w)
    have hid : (Fintype.card (V × V) : ℝ) * δ = n := by
      simp only [Fintype.card_prod, Nat.cast_mul]
      dsimp [δ, n]
      field_simp
    calc
      _ ≤ ∑ e, (a e + δ) := Finset.sum_le_sum fun e _ =>
        max_le (by linarith [ha e]) (by linarith [hδ])
      _ = (∑ e, a e) + n := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hid]
      _ ≤ _ := by rw [show (∑ e, a e) = _ from sum_actualEdgeWeight G _]; simpa [add_comm] using add_le_add_right hbound n
  have hsumpos : 0 < ∑ e, max δ (a e) := by
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp hn
    exact hδ.trans_le ((le_max_left _ _).trans
      (Finset.single_le_sum (fun e _ => hδ.le.trans (le_max_left _ _)) (Finset.mem_univ (v, v))))
  have hratio : (∑ e, max δ (a e)) / δ ≤ n * (2 * (totalEdgeWeight G w : ℝ) + n) := by
    rw [div_eq_mul_inv, show δ⁻¹ = n by simp [δ]]
    exact (mul_le_mul_of_nonneg_right hsum hnR.le).trans_eq (mul_comm _ _)
  have hlog := Real.log_le_log (div_pos hsumpos hδ) hratio
  have hscale : (2 * n)⁻¹ ≤ δ * α := by
    have hi : (2 * n)⁻¹ ≤ δ := by
      dsimp [δ]
      exact inv_anti₀ hnR (by linarith)
    exact hi.trans (le_mul_of_one_le_right hδ.le hα)
  have ht : Real.log ((∑ e, max δ (a e)) / δ) ≤
      (2 * n)⁻¹ * (edgeHorizon (Fintype.card V) (totalEdgeWeight G w) : ℝ) := by
    have hc := Nat.le_ceil (2 * n * Real.log (n * (2 * (totalEdgeWeight G w : ℝ) + n)))
    have hh : 2 * n * Real.log (n * (2 * (totalEdgeWeight G w : ℝ) + n)) ≤
        (edgeHorizon (Fintype.card V) (totalEdgeWeight G w) : ℝ) := by
      dsimp [edgeHorizon, n] at *
      push_cast
      linarith
    have hdiv : Real.log (n * (2 * (totalEdgeWeight G w : ℝ) + n)) ≤
        (edgeHorizon (Fintype.card V) (totalEdgeWeight G w) : ℝ) / (2 * n) :=
      (le_div_iff₀ (by positivity : 0 < 2 * n)).mpr (by nlinarith [hh])
    simpa [div_eq_mul_inv, mul_comm] using hlog.trans hdiv
  obtain ⟨X, hX, hpos, hmarginal⟩ := family_of_positive_floor a α δ ((2 * n)⁻¹)
    (fun X => X ⊆ graphEdges G ∧
      IsIntegralEdgeCut G X (edgeThresholdDemands G (TinyEdgePreprocessing.weight w)))
    ha (by linarith) hδ (by positivity) hfloor hscale horacle.real_cost_round
    (edgeHorizon (Fintype.card V) (totalEdgeWeight G w)) (edgeHorizon_pos _ _) ht
  refine ⟨X, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hX i).1, fun s t hst => (hX i).2 s t
      (TinyEdgePreprocessing.thresholdDemands_subset G w hst)⟩
  · intro i e he hi
    have hz := TinyEdgePreprocessing.weight_zero_of_tiny w e he
    have h := hpos i e hi
    simp [a, actualEdgeWeight, hz] at h
  · intro e
    have hpoint : a e ≤ 2 * (w e : ℝ) := by
      by_cases he : G.Adj e.1 e.2
      · simpa [a, actualEdgeWeight, he] using
          NNReal.coe_le_coe.mpr (TinyEdgePreprocessing.weight_le_twice w e)
      · simp [a, actualEdgeWeight, he]
    calc
      _ ≤ 4 * α * a e := hmarginal e
      _ ≤ 4 * α * (2 * (w e : ℝ)) := mul_le_mul_of_nonneg_left hpoint (by positivity)
      _ = _ := by ring

/-- Turn any proved finite family into a genuine cut-valued probability law.
The support and marginal conclusions concern that same law. -/
theorem law_of_edge_family (G : Digraph V) (w : V × V → ℝ≥0)
    (Δ : ℝ≥0) (L : ℝ) (T : ℕ) (hT : 0 < T) (X : Fin T → Finset (V × V))
    (hvalid : ∀ i, X i ⊆ graphEdges G ∧ IsIntegralEdgeCut G (X i)
      {st | (Δ : ℝ≥0∞) ≤ edgeDistance G w st.1 st.2})
    (hmarginal : ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ) / (T : ℝ) ≤
      L * ((w e / Δ : ℝ≥0) : ℝ)) :
    ∃ μ : PMF (Finset (V × V)),
      (∀ Y ∈ μ.support, Y ⊆ graphEdges G ∧ IsIntegralEdgeCut G Y
        {st | (Δ : ℝ≥0∞) ≤ edgeDistance G w st.1 st.2}) ∧
      ∀ e, (μ.toOuterMeasure {Y | e ∈ Y}).toReal ≤ L * ((w e / Δ : ℝ≥0) : ℝ) := by
  refine ⟨familyLaw hT X, ?_, ?_⟩
  · intro Y hY
    exact familyLaw_support hT X (fun Y => Y ⊆ graphEdges G ∧ IsIntegralEdgeCut G Y
      {st | (Δ : ℝ≥0∞) ≤ edgeDistance G w st.1 st.2}) hvalid hY
  · intro e
    rw [familyLaw_marginal]
    exact hmarginal e

omit [Fintype V] in
/-- A valid threshold cut makes every surviving pair have original distance
strictly below the target diameter, including the unreachable-pair convention. -/
theorem distance_lt_of_surviving_path (G : Digraph V) (w : V × V → ℝ≥0)
    (Δ : ℝ≥0) (X : Finset (V × V))
    (hX : IsIntegralEdgeCut G X {st | (Δ : ℝ≥0∞) ≤ edgeDistance G w st.1 st.2})
    {s t : V} (p : SimplePath (edgeDeletedGraph G X) s t) :
    edgeDistance G w s t < Δ := by
  by_contra h
  have hh := hX s t (le_of_not_gt h) p.forgetEdgeDeletion
  obtain ⟨e, he, hx⟩ := hh
  exact p.forgetEdgeDeletion_avoids e he hx

end WeakDecomposition
end
end DirectedFlowCutGap
