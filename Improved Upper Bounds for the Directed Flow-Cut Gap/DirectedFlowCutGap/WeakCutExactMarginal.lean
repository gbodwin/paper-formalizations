import DirectedFlowCutGap.WeakDecompositionBounds
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation

/-! A finite cut law bounded by the all-cost rounding factor in each marginal,
and its specialization to the paper's least integer factors at fixed mass. -/

namespace DirectedFlowCutGap.WeakDecomposition

noncomputable section
open scoped BigOperators NNReal ENNReal
open Set

variable {E : Type*} [Fintype E] [DecidableEq E]

private def cutIndicator (X : Finset E) (e : E) : ℝ := if e ∈ X then 1 else 0

omit [Fintype E] in
private theorem cutIndicator_nonneg (X : Finset E) (e : E) : 0 ≤ cutIndicator X e := by
  simp only [cutIndicator]
  split <;> norm_num

private theorem convex_oracle_feasible (P : Finset E → Prop) (limit : E → ℝ)
    (nonneg : ∀ e, 0 ≤ limit e)
    (oracle : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) → ∃ X : Finset E, P X ∧
      (∑ e ∈ X, c e) ≤ ∑ e, c e * limit e) :
    ∃ x ∈ convexHull ℝ (cutIndicator '' {X | P X}), x ≤ limit := by
  classical
  let cuts : Set (E → ℝ) := cutIndicator '' {X | P X}
  let feasible := convexHull ℝ cuts
  have compact : IsCompact feasible := ((Set.toFinite {X : Finset E | P X}).image cutIndicator).isCompact_convexHull ℝ
  have closed : IsClosed (Iic limit) := by
    have h : Iic limit = ⋂ e : E, {x : E → ℝ | x e ≤ limit e} := by ext x; simp [Pi.le_def]
    rw [h]
    exact isClosed_iInter (fun e => isClosed_le (continuous_apply e) continuous_const)
  by_contra bad
  have disj : Disjoint (Iic limit) feasible := Set.disjoint_left.mpr (fun x h₁ h₂ => bad ⟨x,h₂,h₁⟩)
  obtain ⟨f,u,v,below,gap,above⟩ := geometric_hahn_banach_closed_compact
    (convex_Iic (𝕜:=ℝ) limit) closed (convex_convexHull ℝ cuts) compact disj
  let coord (e : E) := f (Pi.single e (1 : ℝ))
  let price (e : E) := max 0 (coord e)
  let comparator (e : E) := if 0 ≤ coord e then limit e else 0
  have comparator_le : comparator ∈ Iic limit := by
    intro e
    unfold comparator
    split <;> first | exact le_rfl | exact nonneg e
  have expands (x : E → ℝ) : f x = ∑ e, coord e * x e := by
    have full : (∑ e : E, x e • Pi.single e (1 : ℝ)) = x := by
      ext i
      simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,mul_ite]
    conv_lhs => rw [← full]
    simp [coord,map_sum,mul_comm]
  have comparator_value : f comparator = ∑ e, price e * limit e := by
    rw [expands]
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : 0 ≤ coord e
    · simp [comparator,price,h]
    · simp [comparator,price,h,max_eq_left (le_of_not_ge h)]
  obtain ⟨X,valid,within⟩ := oracle price (fun e => le_max_left _ _)
  have hX : cutIndicator X ∈ feasible := subset_convexHull ℝ cuts ⟨X,valid,rfl⟩
  have cut_cost : f (cutIndicator X) ≤ ∑ e ∈ X, price e := by
    rw [expands]
    calc
      _ ≤ ∑ e, price e * cutIndicator X e := Finset.sum_le_sum (fun e _ =>
        mul_le_mul_of_nonneg_right (le_max_right _ _) (cutIndicator_nonneg X e))
      _ = _ := by simp [cutIndicator,mul_ite]
  exact (lt_irrefl (f comparator)) ((below comparator comparator_le).trans
    (gap.trans ((above _ hX).trans_le (cut_cost.trans (within.trans_eq comparator_value.symm)))))

theorem law_of_all_cost_factor (P : Finset E → Prop) (w : E → ℝ) (α : ℝ)
    (hw : ∀ e, 0 ≤ w e) (hα : 0 ≤ α)
    (oracle : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) → ∃ X : Finset E, P X ∧
      (∑ e ∈ X, c e) ≤ α * mwPotential w c) :
    ∃ p : PMF (Finset E), (∀ X ∈ p.support, P X) ∧
      ∀ e, (p.toOuterMeasure {X | e ∈ X}).toReal ≤ α * w e := by
  classical
  let limit (e : E) := α * w e
  have hOracle (c : E → ℝ) (hc : ∀ e, 0 ≤ c e) :
      ∃ X : Finset E, P X ∧ (∑ e ∈ X, c e) ≤ ∑ e, c e * limit e := by
    obtain ⟨X,valid,h⟩ := oracle c hc
    refine ⟨X,valid,?_⟩
    simpa [mwPotential,limit,Finset.mul_sum,mul_left_comm] using h
  obtain ⟨x, hx, within⟩ := convex_oracle_feasible P limit (fun e => mul_nonneg hα (hw e)) hOracle
  obtain ⟨I, finite, mass, indicator, positive, normalized, supported, mean⟩ :=
    mem_convexHull_iff_exists_fintype.mp hx
  choose cut valid same using supported
  have sums : ∑ i : I, ENNReal.ofReal (mass i) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => positive i),normalized,ENNReal.ofReal_one]
  let native := PMF.ofFintype (fun i : I => ENNReal.ofReal (mass i)) sums
  refine ⟨native.map cut, ?_, ?_⟩
  · intro Y hy
    obtain ⟨i, _, rfl⟩ := (PMF.mem_support_map_iff cut native Y).mp hy
    exact valid i
  · intro e
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_fintype]
    have terms (i : I) :
        ((cut ⁻¹' {X | e ∈ X}).indicator native i).toReal = mass i * indicator i e := by
      rw [← same i]
      by_cases h : e ∈ cut i <;> simp [native,cutIndicator,Set.indicator,h,ENNReal.toReal_ofReal (positive i)]
    rw [ENNReal.toReal_sum (fun i _ => by
      by_cases h : e ∈ cut i <;> simp [native,Set.indicator,h])]
    simp only [terms]
    have h := congrFun mean e
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at h
    exact h.trans_le (within e)

theorem vertex_law_of_exact_factor {G : Digraph E} {w : E → ℝ≥0} {α : ℝ}
    (factor : HasVertexRoundingFactor G w α) :
    ∃ p : PMF (Finset E), (∀ X ∈ p.support, IsIntegralCut G X (thresholdDemands G w)) ∧
      ∀ e, (p.toOuterMeasure {X | e ∈ X}).toReal ≤ α * (w e : ℝ) :=
  law_of_all_cost_factor _ _ α (fun e => (w e).coe_nonneg) factor.nonneg factor.real_cost_round

theorem edge_law_of_exact_factor (G : Digraph E) (w : E × E → ℝ≥0) (α : ℝ)
    (factor : HasEdgeRoundingFactor G w α) :
    ∃ p : PMF (Finset (E × E)),
      (∀ X ∈ p.support, X ⊆ graphEdges G ∧ IsIntegralEdgeCut G X (edgeThresholdDemands G w)) ∧
      ∀ e, (p.toOuterMeasure {X | e ∈ X}).toReal ≤ α * (w e : ℝ) := by
  obtain ⟨p,support,margin⟩ := law_of_all_cost_factor
    (fun X => X ⊆ graphEdges G ∧ IsIntegralEdgeCut G X (edgeThresholdDemands G w))
    (fun e => (actualEdgeWeight G w e : ℝ)) α (fun e => (actualEdgeWeight G w e).coe_nonneg)
    factor.nonneg factor.real_cost_round
  refine ⟨p,support,fun e => (margin e).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ factor.nonneg
  unfold actualEdgeWeight
  split <;> simp

end
end DirectedFlowCutGap.WeakDecomposition

namespace DirectedFlowCutGap.ExactFlowCutGap

noncomputable section
open scoped NNReal

def VertexBound (n : ℕ) (W : ℝ≥0) (k : ℕ) : Prop :=
  ∀ (G : Digraph (Fin n)) (w : Fin n → ℝ≥0), totalWeight w = W →
    HasVertexRoundingFactor G w (k : ℝ)

def EdgeBound (n : ℕ) (W : ℝ≥0) (k : ℕ) : Prop :=
  ∀ (G : Digraph (Fin n)) (w : Fin n × Fin n → ℝ≥0), totalEdgeWeight G w = W →
    HasEdgeRoundingFactor G w (k : ℝ)

private theorem vertexBound_exists (n : ℕ) (W : ℝ≥0) : ∃ k, VertexBound n W k := by
  refine ⟨n,?_⟩
  intro G w _
  simpa only [Fintype.card_fin] using hasVertexRoundingFactor_card G w

private theorem edgeBound_exists (n : ℕ) (W : ℝ≥0) : ∃ k, EdgeBound n W k := by
  obtain ⟨K,_,oracle⟩ := AdaptiveEdgeBound.hasEdgeRoundingFactor_uniform.{0} 1 one_pos
  let b : ℝ := K * (n : ℝ) ^ ((1 : ℝ) / 3 + 1)
  refine ⟨⌈b⌉₊,?_⟩
  intro G w _
  apply WeakDecomposition.edge_factor_mono (α:=b)
  · simpa only [b,Fintype.card_fin] using oracle (Fin n) G w
  · exact Nat.le_ceil b

def vfg (n : ℕ) (W : ℝ≥0) : ℕ := by
  classical
  exact Nat.find (vertexBound_exists n W)

def efg (n : ℕ) (W : ℝ≥0) : ℕ := by
  classical
  exact Nat.find (edgeBound_exists n W)

theorem vfg_bound (n : ℕ) (W : ℝ≥0) : VertexBound n W (vfg n W) := by
  classical
  exact Nat.find_spec (vertexBound_exists n W)

theorem efg_bound (n : ℕ) (W : ℝ≥0) : EdgeBound n W (efg n W) := by
  classical
  exact Nat.find_spec (edgeBound_exists n W)

theorem vfg_le {n : ℕ} {W : ℝ≥0} {k : ℕ} (bound : VertexBound n W k) : vfg n W ≤ k := by
  classical
  exact Nat.find_min' (vertexBound_exists n W) bound

theorem efg_le {n : ℕ} {W : ℝ≥0} {k : ℕ} (bound : EdgeBound n W k) : efg n W ≤ k := by
  classical
  exact Nat.find_min' (edgeBound_exists n W) bound

theorem vertex_law {n : ℕ} (G : Digraph (Fin n)) (w : Fin n → ℝ≥0) :
    ∃ p : PMF (Finset (Fin n)), (∀ X ∈ p.support, IsIntegralCut G X (thresholdDemands G w)) ∧
      ∀ e, (p.toOuterMeasure {X | e ∈ X}).toReal ≤ (vfg n (totalWeight w) : ℝ) * (w e : ℝ) :=
  WeakDecomposition.vertex_law_of_exact_factor (vfg_bound n (totalWeight w) G w rfl)

theorem edge_law {n : ℕ} (G : Digraph (Fin n)) (w : Fin n × Fin n → ℝ≥0) :
    ∃ p : PMF (Finset (Fin n × Fin n)),
      (∀ X ∈ p.support, X ⊆ graphEdges G ∧ IsIntegralEdgeCut G X (edgeThresholdDemands G w)) ∧
      ∀ e, (p.toOuterMeasure {X | e ∈ X}).toReal ≤ (efg n (totalEdgeWeight G w) : ℝ) * (w e : ℝ) :=
  WeakDecomposition.edge_law_of_exact_factor G w _ (efg_bound n (totalEdgeWeight G w) G w rfl)

end
end DirectedFlowCutGap.ExactFlowCutGap
