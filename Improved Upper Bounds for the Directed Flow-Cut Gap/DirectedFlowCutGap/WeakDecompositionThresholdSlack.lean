import DirectedFlowCutGap.WeakDecompositionLightBudget

/-! A distance margin can pay for removal of light arcs without rescaling
the remaining weights. This keeps the rounding query at the original
weight budget, including on dense graphs. -/
namespace DirectedFlowCutGap.ExactFlowCutGap

noncomputable section

open scoped BigOperators NNReal ENNReal
open WeakDecomposition
attribute [local instance] Classical.propDecidable

def thresholdSlackCutoff (n : ℕ) : ℝ≥0 := (2*(n : ℝ≥0))⁻¹

def trimmedForSlack {n : ℕ} (G : Digraph (Fin n)) (w : Fin n × Fin n → ℝ≥0)
    (e : Fin n × Fin n) : ℝ≥0 :=
  let a := actualEdgeWeight G w e
  if a ≤ thresholdSlackCutoff n then 0 else a

theorem trimmedForSlack_le {n : ℕ} (G : Digraph (Fin n)) (w : Fin n × Fin n → ℝ≥0)
    (e : Fin n × Fin n) : trimmedForSlack G w e ≤ w e := by
  unfold trimmedForSlack
  dsimp only
  split
  · exact zero_le
  · by_cases adj : G.Adj e.1 e.2 <;> simp [actualEdgeWeight,adj]

private theorem path_split {n : ℕ} {G : Digraph (Fin n)} {s t : Fin n} (p : SimplePath G s t)
    (w : Fin n × Fin n → ℝ≥0) :
    p.edgeWeight w = p.edgeWeight (trimmedForSlack G w) + p.edgeWeight (lightWeight G w (thresholdSlackCutoff n)) := by
  unfold SimplePath.edgeWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e h
  unfold trimmedForSlack lightWeight
  dsimp only
  rw [actualEdgeWeight_of_adj G w (p.edge_adj h)]
  split_ifs <;> simp

theorem trim_preserves_slack_demands {n : ℕ} (G : Digraph (Fin n)) (w : Fin n × Fin n → ℝ≥0)
    (slack : ∀ e ∈ edgeThresholdDemands G w,
      ((1+outgoingLightLoss G w (thresholdSlackCutoff n) : ℝ≥0) : ℝ≥0∞) ≤ edgeDistance G w e.1 e.2) :
    edgeThresholdDemands G w ⊆ edgeThresholdDemands G (trimmedForSlack G w) := by
  rintro ⟨s,t⟩ demand
  apply (coe_le_edgeDistance_iff G (trimmedForSlack G w) s t 1).mpr
  intro path
  have base := (coe_le_edgeDistance_iff G w s t _).mp (slack (s,t) demand) path
  rw [path_split path w] at base
  have removed := edge_path_light_loss_le path w (thresholdSlackCutoff n)
  exact le_of_add_le_add_right (base.trans (add_le_add_right removed _))

private theorem horizon_le {n : ℕ} (hn : 0 < n) {W U : ℝ≥0} (le : W ≤ U) :
    edgeHorizon n W ≤ edgeHorizon n U := by
  unfold edgeHorizon
  apply Nat.add_le_add_right
  apply Nat.ceil_mono
  have npos : 0 < (n : ℝ) := by exact_mod_cast hn
  have leR := NNReal.coe_le_coe.mpr le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.log_le_log (by positivity)
  gcongr

theorem edge_uniform_of_threshold_slack {n : ℕ} (hn : 0 < n) (G : Digraph (Fin n))
    (w : Fin n × Fin n → ℝ≥0)
    (slack : ∀ e ∈ edgeThresholdDemands G w,
      ((1+outgoingLightLoss G w (thresholdSlackCutoff n) : ℝ≥0) : ℝ≥0∞) ≤ edgeDistance G w e.1 e.2) :
    let W := totalEdgeWeight G w
    let α : ℝ := efg n W
    ∃ T ≤ edgeHorizon n W, 0 < T ∧
      ∃ X : Fin T → Finset (Fin n × Fin n),
        (∀ i, X i ⊆ graphEdges G ∧ IsIntegralEdgeCut G (X i) (edgeThresholdDemands G w)) ∧
        ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ)/(T : ℝ) ≤ 4*α*(w e : ℝ) := by
  classical
  let W := totalEdgeWeight G w
  let factor := efg n W
  let α : ℝ := factor
  let q := trimmedForSlack G w
  have mass : totalEdgeWeight G q ≤ W := Finset.sum_le_sum fun e _ => trimmedForSlack_le G w e
  by_cases zero : factor = 0
  · obtain ⟨Y,ok,cost⟩ := (efg_bound n W G w rfl).real_cost_round (fun _ => 1) (fun _ => zero_le_one)
    have zero_card : (Y.card : ℝ) ≤ 0 := by simpa [W,factor,zero] using cost
    have empty : Y = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp (by exact_mod_cast zero_card))
    subst Y
    exact ⟨1,edgeHorizon_pos _ _,Nat.one_pos,fun _ => ∅,fun _ => ok,by simp [W,factor,zero]⟩
  have alpha : 1 ≤ α := by
    change (1 : ℝ) ≤ (factor : ℝ)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr zero
  have floor (e : Fin n × Fin n) (_ : e ∈ graphEdges G) (pos : 0 < q e) :
      (2*(Fintype.card (Fin n) : ℝ≥0))⁻¹ ≤ q e := by
    rw [Fintype.card_fin]
    unfold q trimmedForSlack at pos ⊢
    dsimp only at pos ⊢
    by_cases h : actualEdgeWeight G w e ≤ thresholdSlackCutoff n
    · rw [ite_eq_left h] at pos
      exact (lt_irrefl _ pos).elim
    · rw [ite_eq_right h]
      exact (lt_of_not_ge h).le
  have oracle : HasEdgeRoundingFactor G q α := efg_round_atMost hn G q mass
  have card : 0 < Fintype.card (Fin n) := by simpa only [Fintype.card_fin] using hn
  obtain ⟨X,valid,_,bound⟩ := edge_family_of_original_floor G q α card alpha oracle floor
  refine ⟨_,?_,edgeHorizon_pos _ _,X,?_,?_⟩
  · simpa only [Fintype.card_fin] using horizon_le hn mass
  · intro i
    exact ⟨(valid i).1,fun s t d => (valid i).2 s t (trim_preserves_slack_demands G w slack d)⟩
  · intro e
    exact (bound e).trans (mul_le_mul_of_nonneg_left
      (NNReal.coe_le_coe.mpr (trimmedForSlack_le G w e)) (by positivity))

theorem edge_uniform_of_half_threshold_slack {n : ℕ} (hn : 0 < n) (G : Digraph (Fin n))
    (w : Fin n × Fin n → ℝ≥0)
    (slack : ∀ e ∈ edgeThresholdDemands G w, (3/2 : ℝ≥0∞) ≤ edgeDistance G w e.1 e.2) :
    let W := totalEdgeWeight G w
    let α : ℝ := efg n W
    ∃ T ≤ edgeHorizon n W, 0 < T ∧
      ∃ X : Fin T → Finset (Fin n × Fin n),
        (∀ i, X i ⊆ graphEdges G ∧ IsIntegralEdgeCut G (X i) (edgeThresholdDemands G w)) ∧
        ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ)/(T : ℝ) ≤ 4*α*(w e : ℝ) := by
  apply edge_uniform_of_threshold_slack hn G w
  have nn : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  have total : (n : ℝ≥0)*thresholdSlackCutoff n = 1/2 := by
    unfold thresholdSlackCutoff
    field_simp
  have loss := (outgoing_light_loss_le G w (thresholdSlackCutoff n)).trans_eq total
  intro e h
  apply le_trans _ (slack e h)
  have bound : 1+outgoingLightLoss G w (thresholdSlackCutoff n) ≤ (3/2 : ℝ≥0) := calc
    _ ≤ 1+(1/2 : ℝ≥0) := add_le_add_right loss _
    _ = _ := by norm_num
  exact (ENNReal.coe_le_coe.mpr bound).trans_eq (by norm_num)

end
end DirectedFlowCutGap.ExactFlowCutGap
