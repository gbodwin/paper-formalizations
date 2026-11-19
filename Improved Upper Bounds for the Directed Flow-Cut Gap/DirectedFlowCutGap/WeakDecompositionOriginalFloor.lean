import DirectedFlowCutGap.WeakDecomposition

/-! The near-linear horizon at the original weight vector for graphs whose
positive edge weights already satisfy the preprocessing floor. -/
namespace DirectedFlowCutGap.WeakDecomposition

noncomputable section

open scoped NNReal BigOperators
open Set

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem edge_family_of_original_floor (G : Digraph V) (w : V × V → ℝ≥0) (α : ℝ)
    (hn : 0 < Fintype.card V) (hα : 1 ≤ α) (oracle : HasEdgeRoundingFactor G w α)
    (floor : ∀ e ∈ graphEdges G, 0 < w e → (2*(Fintype.card V : ℝ≥0))⁻¹ ≤ w e) :
    ∃ X : Fin (edgeHorizon (Fintype.card V) (totalEdgeWeight G w)) → Finset (V × V),
      (∀ i, X i ⊆ graphEdges G ∧ IsIntegralEdgeCut G (X i) (edgeThresholdDemands G w)) ∧
      (∀ i e, e ∈ X i → 0 < w e) ∧
      ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ) /
        (edgeHorizon (Fintype.card V) (totalEdgeWeight G w) : ℝ) ≤ 4*α*(w e : ℝ) := by
  classical
  let n : ℝ := Fintype.card V
  let δ : ℝ := (2*n)⁻¹
  let a : V × V → ℝ := fun e => (actualEdgeWeight G w e : ℝ)
  let W : ℝ := totalEdgeWeight G w
  let T := edgeHorizon (Fintype.card V) (totalEdgeWeight G w)
  have npos : 0 < n := by dsimp [n]; exact_mod_cast hn
  have hd : 0 < δ := by unfold δ; positivity
  have hweight (e : V × V) : 0 ≤ a e := (actualEdgeWeight G w e).coe_nonneg
  have positive (e : V × V) (he : 0 < a e) : δ ≤ a e := by
    by_cases adjacent : G.Adj e.1 e.2
    · have actual : 0 < w e := by simpa [a,actualEdgeWeight,adjacent] using he
      have kept := floor e ((mem_graphEdges G e).mpr adjacent) actual
      simpa [a,δ,n,actualEdgeWeight,adjacent] using NNReal.coe_le_coe.mpr kept
    · simp [a,actualEdgeWeight,adjacent] at he
  have hnδ : (Fintype.card (V × V) : ℝ)*δ=n/2 := by
    simp only [Fintype.card_prod,Nat.cast_mul]
    change n*n*(2*n)⁻¹=n/2
    field_simp
  have total : (∑ e, max δ (a e)) ≤ W+n/2 := by
    calc
      _ ≤ ∑ e, (a e+δ) := Finset.sum_le_sum fun e _ => max_le
        (by linarith [hweight e]) (by linarith [hd])
      _ = (∑ e, a e)+(Fintype.card (V × V) : ℝ)*δ := by
        rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _ = W+n/2 := by rw [hnδ]; exact congrArg (·+n/2) (sum_actualEdgeWeight G w)
  have totalPos : 0 < ∑ e, max δ (a e) := by
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp hn
    exact hd.trans_le ((le_max_left _ _).trans
      (Finset.single_le_sum (fun e _ => hd.le.trans (le_max_left _ _)) (Finset.mem_univ (v,v))))
  have ratio : (∑ e, max δ (a e))/δ ≤ n*(2*W+n) := by
    apply (div_le_iff₀ hd).mpr
    have eq : n*(2*W+n)*δ=W+n/2 := by
      unfold δ
      field_simp
    exact total.trans_eq eq.symm
  have log := Real.log_le_log (div_pos totalPos hd) ratio
  have ceil : 2*n*Real.log (n*(2*W+n)) ≤ T := by
    have h := Nat.le_ceil (2*n*Real.log (n*(2*W+n)))
    exact h.trans (by unfold T edgeHorizon; push_cast; linarith)
  have bound : Real.log ((∑ e, max δ (a e))/δ) ≤ δ*T := by
    apply log.trans
    have h : Real.log (n*(2*W+n)) ≤ T/(2*n) :=
      (le_div_iff₀ (by positivity : 0 < 2*n)).mpr (by nlinarith [ceil])
    simpa [δ, div_eq_mul_inv, mul_comm] using h
  have scale : δ ≤ δ*α := le_mul_of_one_le_right hd.le hα
  obtain ⟨X,valid,kept,cost⟩ := family_of_positive_floor a α δ δ
    (fun X => X ⊆ graphEdges G ∧ IsIntegralEdgeCut G X (edgeThresholdDemands G w))
    hweight (by linarith) hd hd positive scale oracle.real_cost_round T (edgeHorizon_pos _ _) bound
  have point (e : V × V) : a e ≤ w e := by
    by_cases adj : G.Adj e.1 e.2 <;> simp [a,actualEdgeWeight,adj]
  refine ⟨X,valid,fun i e he => ?_,fun e => ?_⟩
  · exact NNReal.coe_pos.mp ((kept i e he).trans_le (point e))
  · exact (cost e).trans (mul_le_mul_of_nonneg_left (point e) (by positivity))

theorem edge_law_of_original_floor (G : Digraph V) (w : V × V → ℝ≥0) (α : ℝ)
    (hn : 0 < Fintype.card V) (hα : 1 ≤ α) (oracle : HasEdgeRoundingFactor G w α)
    (floor : ∀ e ∈ graphEdges G, 0 < w e → (2*(Fintype.card V : ℝ≥0))⁻¹ ≤ w e) :
    ∃ X : Fin (edgeHorizon (Fintype.card V) (totalEdgeWeight G w)) → Finset (V × V),
      let p := familyLaw (edgeHorizon_pos (Fintype.card V) (totalEdgeWeight G w)) X
      (∀ cut ∈ p.support, cut ⊆ graphEdges G ∧ IsIntegralEdgeCut G cut (edgeThresholdDemands G w)) ∧
      ∀ e, (p.toOuterMeasure {cut | e ∈ cut}).toReal ≤ 4*α*(w e : ℝ) := by
  obtain ⟨X,valid,_,bound⟩ := edge_family_of_original_floor G w α hn hα oracle floor
  let T := edgeHorizon_pos (Fintype.card V) (totalEdgeWeight G w)
  refine ⟨X,?_,?_⟩
  · intro cut supported
    exact familyLaw_support T X
      (fun cut => cut ⊆ graphEdges G ∧ IsIntegralEdgeCut G cut (edgeThresholdDemands G w)) valid supported
  · intro e
    rw [familyLaw_marginal]
    exact bound e

end
end DirectedFlowCutGap.WeakDecomposition
