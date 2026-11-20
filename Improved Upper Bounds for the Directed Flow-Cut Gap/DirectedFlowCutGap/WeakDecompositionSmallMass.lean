import DirectedFlowCutGap.WeakCutExactMarginal

/-! An exact-weight uniform family can avoid arbitrarily small edges when
their total weight fits the original oracle's penalty budget. -/
namespace DirectedFlowCutGap.WeakDecomposition

noncomputable section

open scoped NNReal BigOperators
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
def smallEdgeMass (G : Digraph V) (w : V × V → ℝ≥0) (cutoff : ℝ) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e => (actualEdgeWeight G w e : ℝ) ≤ cutoff),
    (actualEdgeWeight G w e : ℝ)

theorem smallEdgeMass_le_arc_count (G : Digraph V) (w : V × V → ℝ≥0) (cutoff : ℝ)
    (nonneg : 0≤cutoff) : smallEdgeMass G w cutoff ≤ ((graphEdges G).card : ℝ)*cutoff := by
  let light := Finset.univ.filter (fun e => (actualEdgeWeight G w e : ℝ)≤cutoff)
  let actual := graphEdges G
  have remove_nonarcs : (∑ e ∈ light ∩ actual, (actualEdgeWeight G w e : ℝ)) =
       ∑ e ∈ light, (actualEdgeWeight G w e : ℝ) := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro e hl notBoth
    have missing : e ∉ actual := fun isArc => notBoth (Finset.mem_inter.mpr ⟨hl,isArc⟩)
    have notAdj : ¬G.Adj e.1 e.2 := fun yes => missing ((mem_graphEdges G e).mpr yes)
    rw [actualEdgeWeight_of_not_adj G w notAdj,NNReal.coe_zero]
  change (∑ e ∈ light, (actualEdgeWeight G w e : ℝ)) ≤ (actual.card : ℝ)*cutoff
  rw [← remove_nonarcs]
  calc
    _ ≤ ∑ _e ∈ light ∩ actual, cutoff := Finset.sum_le_sum (fun e h =>
      (Finset.mem_filter.mp (Finset.mem_inter.mp h).1).2)
    _ = ((light ∩ actual).card : ℝ)*cutoff := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr
      (Finset.card_le_card Finset.inter_subset_right)) nonneg

def smallMassHorizon (n k : ℕ) (W : ℝ≥0) (α : ℝ) : ℕ :=
  ⌈2*(k : ℝ)*Real.log (4*α*(k : ℝ)*(W : ℝ)+(n : ℝ)^2)⌉₊+1

theorem edge_family_of_small_mass (G : Digraph V) (w : V × V → ℝ≥0) (α : ℝ) (k : ℕ)
    {n : ℕ} (cardV : Fintype.card V=n) (hn : 0 < n) (hk : 0 < k) (hα : 0 < α)
    (oracle : HasEdgeRoundingFactor G w α)
    (small : α * smallEdgeMass G w (4*α*(k : ℝ))⁻¹ ≤ 1/4) :
    ∃ X : Fin (smallMassHorizon n k (totalEdgeWeight G w) α) → Finset (V × V),
      (∀ i, X i ⊆ graphEdges G ∧ IsIntegralEdgeCut G (X i) (edgeThresholdDemands G w)) ∧
      ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ) /
          (smallMassHorizon n k (totalEdgeWeight G w) α : ℝ) ≤ 8*α*(w e : ℝ) := by
  classical
  let N : ℝ := n
  let K : ℝ := k
  let δ := (4*α*K)⁻¹
  let scale := (2*K)⁻¹
  let W : ℝ := totalEdgeWeight G w
  let T := smallMassHorizon n k (totalEdgeWeight G w) α
  let weight (e : V × V) : ℝ := actualEdgeWeight G w e
  let tiny := Finset.univ.filter fun e => weight e ≤ δ
  let kept (e : V × V) := if e ∈ tiny then 0 else weight e
  let valid (X : Finset (V × V)) := X ⊆ graphEdges G ∧ IsIntegralEdgeCut G X (edgeThresholdDemands G w)
  have kpos : 0 < K := by dsimp [K]; exact_mod_cast hk
  have npos : 0 < N := by dsimp [N]; exact_mod_cast hn
  have δpos : 0 < δ := by unfold δ; positivity
  have δeq : 4*α*K*δ=1 := by unfold δ; field_simp
  have rate : scale=δ*(2*α) := by unfold scale δ; field_simp; ring
  have weight_nonneg (e : V × V) : 0 ≤ weight e := (actualEdgeWeight G w e).coe_nonneg
  have tiny_iff (e : V × V) : e ∈ tiny ↔ weight e ≤ δ := by simp [tiny]
  have positive (e : V × V) (he : e ∉ tiny) : 0 < weight e :=
    δpos.trans (lt_of_not_ge (fun h => he ((tiny_iff e).mpr h)))
  have kept_floor (e : V × V) (he : 0 < kept e) : δ ≤ kept e := by
    by_cases h : e ∈ tiny
    · simp [kept,h] at he
    · simpa only [kept,h,ite_false] using (lt_of_not_ge (fun h' => h ((tiny_iff e).mpr h'))).le
  have kept_le (e : V × V) : kept e ≤ weight e := by
    unfold kept
    split
    · exact weight_nonneg e
    · exact le_rfl
  have kept_nonneg (e : V × V) : 0 ≤ kept e := by
    unfold kept
    split
    · exact le_rfl
    · exact weight_nonneg e
  have retained : ∀ c : V × V → ℝ, (∀ e, 0 ≤ c e) →
      ∃ X, valid X ∧ (∑ e ∈ X, c e) ≤ (2*α)*mwPotential kept c := by
    intro c nonneg
    obtain ⟨X,ok,_,cost⟩ := BoundedSampling.oracle_avoids_small_mass weight α valid tiny
      weight_nonneg hα small positive oracle.real_cost_round c nonneg
    refine ⟨X,ok,cost.trans_eq ?_⟩
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : e ∈ tiny <;> simp [kept,h]
  have card : (Fintype.card (V × V) : ℝ)=N^2 := by simp [N,cardV,pow_two]
  have sum_bound : (∑ e, max δ (kept e)) ≤ W+N^2*δ := by
    calc
      _ ≤ ∑ e, (weight e+δ) := Finset.sum_le_sum fun e _ =>
        max_le (by linarith [weight_nonneg e]) ((kept_le e).trans (by linarith))
      _ = _ := by
        rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card]
        rw [show (∑ e, weight e)=W from sum_actualEdgeWeight G w]
  let U := 4*α*K*W+N^2
  have ratio : (∑ e, max δ (kept e))/δ ≤ U := (div_le_iff₀ δpos).mpr (by
    have budget : U*δ=W+N^2*δ := by
      unfold U
      rw [add_mul, mul_assoc (4*α*K) W δ,mul_comm W δ,← mul_assoc,δeq,one_mul]
    rwa [budget])
  have sum_pos : 0 < ∑ e, max δ (kept e) := by
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp (cardV ▸ hn)
    exact δpos.trans_le ((le_max_left _ _).trans
      (Finset.single_le_sum (fun e _ => δpos.le.trans (le_max_left _ _)) (Finset.mem_univ (v,v))))
  have log := Real.log_le_log (div_pos sum_pos δpos) ratio
  have horizon : Real.log U ≤ scale*(T : ℝ) := by
    have ceil := Nat.le_ceil (2*K*Real.log U)
    have upper : 2*K*Real.log U ≤ (T : ℝ) := by
      unfold T smallMassHorizon
      push_cast
      change 2*K*Real.log U ≤ (⌈2*K*Real.log U⌉₊ : ℝ)+1
      linarith
    have divided : Real.log U ≤ (T : ℝ)/(2*K) :=
      (le_div_iff₀ (by positivity : 0 < 2*K)).mpr (by simpa only [mul_comm (Real.log U)] using upper)
    simpa only [div_eq_mul_inv,mul_comm (T : ℝ),scale] using
      divided
  obtain ⟨X,ok,_,bounds⟩ := family_of_positive_floor kept (2*α) δ scale valid kept_nonneg
    (by positivity) δpos (by unfold scale; positivity) kept_floor rate.le retained T
    (Nat.zero_lt_succ _) (log.trans horizon)
  refine ⟨X,ok,fun e => (bounds e).trans ?_⟩
  have original : weight e ≤ (w e : ℝ) := by
    unfold weight actualEdgeWeight
    split
    · exact le_rfl
    · exact (w e).coe_nonneg
  calc
    _ = 8*α*kept e := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ((kept_le e).trans original) (by positivity)

omit [DecidableEq V] in
theorem smallEdgeMass_le_of_card (G : Digraph V) (w : V × V → ℝ≥0) (cutoff : ℝ) (k : ℕ)
    (pos : 0 ≤ cutoff)
    (few : (Finset.univ.filter (fun e => 0 < actualEdgeWeight G w e ∧
      (actualEdgeWeight G w e : ℝ) ≤ cutoff)).card ≤ k) :
    smallEdgeMass G w cutoff ≤ (k : ℝ)*cutoff := by
  let positive := Finset.univ.filter fun e => 0 < actualEdgeWeight G w e ∧
    (actualEdgeWeight G w e : ℝ) ≤ cutoff
  let tiny := Finset.univ.filter fun e => (actualEdgeWeight G w e : ℝ) ≤ cutoff
  have subset : positive ⊆ tiny := by
    intro e he
    simp only [positive,Finset.mem_filter,Finset.mem_univ,true_and] at he
    simpa [tiny] using he.2
  have zero (e : V × V) (he : e ∈ tiny) (absent : e ∉ positive) :
      (actualEdgeWeight G w e : ℝ)=0 := by
    by_contra h
    have hp : 0 < actualEdgeWeight G w e := by
      exact pos_iff_ne_zero.mpr (fun h' => h (by simp [h']))
    exact absent (Finset.mem_filter.mpr ⟨Finset.mem_univ e,hp,(Finset.mem_filter.mp he).2⟩)
  calc
    _ = ∑ e ∈ positive, (actualEdgeWeight G w e : ℝ) := (Finset.sum_subset subset zero).symm
    _ ≤ ∑ _e ∈ positive, cutoff := Finset.sum_le_sum fun e he =>
      ((Finset.mem_filter.mp he).2).2
    _ = (positive.card : ℝ)*cutoff := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast few) pos

theorem edge_family_of_few_tiny_edges (G : Digraph V) (w : V × V → ℝ≥0) (α : ℝ) (k : ℕ)
    (hn : 0 < Fintype.card V) (hk : 0 < k) (hα : 0 < α)
    (oracle : HasEdgeRoundingFactor G w α)
    (few : (Finset.univ.filter (fun e => 0 < actualEdgeWeight G w e ∧
      (actualEdgeWeight G w e : ℝ) ≤ (4*α*(k : ℝ))⁻¹)).card ≤ k) :
    ∃ X : Fin (smallMassHorizon (Fintype.card V) k (totalEdgeWeight G w) α) → Finset (V × V),
      (∀ i, X i ⊆ graphEdges G ∧ IsIntegralEdgeCut G (X i) (edgeThresholdDemands G w)) ∧
      ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ) /
          (smallMassHorizon (Fintype.card V) k (totalEdgeWeight G w) α : ℝ) ≤ 8*α*(w e : ℝ) := by
  apply edge_family_of_small_mass G w α k rfl hn hk hα oracle
  have kpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  calc
    _ ≤ α*((k : ℝ)*(4*α*(k : ℝ))⁻¹) := mul_le_mul_of_nonneg_left
      (smallEdgeMass_le_of_card G w _ k (by positivity) few) hα.le
    _ = _ := by field_simp

end
end DirectedFlowCutGap.WeakDecomposition

namespace DirectedFlowCutGap.ExactFlowCutGap

noncomputable section
open scoped NNReal BigOperators
open WeakDecomposition

theorem edge_uniform_of_small_mass_at_scale {n k : ℕ} (hn : 0 < n)
    (G : Digraph (Fin n)) (w : Fin n × Fin n → ℝ≥0) (hk : 0 < k)
    (small : let α : ℝ := efg n (totalEdgeWeight G w)
      α*smallEdgeMass G w (4*α*(k : ℝ))⁻¹ ≤ 1/4) :
    let α : ℝ := efg n (totalEdgeWeight G w)
    let T := smallMassHorizon n k (totalEdgeWeight G w) α
    ∃ X : Fin T → Finset (Fin n × Fin n),
      let p := familyLaw (show 0 < T from Nat.zero_lt_succ _) X
      (∀ Y ∈ p.support, Y ⊆ graphEdges G ∧ IsIntegralEdgeCut G Y (edgeThresholdDemands G w)) ∧
      ∀ e, (p.toOuterMeasure {Y | e ∈ Y}).toReal ≤ 8*α*(w e : ℝ) := by
  classical
  let α : ℝ := efg n (totalEdgeWeight G w)
  let T := smallMassHorizon n k (totalEdgeWeight G w) α
  have ht : 0 < T := Nat.zero_lt_succ _
  have oracle : HasEdgeRoundingFactor G w α := efg_bound n (totalEdgeWeight G w) G w rfl
  have valid_card : ∃ X : Fin T → Finset (Fin n × Fin n),
      (∀ i, X i ⊆ graphEdges G ∧ IsIntegralEdgeCut G (X i) (edgeThresholdDemands G w)) ∧
      ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ)/(T : ℝ) ≤ 8*α*(w e : ℝ) := by
    by_cases pos : 0 < α
    · exact edge_family_of_small_mass G w α k (Fintype.card_fin n) hn hk pos oracle small
    · have zero : α=0 := le_antisymm (le_of_not_gt pos) oracle.nonneg
      obtain ⟨Y,ok,cost⟩ := oracle.real_cost_round (fun _ => 1) (fun _ => zero_le_one)
      have zero_card : (Y.card : ℝ) ≤ 0 := by simpa [zero] using cost
      have empty : Y=∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp (by exact_mod_cast zero_card))
      subst Y
      exact ⟨fun _ => ∅,fun _ => ok,by simp [zero]⟩
  obtain ⟨X,ok,card⟩ := valid_card
  refine ⟨X,?_,?_⟩
  · exact fun Y hY => familyLaw_support ht X
      (fun Z => Z ⊆ graphEdges G ∧ IsIntegralEdgeCut G Z (edgeThresholdDemands G w)) ok hY
  · intro e
    rw [familyLaw_marginal]
    exact card e

theorem edge_uniform_of_small_mass {n : ℕ} (hn : 0 < n)
    (G : Digraph (Fin n)) (w : Fin n × Fin n → ℝ≥0)
    (small : let α : ℝ := efg n (totalEdgeWeight G w)
      α*smallEdgeMass G w (4*α*(n : ℝ))⁻¹ ≤ 1/4) :
    let α : ℝ := efg n (totalEdgeWeight G w)
    let T := smallMassHorizon n n (totalEdgeWeight G w) α
    ∃ X : Fin T → Finset (Fin n × Fin n),
      let p := familyLaw (show 0 < T from Nat.zero_lt_succ _) X
      (∀ Y ∈ p.support, Y ⊆ graphEdges G ∧ IsIntegralEdgeCut G Y (edgeThresholdDemands G w)) ∧
      ∀ e, (p.toOuterMeasure {Y | e ∈ Y}).toReal ≤ 8*α*(w e : ℝ) :=
  edge_uniform_of_small_mass_at_scale hn G w hn small

/-- An original-factor family needs a horizon proportional to the actual
arc count, up to the displayed log factor. -/
theorem edge_uniform_at_original_arc_count {n : ℕ} (hn : 0 < n)
    (G : Digraph (Fin n)) (w : Fin n × Fin n → ℝ≥0) :
    let α : ℝ := efg n (totalEdgeWeight G w)
    let k := max 1 (graphEdges G).card
    let T := smallMassHorizon n k (totalEdgeWeight G w) α
    ∃ X : Fin T → Finset (Fin n × Fin n),
      let p := familyLaw (show 0 < T from Nat.zero_lt_succ _) X
      (∀ Y ∈ p.support, Y ⊆ graphEdges G ∧ IsIntegralEdgeCut G Y (edgeThresholdDemands G w)) ∧
      ∀ e, (p.toOuterMeasure {Y | e ∈ Y}).toReal ≤ 8*α*(w e : ℝ) := by
  let α : ℝ := efg n (totalEdgeWeight G w)
  let k := max 1 (graphEdges G).card
  have kpos : 0<k := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  refine edge_uniform_of_small_mass_at_scale hn G w kpos ?_
  change α*smallEdgeMass G w (4*α*(k : ℝ))⁻¹ ≤ 1/4
  by_cases hα : α=0
  · rw [hα,zero_mul]
    norm_num
  · have apos : 0<α := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hα)
    let δ := (4*α*(k : ℝ))⁻¹
    have nonneg : 0≤δ := by dsimp only [δ]; positivity
    have card : ((graphEdges G).card : ℝ)≤k := Nat.cast_le.mpr (le_max_right _ _)
    have bound := (smallEdgeMass_le_arc_count G w δ nonneg).trans (mul_le_mul_of_nonneg_right card nonneg)
    exact (mul_le_mul_of_nonneg_left bound apos.le).trans_eq (by
      unfold δ
      field_simp)

end
end DirectedFlowCutGap.ExactFlowCutGap
