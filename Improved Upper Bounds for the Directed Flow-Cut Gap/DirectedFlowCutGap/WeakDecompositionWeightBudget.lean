import DirectedFlowCutGap.ExactEdgeWeightPadding
import DirectedFlowCutGap.WeakDecompositionOriginalFloor
import DirectedFlowCutGap.WeakDecompositionSmallMass

/-! Exact-weight uniform families from the clipped total and a weight-dependent
horizon. Rescaling preserves the original demands and stays within the original
oracle budget when the mass removed pays for the rescaling. -/
namespace DirectedFlowCutGap.ExactFlowCutGap

noncomputable section

open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

open WeakDecomposition

def clippedWeight {V : Type*} [Fintype V] (w : V × V → ℝ≥0) (e : V × V) : ℝ≥0 :=
  min 1 (TinyEdgePreprocessing.weight w e)

theorem one_le_clamped_path {V : Type*} [DecidableEq V]
    {G : Digraph V} {s t : V} (p : SimplePath G s t) (w : V × V → ℝ≥0)
    (bound : 1≤p.edgeWeight w) : 1≤p.edgeWeight (fun e => min 1 (w e)) := by
  by_cases h : ∃ e ∈ p.edges, 1 ≤ w e
  · obtain ⟨e,member,weight⟩ := h
    calc
      1=min 1 (w e) := (min_eq_left weight).symm
      _≤p.edgeWeight (fun e => min 1 (w e)) :=
        Finset.single_le_sum (f := fun a => min 1 (w a)) (fun _ _ => bot_le) member
  · have eq : p.edgeWeight (fun e => min 1 (w e))=p.edgeWeight w := by
      apply Finset.sum_congr rfl
      intro e member
      exact min_eq_right (le_of_lt (lt_of_not_ge (fun he => h ⟨e,member,he⟩)))
    exact bound.trans_eq eq.symm

private theorem clipped_threshold {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) (w : V × V → ℝ≥0) :
    edgeThresholdDemands G w ⊆ edgeThresholdDemands G (clippedWeight w) := by
  rintro ⟨s,t⟩ demand
  apply (coe_le_edgeDistance_iff G (clippedWeight w) s t 1).mpr
  intro p
  apply one_le_clamped_path p
  exact TinyEdgePreprocessing.path_threshold_preserved p w
    ((coe_le_edgeDistance_iff G w s t 1).mp demand p)

private theorem edgeHorizon_mono {n : ℕ} (hn : 0<n) {W U : ℝ≥0} (le : W≤U) :
    edgeHorizon n W ≤ edgeHorizon n U := by
  unfold edgeHorizon
  apply Nat.add_le_add_right
  apply Nat.ceil_mono
  have npos : 0 < (n : ℝ) := by exact_mod_cast hn
  have leR := NNReal.coe_le_coe.mpr le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.log_le_log (by positivity)
  gcongr

/-- Clipping the preprocessed weights at one leaves threshold demands intact.
When the clipped total fits the original budget, a padded query to the exact
original factor gives a near-linear uniform family. -/
theorem edge_uniform_of_clipped_mass {n : ℕ} (hn : 0<n) (G : Digraph (Fin n)) (w : Fin n × Fin n → ℝ≥0)
    (mass : totalEdgeWeight G (clippedWeight w) ≤ totalEdgeWeight G w) :
    ∃ T ≤ edgeHorizon n (totalEdgeWeight G w), 0<T ∧
      ∃ X : Fin T → Finset (Fin n × Fin n),
        (∀ i, X i ⊆ graphEdges G ∧ IsIntegralEdgeCut G (X i) (edgeThresholdDemands G w)) ∧
        ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ)/(T : ℝ) ≤
          8*(efg n (totalEdgeWeight G w) : ℝ)*(w e : ℝ) := by
  classical
  let q := clippedWeight w
  let α := efg n (totalEdgeWeight G w)
  have bound : EdgeBound n (totalEdgeWeight G w) α := efg_bound n (totalEdgeWeight G w)
  by_cases zero : α=0
  · obtain ⟨Y,ok,cost⟩ := (bound G w rfl).real_cost_round (fun _ => 1) (fun _ => zero_le_one)
    have zero_card : (Y.card : ℝ) ≤ 0 := by simpa [zero] using cost
    have empty : Y=∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp (by exact_mod_cast zero_card))
    subst Y
    exact ⟨1,edgeHorizon_pos ..,Nat.one_pos,fun _ => ∅,fun _ => ok,by simp [α,zero]⟩
  have alpha : (1 : ℝ) ≤ α := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr zero)
  have npos : 0 < (Fintype.card (Fin n) : ℝ≥0) := by
    rw [Fintype.card_fin]
    exact_mod_cast hn
  have floor (e : Fin n × Fin n) (_ : e ∈ graphEdges G) (pos : 0<q e) :
      (2*(Fintype.card (Fin n) : ℝ≥0))⁻¹ ≤ q e := by
    have local_pos : 0<TinyEdgePreprocessing.weight w e := pos.trans_le (min_le_right ..)
    have lower := TinyEdgePreprocessing.positive_weight_lower w e local_pos
    apply le_min
    · exact (inv_le_one₀ (by positivity)).mpr (by
        have n1 : (1 : ℝ≥0) ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact_mod_cast hn
        nlinarith)
    · apply le_trans _ lower
      apply (inv_le_inv₀ (by positivity) npos).mpr
      nlinarith
  have oracle : HasEdgeRoundingFactor G q (α : ℝ) :=
    efg_round_atMost hn G q mass
  have hnFin : 0 < Fintype.card (Fin n) := by simpa only [Fintype.card_fin] using hn
  obtain ⟨X,valid,_,marginal⟩ := edge_family_of_original_floor G q _ hnFin alpha oracle floor
  refine ⟨edgeHorizon (Fintype.card (Fin n)) (totalEdgeWeight G q),?_,edgeHorizon_pos ..,X,?_,?_⟩
  · simpa only [Fintype.card_fin] using edgeHorizon_mono hn mass
  · intro i
    exact ⟨(valid i).1,fun s t d => (valid i).2 s t (clipped_threshold G w d)⟩
  · intro e
    have upper := NNReal.coe_le_coe.mpr ((min_le_right 1 _).trans (TinyEdgePreprocessing.weight_le_twice w e))
    push_cast at upper
    calc
      _ ≤ 4*(α : ℝ)*(q e : ℝ) := marginal e
      _ ≤ 4*(α : ℝ)*(2*(w e : ℝ)) := mul_le_mul_of_nonneg_left upper (by positivity)
      _ = _ := by unfold α; ring

theorem clipped_total_le_card {n : ℕ} (G : Digraph (Fin n)) (w : Fin n × Fin n → ℝ≥0) :
    totalEdgeWeight G (clippedWeight w) ≤ (graphEdges G).card := by
  classical
  unfold totalEdgeWeight
  calc
    _ ≤ ∑ _e ∈ graphEdges G, (1 : ℝ≥0) := Finset.sum_le_sum fun _ _ => min_le_left ..
    _ = _ := by simp

/-- The preprocessing argument applies to all original edge weights when
the oracle's exact factor is evaluated at the modified total. -/
theorem edge_uniform_at_preprocessed_weight {n : ℕ} (hn : 0<n)
    (G : Digraph (Fin n)) (w : Fin n × Fin n → ℝ≥0) :
    let α : ℝ := efg n (totalEdgeWeight G (TinyEdgePreprocessing.weight w))
    ∃ T ≤ edgeHorizon n (totalEdgeWeight G w), 0<T ∧
      ∃ X : Fin T → Finset (Fin n × Fin n),
        (∀ i, X i ⊆ graphEdges G ∧ IsIntegralEdgeCut G (X i) (edgeThresholdDemands G w)) ∧
        ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ)/(T : ℝ) ≤ 8*α*(w e : ℝ) := by
  classical
  let q := TinyEdgePreprocessing.weight w
  let factor := efg n (totalEdgeWeight G q)
  have oracle : HasEdgeRoundingFactor G q (factor : ℝ) :=
    efg_bound n (totalEdgeWeight G q) G q rfl
  by_cases zero : factor=0
  · obtain ⟨Y,ok,cost⟩ := oracle.real_cost_round (fun _ => 1) (fun _ => zero_le_one)
    have zero_card : (Y.card : ℝ) ≤ 0 := by simpa [zero] using cost
    have empty : Y=∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp (by exact_mod_cast zero_card))
    subst Y
    refine ⟨1,edgeHorizon_pos ..,Nat.one_pos,fun _ => ∅,fun _ => ⟨ok.1,?_⟩,?_⟩
    · exact fun s t d => ok.2 s t (TinyEdgePreprocessing.thresholdDemands_subset G w d)
    · intro e
      have nonneg : 0 ≤ 8*(factor : ℝ)*(w e : ℝ) := by positivity
      simpa using nonneg
  have hp : (1 : ℝ) ≤ (factor : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr zero)
  have hnFin : 0<Fintype.card (Fin n) := by simpa only [Fintype.card_fin] using hn
  obtain ⟨X,valid,_,marginals⟩ := edge_family_of_preprocessed_factor G w _ hnFin hp oracle
  exact ⟨_,by simp only [Fintype.card_fin,le_rfl],edgeHorizon_pos ..,X,valid,marginals⟩

theorem smallMassHorizon_mono {n k : ℕ} (hn : 0<n) {α : ℝ} (ha : 0≤α)
    {W U : ℝ≥0} (le : W≤U) : smallMassHorizon n k W α ≤ smallMassHorizon n k U α := by
  unfold smallMassHorizon
  apply Nat.add_le_add_right
  apply Nat.ceil_mono
  have npos : 0 < (n : ℝ) := by exact_mod_cast hn
  have leR := NNReal.coe_le_coe.mpr le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.log_le_log (by positivity)
  gcongr

set_option maxHeartbeats 1200000 in
/-- An original-weight family with a horizon controlled by `k` works without
a weight floor when `k` bounds both the node count and its product with the
total weight. The second case rescales the retained weights by only the
largest loss a simple path could incur. -/
theorem edge_uniform_at_weight_budget {n k : ℕ} (hn : 0<n) (nk : n≤k)
    (G : Digraph (Fin n)) (w : Fin n × Fin n → ℝ≥0)
    (size : (n : ℝ≥0)*totalEdgeWeight G w≤k) :
    let α : ℝ := efg n (totalEdgeWeight G w)
    ∃ T ≤ smallMassHorizon n k (totalEdgeWeight G w) α, 0<T ∧
      ∃ X : Fin T → Finset (Fin n × Fin n),
        (∀ i, X i ⊆ graphEdges G ∧ IsIntegralEdgeCut G (X i) (edgeThresholdDemands G w)) ∧
        ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ)/(T : ℝ) ≤ 16*α*(w e : ℝ) := by
  classical
  let W := totalEdgeWeight G w
  let factor := efg n W
  let α : ℝ := factor
  let horizon := smallMassHorizon n k W α
  have bound : EdgeBound n W factor := efg_bound n W
  have hk := hn.trans_le nk
  by_cases hz : factor=0
  · obtain ⟨Y,ok,cost⟩ := (bound G w rfl).real_cost_round (fun _ => 1) (fun _ => zero_le_one)
    have zero_card : (Y.card : ℝ) ≤ 0 := by simpa [hz] using cost
    have empty : Y=∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp (by exact_mod_cast zero_card))
    subst Y
    refine ⟨1,show 1≤horizon from Nat.zero_lt_succ _,Nat.one_pos,fun _ => ∅,fun _ => ok,?_⟩
    intro e
    have nonneg : 0≤16*(efg n (totalEdgeWeight G w) : ℝ)*(w e : ℝ) := by positivity
    simpa using nonneg
  have al1 : (1 : ℝ)≤α := by
    change (1 : ℝ)≤(factor : ℝ)
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hz)
  have apos : 0<α := zero_lt_one.trans_le al1
  let d : ℝ≥0 := (4*(factor : ℝ≥0)*(k : ℝ≥0))⁻¹
  have d_expr : (d : ℝ)=(4*α*(k : ℝ))⁻¹ := by simp [d,α]
  by_cases small : α*smallEdgeMass G w (d : ℝ)≤1/4
  · rw [d_expr] at small
    obtain ⟨X,ok,h⟩ := edge_family_of_small_mass G w α k (Fintype.card_fin n) hn hk apos
      (bound G w rfl) small
    refine ⟨horizon,le_rfl,Nat.zero_lt_succ _,X,ok,fun e => (h e).trans ?_⟩
    nlinarith [(w e).coe_nonneg]
  let τ : ℝ≥0 := 1-(n : ℝ≥0)*d
  let a (e : Fin n × Fin n) := actualEdgeWeight G w e
  let S := Finset.univ.filter fun e => a e≤d
  let M := ∑ e ∈ S, a e
  let keep (e : Fin n × Fin n) := if a e≤d then 0 else a e
  let raw e := keep e/τ
  let q e := min 1 (raw e)
  have dpos : 0<d := by
    rw [← NNReal.coe_pos,d_expr]
    positivity
  have d_product : 4*α*(k : ℝ)*(d:ℝ)=1 := by
    rw [d_expr]
    exact mul_inv_cancel₀ (by positivity)
  have nRle : (n : ℝ)≤k := by exact_mod_cast nk
  have αk : (k : ℝ)≤α*k := by nlinarith
  have nd_le : (n : ℝ)*(d : ℝ)≤1/4 := by
    have compare := mul_le_mul_of_nonneg_right (nRle.trans αk) d.coe_nonneg
    nlinarith
  have nN : (1 : ℝ)≤n := by exact_mod_cast hn
  have d_lt : d<1 := by
    apply NNReal.coe_lt_coe.mp
    have dn := mul_le_mul_of_nonneg_right nN d.coe_nonneg
    push_cast
    nlinarith
  have τ_value : (τ : ℝ)=1-(n : ℝ)*(d : ℝ) := by
    unfold τ
    rw [NNReal.coe_sub]
    · push_cast
      rfl
    · apply NNReal.coe_le_coe.mp
      push_cast
      linarith
  have τ_lower : (1/2 : ℝ)≤τ := by rw [τ_value]; linarith
  have τ_le : τ≤1 := by unfold τ; exact tsub_le_self
  have τ_pos : 0<τ := NNReal.coe_pos.mp (by linarith)
  have M_small : (M : ℝ)=smallEdgeMass G w (d : ℝ) := by
    simp only [M,S,smallEdgeMass,NNReal.coe_sum,NNReal.coe_le_coe,a]
  have budget : (n : ℝ)*(d : ℝ)*(W : ℝ)≤M := by
    have nW : (n : ℝ)*(W : ℝ)≤k := by exact_mod_cast size
    have nWd := mul_le_mul_of_nonneg_right nW d.coe_nonneg
    have comparison : α*((n : ℝ)*(d : ℝ)*(W : ℝ))≤α*(k : ℝ)*(d : ℝ) := by
      convert mul_le_mul_of_nonneg_left nWd apos.le using 1 <;> ring
    rw [← M_small] at small
    nlinarith
  have sum_a : (∑ e, a e)=W := by exact_mod_cast sum_actualEdgeWeight G w
  have splitMass : (∑ e, keep e)+M=W := by
    unfold M S
    rw [Finset.sum_filter,← Finset.sum_add_distrib,← sum_a]
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : a e≤d <;> simp [keep,h]
  have scale_mass : totalEdgeWeight G q≤W := by
    calc
      _ ≤ ∑ e, q e := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ ≤ ∑ e, keep e/τ := Finset.sum_le_sum (fun e _ => min_le_right ..)
      _ = (∑ e, keep e)/τ := (Finset.sum_div ..).symm
      _ ≤ W := (div_le_iff₀ τ_pos).mpr (by
        have splitR := congrArg (fun x : ℝ≥0 => (x : ℝ)) splitMass
        push_cast at splitR
        apply NNReal.coe_le_coe.mp
        push_cast
        rw [τ_value]
        nlinarith)
  have retained_le (e : Fin n × Fin n) : q e≤2*w e := by
    have below : keep e≤w e := by
      unfold keep a actualEdgeWeight
      split_ifs <;> simp
    apply (min_le_right ..).trans
    apply (div_le_iff₀ τ_pos).mpr
    apply below.trans
    apply NNReal.coe_le_coe.mp
    push_cast
    nlinarith [(w e).coe_nonneg]
  have no_tiny : smallEdgeMass G q (d : ℝ)=0 := by
    unfold smallEdgeMass
    apply Finset.sum_eq_zero
    intro e he
    by_cases adj : G.Adj e.1 e.2
    · have light := (Finset.mem_filter.mp he).2
      rw [actualEdgeWeight_of_adj G q adj] at light ⊢
      by_cases h : a e≤d
      · simp [q,raw,keep,h]
      · have hq : q e≤d := NNReal.coe_le_coe.mp light
        have large : d<q e := by
          apply lt_min d_lt
          have below : a e≤raw e := (le_div_iff₀ τ_pos).mpr (by
            have mul := mul_le_mul_of_nonneg_left τ_le (show 0≤a e from zero_le)
            simpa [keep,h] using mul)
          exact (lt_of_not_ge h).trans_le below
        exact (not_lt_of_ge hq large).elim
    · simp [actualEdgeWeight_of_not_adj G q adj]
  have thresholds : edgeThresholdDemands G w ⊆ edgeThresholdDemands G q := by
    rintro ⟨s,t⟩ demand
    apply (coe_le_edgeDistance_iff G q s t 1).mpr
    intro p
    apply one_le_clamped_path p
    have old := (coe_le_edgeDistance_iff G w s t 1).mp demand p
    have drop : p.edgeWeight w≤p.edgeWeight keep+(p.edgeLength : ℝ≥0)*d := by
      have point (e : Fin n × Fin n) (he : e ∈ p.edges) : w e≤keep e+d := by
        have same : a e=w e := actualEdgeWeight_of_adj G w (p.edge_adj he)
        unfold keep
        split
        · simpa [same] using ‹a e≤d›
        · simp [same]
      simpa [SimplePath.edgeWeight,Finset.sum_add_distrib] using Finset.sum_le_sum point
    have paths : (p.edgeLength : ℝ≥0)≤n := by
      exact_mod_cast (p.edgeLength_lt_card.le.trans_eq (Fintype.card_fin n))
    have keptEnough : τ≤p.edgeWeight keep := by
      apply tsub_le_iff_right.mpr
      exact old.trans (drop.trans (by gcongr))
    have path_sum : p.edgeWeight raw=p.edgeWeight keep/τ := by
      unfold SimplePath.edgeWeight raw
      exact (Finset.sum_div ..).symm
    rw [path_sum]
    exact (le_div_iff₀ τ_pos).mpr (by simpa using keptEnough)
  have oracle : HasEdgeRoundingFactor G q α := efg_round_atMost hn G q scale_mass
  have small_q : α*smallEdgeMass G q (4*α*(k : ℝ))⁻¹≤1/4 := by rw [← d_expr,no_tiny]; norm_num
  let T := smallMassHorizon n k (totalEdgeWeight G q) α
  obtain ⟨X,valid,marginal⟩ := edge_family_of_small_mass G q α k (Fintype.card_fin n) hn hk apos oracle small_q
  refine ⟨T,smallMassHorizon_mono hn apos.le scale_mass,Nat.zero_lt_succ _,X,?_,?_⟩
  · intro i
    exact ⟨(valid i).1,fun s t d => (valid i).2 s t (thresholds d)⟩
  · intro e
    have upper := NNReal.coe_le_coe.mpr (retained_le e)
    push_cast at upper
    calc
      _ ≤ 8*α*(q e : ℝ) := marginal e
      _ ≤ 8*α*(2*(w e : ℝ)) := mul_le_mul_of_nonneg_left upper (by positivity)
      _ = _ := by ring

theorem vertex_uniform {n : ℕ} (G : Digraph (Fin n)) (w : Fin n → ℝ≥0) :
    let α : ℝ := vfg n (totalWeight w)
    let T := BoundedSampling.horizon (fun e => (w e : ℝ)) α
    ∃ X : Fin T → Finset (Fin n),
      (∀ i, IsIntegralCut G (X i) (thresholdDemands G w)) ∧
      ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ)/(T : ℝ) ≤ 8*α*(w e : ℝ) :=
  vertex_family (vfg_bound n (totalWeight w) G w rfl)

end
end DirectedFlowCutGap.ExactFlowCutGap
