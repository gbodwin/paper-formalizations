import DirectedFlowCutGap.WeakDecompositionWeightBudget

/-! Bound the loss from removing light arcs by the sum of the heaviest
removed outgoing arc at each vertex. A simple path visits each tail once. -/
namespace DirectedFlowCutGap.ExactFlowCutGap

noncomputable section

open scoped NNReal ENNReal BigOperators
open WeakDecomposition
attribute [local instance] Classical.propDecidable

def lightWeight {n : ℕ} (G : Digraph (Fin n)) (w : Fin n × Fin n → ℝ≥0)
    (cutoff : ℝ≥0) (e : Fin n × Fin n) : ℝ≥0 :=
  let actual := actualEdgeWeight G w e
  if actual ≤ cutoff then actual else 0

private def outgoingLightMax {n : ℕ} (G : Digraph (Fin n)) (w : Fin n × Fin n → ℝ≥0)
    (cutoff : ℝ≥0) (u : Fin n) : ℝ≥0 :=
  Finset.univ.sup fun v => lightWeight G w cutoff (u,v)

def outgoingLightLoss {n : ℕ} (G : Digraph (Fin n)) (w : Fin n × Fin n → ℝ≥0) (cutoff : ℝ≥0) : ℝ≥0 :=
  ∑ u : Fin n, outgoingLightMax G w cutoff u

theorem outgoing_light_loss_le {n : ℕ} (G : Digraph (Fin n)) (w : Fin n × Fin n → ℝ≥0) (cutoff : ℝ≥0) :
    outgoingLightLoss G w cutoff ≤ (n : ℝ≥0)*cutoff := by
  have point (u : Fin n) : outgoingLightMax G w cutoff u ≤ cutoff := by
    apply Finset.sup_le
    intro v _
    unfold lightWeight
    dsimp only
    split
    · assumption
    · exact bot_le
  calc
    _ ≤ ∑ _u : Fin n, cutoff := Finset.sum_le_sum fun u _ => point u
    _ = _ := by simp [nsmul_eq_mul]

theorem edge_path_light_loss_le {n : ℕ} {G : Digraph (Fin n)} {s t : Fin n} (p : SimplePath G s t)
    (w : Fin n × Fin n → ℝ≥0) (cutoff : ℝ≥0) :
    p.edgeWeight (lightWeight G w cutoff) ≤ outgoingLightLoss G w cutoff := by
  let tail (i : Fin p.edgeLength) : Fin n := (p.edgeAt i).1
  have distinct : Function.Injective tail := by
    intro i j same
    have sides : i.castSucc=j.castSucc := p.injective same
    exact Fin.ext (congrArg (fun k : Fin (p.edgeLength+1) => k.val) sides)
  rw [p.edgeWeight_eq_sum]
  calc
    _ ≤ ∑ i : Fin p.edgeLength, outgoingLightMax G w cutoff (tail i) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.le_sup (f:=fun v => lightWeight G w cutoff (tail i,v)) (Finset.mem_univ (p.edgeAt i).2)
    _ = ∑ u ∈ Finset.univ.image tail, outgoingLightMax G w cutoff u :=
      (Finset.sum_image (fun i _ j _ h => distinct h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

def originalLightCutoff (n factor : ℕ) : ℝ≥0 := (4*(factor : ℝ≥0)*(n : ℝ≥0))⁻¹

set_option maxHeartbeats 1600000 in
/-- A near-linear family at the exact original gap when the removed mass
and clipping savings cover the rescaling. -/
theorem edge_uniform_of_outgoing_light_budget {n : ℕ} (hn : 0<n) (G : Digraph (Fin n))
    (w : Fin n × Fin n → ℝ≥0) (positive : 0 < efg n (totalEdgeWeight G w))
    (budget :
      let capped e := min 1 (w e)
      let cutoff := originalLightCutoff n (efg n (totalEdgeWeight G w))
      totalEdgeWeight G capped ≤ (1-outgoingLightLoss G capped cutoff)*totalEdgeWeight G w+
        ∑ e, lightWeight G capped cutoff e) :
    let W := totalEdgeWeight G w
    let α : ℝ := efg n W
    ∃ T ≤ smallMassHorizon n n W α, 0<T ∧
      ∃ X : Fin T → Finset (Fin n × Fin n),
        (∀ i, X i ⊆ graphEdges G ∧ IsIntegralEdgeCut G (X i) (edgeThresholdDemands G w)) ∧
        ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ)/(T : ℝ) ≤ 16*α*(w e : ℝ) := by
  classical
  let W := totalEdgeWeight G w
  let factor := efg n W
  let α : ℝ := factor
  let capped (e : Fin n × Fin n) := min 1 (w e)
  let cutoff := originalLightCutoff n factor
  let loss := outgoingLightLoss G capped cutoff
  let scale : ℝ≥0 := 1-loss
  let actual := actualEdgeWeight G capped
  let kept (e : Fin n × Fin n) := if actual e ≤ cutoff then 0 else actual e
  let adjusted (e : Fin n × Fin n) := min 1 (kept e/scale)
  have alpha : (1 : ℝ)≤α := by
    change (1 : ℝ)≤(factor : ℝ)
    exact_mod_cast positive
  have apos := zero_lt_one.trans_le alpha
  have npos : (0 : ℝ)<n := by exact_mod_cast hn
  have n1 : (1 : ℝ)≤n := by exact_mod_cast hn
  have cutoff_real : (cutoff : ℝ)=(4*α*(n : ℝ))⁻¹ := by simp [cutoff,originalLightCutoff,α]
  have mul_cutoff : (n : ℝ)*(cutoff : ℝ)≤1/4 := by
    rw [cutoff_real,← div_eq_mul_inv]
    apply (div_le_iff₀ (by positivity : 0<4*α*(n : ℝ))).mpr
    nlinarith [mul_le_mul_of_nonneg_right alpha npos.le]
  have loss_le : (loss : ℝ) ≤ 1/4 := (NNReal.coe_le_coe.mpr (outgoing_light_loss_le G capped cutoff)).trans
    (by exact_mod_cast mul_cutoff)
  have cutoff_lt : cutoff<1 := by
    apply NNReal.coe_lt_coe.mp
    change (cutoff : ℝ) < 1
    have wide := mul_le_mul_of_nonneg_right n1 cutoff.coe_nonneg
    nlinarith
  have scale_real : (scale : ℝ)=1-(loss : ℝ) := by
    apply NNReal.coe_sub
    apply NNReal.coe_le_coe.mp
    norm_num
    linarith
  have scale_pos : 0<scale := NNReal.coe_pos.mp (by rw [scale_real]; linarith)
  have scale_lower : (1/2 : ℝ) ≤ scale := by rw [scale_real]; linarith
  have scale_le : scale≤1 := tsub_le_self
  have split (e : Fin n × Fin n) : kept e+lightWeight G capped cutoff e=actual e := by
    by_cases light : actual e≤cutoff <;> simp [kept,lightWeight,actual,light]
  have mass_split : (∑ e, kept e)+(∑ e, lightWeight G capped cutoff e)=totalEdgeWeight G capped := by
    rw [← Finset.sum_add_distrib,Finset.sum_congr rfl (fun e _ => split e)]
    exact_mod_cast sum_actualEdgeWeight G capped
  have stored : (∑ e, kept e) ≤ W*scale := by
    have within := mass_split.trans_le budget
    change (∑ e, kept e)+(∑ e, lightWeight G capped cutoff e) ≤
      scale*W+(∑ e, lightWeight G capped cutoff e) at within
    exact (le_of_add_le_add_right within).trans_eq (mul_comm scale W)
  have mass : totalEdgeWeight G adjusted≤W := by
    calc
      _≤∑ e, adjusted e := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _≤∑ e, kept e/scale := Finset.sum_le_sum fun _ _ => min_le_right ..
      _=(∑ e, kept e)/scale := (Finset.sum_div ..).symm
      _≤W := (div_le_iff₀ scale_pos).mpr stored
  have weight_bound (e : Fin n × Fin n) : adjusted e≤2*w e := by
    have keep_le : kept e≤w e := by
      have within : actual e≤w e := by unfold actual actualEdgeWeight capped; split <;> simp
      unfold kept
      split
      · exact bot_le
      · exact within
    refine (min_le_right ..).trans ((div_le_iff₀ scale_pos).mpr (keep_le.trans ?_))
    apply NNReal.coe_le_coe.mp
    push_cast
    nlinarith [(w e).coe_nonneg]
  have thresholds : edgeThresholdDemands G w ⊆ edgeThresholdDemands G adjusted := by
    rintro ⟨s,t⟩ connected
    apply (coe_le_edgeDistance_iff G adjusted s t 1).mpr
    intro p
    apply one_le_clamped_path
    have order : 1≤p.edgeWeight capped :=
      one_le_clamped_path p w ((coe_le_edgeDistance_iff G w s t 1).mp connected p)
    have separated : p.edgeWeight capped=p.edgeWeight kept+p.edgeWeight (lightWeight G capped cutoff) := by
      unfold SimplePath.edgeWeight
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e member
      rw [split]
      exact (actualEdgeWeight_of_adj G capped (p.edge_adj member)).symm
    have left := edge_path_light_loss_le p capped cutoff
    have enough : scale≤p.edgeWeight kept := by
      apply tsub_le_iff_right.mpr
      exact order.trans (separated.trans_le (add_le_add_right left _))
    have scaled : p.edgeWeight (fun e => kept e/scale)=p.edgeWeight kept/scale := (Finset.sum_div ..).symm
    rw [scaled]
    exact (le_div_iff₀ scale_pos).mpr (by simpa using enough)
  have no_light : smallEdgeMass G adjusted (cutoff : ℝ)=0 := by
    unfold smallEdgeMass
    apply Finset.sum_eq_zero
    intro e member
    by_cases edge : G.Adj e.1 e.2
    · have displayed := (Finset.mem_filter.mp member).2
      rw [actualEdgeWeight_of_adj G adjusted edge] at displayed ⊢
      by_cases light : actual e≤cutoff
      · simp [adjusted,kept,light]
      · have retained : actual e≤kept e/scale := (le_div_iff₀ scale_pos).mpr
          (by simpa [kept,light] using mul_le_mul_of_nonneg_left scale_le (show 0≤actual e from zero_le))
        exact (not_lt_of_ge (NNReal.coe_le_coe.mp displayed)
          (lt_min cutoff_lt ((lt_of_not_ge light).trans_le retained))).elim
    · simp [actualEdgeWeight_of_not_adj G adjusted edge]
  have oracle : HasEdgeRoundingFactor G adjusted α := efg_round_atMost hn G adjusted mass
  have small : α*smallEdgeMass G adjusted (4*α*(n : ℝ))⁻¹≤1/4 := by
    rw [← cutoff_real,no_light]
    norm_num
  obtain ⟨X,valid,probability⟩ := edge_family_of_small_mass G adjusted α n (Fintype.card_fin n) hn hn apos oracle small
  refine ⟨smallMassHorizon n n (totalEdgeWeight G adjusted) α,smallMassHorizon_mono hn apos.le mass,
    Nat.zero_lt_succ _,X,?_,?_⟩
  · intro i
    exact ⟨(valid i).1,fun s t d => (valid i).2 s t (thresholds d)⟩
  · intro e
    have compare := NNReal.coe_le_coe.mpr (weight_bound e)
    push_cast at compare
    calc
      _ ≤ 8*α*(adjusted e : ℝ) := probability e
      _ ≤ 8*α*(2*(w e : ℝ)) := mul_le_mul_of_nonneg_left compare (by positivity)
      _ = _ := by ring

end

end DirectedFlowCutGap.ExactFlowCutGap
