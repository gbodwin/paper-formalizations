import DirectedFlowCutGap.EdgeRounding
import DirectedFlowCutGap.LevelCutProbability
import Mathlib.MeasureTheory.Integral.Average

namespace DirectedFlowCutGap.TwoSideEdgeFactor

noncomputable section

open MeasureTheory Set
open scoped BigOperators NNReal ENNReal

variable {V : Type*}

private def hit (w : V × V → ℝ≥0) (side : V × V → Bool) (e : V × V) : Set ℝ :=
  if side e then Ici (1-(w e : ℝ)) else Iic (w e : ℝ)

private theorem hit_measurable (w : V × V → ℝ≥0) (side : V × V → Bool) (e : V × V) :
    MeasurableSet (hit w side e) := by
  unfold hit
  split <;> first | exact measurableSet_Ici | exact measurableSet_Iic

private theorem hit_mass (w : V × V → ℝ≥0) (side : V × V → Bool) (e : V × V) :
    uniformLevel (hit w side e) ≤ (w e : ℝ≥0∞) := by
  rw [uniformLevel, Measure.restrict_apply (hit_measurable w side e)]
  unfold hit
  split
  · calc
      _ ≤ volume (Icc (1-(w e : ℝ)) 1) := measure_mono fun _ h => ⟨h.1,h.2.2⟩
      _ = _ := by rw [Real.volume_Icc,sub_sub_cancel,ENNReal.ofReal_coe_nnreal]
  · calc
      _ ≤ volume (Icc 0 (w e : ℝ)) := measure_mono fun _ h => ⟨h.2.1,h.1⟩
      _ = _ := by rw [Real.volume_Icc,sub_zero,ENNReal.ofReal_coe_nnreal]

variable [Fintype V] [DecidableEq V]

def levelCut (G : Digraph V) (w : V × V → ℝ≥0) (side : V × V → Bool) (d : ℝ) :
    Finset (V × V) := by
  classical
  exact (graphEdges G).filter fun e => d ∈ hit w side e

omit [DecidableEq V] in
theorem mem_levelCut (G : Digraph V) (w : V × V → ℝ≥0) (side : V × V → Bool)
    (d : ℝ) (e : V × V) :
    e ∈ levelCut G w side d ↔ e ∈ graphEdges G ∧
      (if side e then 1-(w e : ℝ) ≤ d else d ≤ (w e : ℝ)) := by
  classical
  rw [levelCut,Finset.mem_filter]
  apply and_congr_right
  intro _
  cases shade : side e <;> simp [hit,shade]

omit [DecidableEq V] in
theorem levelCut_actual (G : Digraph V) (w : V × V → ℝ≥0)
    (side : V × V → Bool) (d : ℝ) : levelCut G w side d ⊆ graphEdges G := by
  classical
  exact Finset.filter_subset _ _

theorem levelCut_valid (G : Digraph V) (w : V × V → ℝ≥0) (side : V × V → Bool)
    (separate : ∀ {s t : V} (p : SimplePath G s t),
      Set.InjOn side (↑(p.edges.filter fun e => 0 < w e) : Set (V × V)))
    {d : ℝ} (range : d ∈ Icc (0 : ℝ) 1) :
    IsIntegralEdgeCut G (levelCut G w side d) (edgeThresholdDemands G w) := by
  classical
  intro s t far p
  by_contra missed
  let paid := p.edges.filter fun e => 0 < w e
  let group (b : Bool) := paid.filter fun e => side e = b
  let mass (b : Bool) : ℝ := ∑ e ∈ group b, (w e : ℝ)
  let budget (b : Bool) : ℝ := if b then 1-d else d
  have pathMass : (1 : ℝ) ≤ ∑ e ∈ paid, (w e : ℝ) := by
    have h := (coe_le_edgeDistance_iff G w s t 1).mp far p
    have equal : (∑ e ∈ paid, w e) = p.edgeWeight w := by
      unfold SimplePath.edgeWeight
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro e inside outside
      by_contra pos
      exact outside (Finset.mem_filter.mpr ⟨inside,pos_iff_ne_zero.mpr pos⟩)
    rw [← equal] at h
    exact_mod_cast h
  have splitMass : (∑ e ∈ paid, (w e : ℝ)) = mass false+mass true := by
    unfold mass group
    rw [Finset.sum_filter (s := paid) (fun e => side e = false),
      Finset.sum_filter (s := paid) (fun e => side e = true), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    cases side e <;> simp
  rw [splitMass] at pathMass
  have small (b : Bool) {e : V × V} (member : e ∈ group b) : (w e : ℝ) < budget b := by
    obtain ⟨paidMem,which⟩ := Finset.mem_filter.mp member
    have onPath := (Finset.mem_filter.mp paidMem).1
    have outside : d ∉ hit w side e := by
      intro hd
      apply missed
      exact ⟨e,onPath,Finset.mem_filter.mpr ⟨p.edges_subset_graphEdges onPath,hd⟩⟩
    rw [hit,which] at outside
    cases b
    · simpa [budget] using (lt_of_not_ge (show ¬ d ≤ (w e : ℝ) from outside))
    · have : d < 1-(w e : ℝ) := lt_of_not_ge (show ¬ 1-(w e : ℝ) ≤ d from outside)
      dsimp [budget]
      linarith
  have parts (b : Bool) : mass b ≤ budget b ∧ ((group b).Nonempty → mass b < budget b) := by
    by_cases present : (group b).Nonempty
    · obtain ⟨e,member⟩ := present
      have alone : group b = {e} := Finset.eq_singleton_iff_unique_mem.mpr ⟨member,fun f hf => by
        obtain ⟨fPaid,fSide⟩ := Finset.mem_filter.mp hf
        obtain ⟨ePaid,eSide⟩ := Finset.mem_filter.mp member
        exact separate p fPaid ePaid (fSide.trans eSide.symm)⟩
      have strict : mass b < budget b := by simpa [mass,alone] using small b member
      exact ⟨strict.le,fun _ => strict⟩
    · have empty : mass b = 0 := by simp [mass,Finset.not_nonempty_iff_eq_empty.mp present]
      refine ⟨?_,fun h => (present h).elim⟩
      rw [empty]
      cases b
      · exact range.1
      · exact sub_nonneg.mpr range.2
  by_cases left : (group false).Nonempty
  · have l : mass false < d := (parts false).2 left
    have r : mass true ≤ 1-d := (parts true).1
    linarith only [l,r,pathMass]
  · have zeroLeft : mass false = 0 := by simp [mass,Finset.not_nonempty_iff_eq_empty.mp left]
    have right : (group true).Nonempty := by
      by_contra empty
      have zeroRight : mass true = 0 := by simp [mass,Finset.not_nonempty_iff_eq_empty.mp empty]
      linarith only [zeroLeft,zeroRight,pathMass]
    have r : mass true < 1-d := (parts true).2 right
    linarith only [r,zeroLeft,pathMass,range.1]

omit [DecidableEq V] in
private theorem cut_fee (G : Digraph V) (w c : V × V → ℝ≥0) (side : V × V → Bool) (d : ℝ) :
    (edgeCutCost G c (levelCut G w side d) : ℝ≥0∞) =
      ∑ e ∈ graphEdges G, (hit w side e).indicator (fun _ => (c e : ℝ≥0∞)) d := by
  classical
  rw [edgeCutCost_eq_sum_of_subset G c (levelCut_actual G w side d), ENNReal.ofNNReal_finsetSum,
      levelCut, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  simp [Set.indicator_apply]

omit [DecidableEq V] in
set_option maxHeartbeats 700000 in
/-- Some unit-interval level reaches the weighted cost bound. -/
theorem exists_level_cost (G : Digraph V) (w c : V × V → ℝ≥0) (side : V × V → Bool) :
    ∃ d ∈ Icc (0 : ℝ) 1, (edgeCutCost G c (levelCut G w side d) : ℝ) ≤ weightedEdgeCost G c w := by
  let cENN (d : ℝ) := (edgeCutCost G c (levelCut G w side d) : ℝ≥0∞)
  let cReal (d : ℝ) := (edgeCutCost G c (levelCut G w side d) : ℝ)
  have measurable : Measurable cENN := by
    unfold cENN
    simp_rw [cut_fee]
    exact Finset.measurable_sum _ (fun e _ => measurable_const.indicator (hit_measurable w side e))
  have mean : (∫⁻ d, cENN d ∂uniformLevel) ≤ (weightedEdgeCost G c w : ℝ≥0∞) := by
    unfold cENN
    simp_rw [cut_fee]
    rw [lintegral_finsetSum _ (fun e _ => measurable_const.indicator (hit_measurable w side e)),
      weightedEdgeCost,ENNReal.ofNNReal_finsetSum]
    apply Finset.sum_le_sum
    intro e _
    rw [lintegral_indicator_const (hit_measurable w side e),ENNReal.coe_mul]
    gcongr
    exact hit_mass w side e
  have cInt : Integrable cReal uniformLevel := by
    simpa only [cReal,cENN,ENNReal.coe_toReal] using
      integrable_toReal_of_lintegral_ne_top measurable.aemeasurable
        ((mean.trans_lt ENNReal.coe_lt_top).ne)
  have meanReal : (∫ d, cReal d ∂uniformLevel) ≤ (weightedEdgeCost G c w : ℝ) :=
    (lintegral_coe_le_coe_iff_integral_le cInt).mp mean
  have outside : uniformLevel (Icc (0 : ℝ) 1)ᶜ = 0 := by
    rw [uniformLevel, Measure.restrict_apply measurableSet_Icc.compl]
    simp
  obtain ⟨d,hd,within⟩ := exists_notMem_null_le_average (IsProbabilityMeasure.ne_zero uniformLevel) cInt outside
  rw [average_eq_integral] at within
  exact ⟨d,by simpa using hd,within.trans meanReal⟩

/-- A two-part partition of the positive arcs that puts distinct arcs of
each simple path on different sides yields a factor-one rounding oracle. -/
theorem factor_one (G : Digraph V) (w : V × V → ℝ≥0) (side : V × V → Bool)
    (separate : ∀ {s t : V} (p : SimplePath G s t),
      Set.InjOn side (↑(p.edges.filter fun e => 0 < w e) : Set (V × V))) :
    HasEdgeRoundingFactor G w 1 := by
  refine ⟨zero_le_one,fun c => ?_⟩
  obtain ⟨d,hd,paid⟩ := exists_level_cost G w c side
  exact ⟨levelCut G w side d,levelCut_actual G w side d,levelCut_valid G w side separate hd,
    by simpa only [one_mul] using paid⟩

end
end DirectedFlowCutGap.TwoSideEdgeFactor
