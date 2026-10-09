import DirectedFlowCutGap.LevelCut

/-!
# Uniform level probabilities and single-round expectations

The sampling measure is actual Lebesgue measure restricted to the real interval
`[0,1]`, whose mass is proved to be one. The sampled nonnegative level is
`Real.toNNReal`; it equals the real sample on this support. All marginal and
expectation formulas below are derived from interval volume and integration of
finite indicator sums, with the actual `levelCut` as the selected set.

This supplies the single-round ingredient of Lemma 14 and the interval event
used to define `val_{s,t}(u,v)` before Lemma 16 of arXiv:2604.03412v3. It does
not assume or assert independence, stopped-epoch estimates, or running time.
-/

namespace DirectedFlowCutGap

noncomputable section

open MeasureTheory Set
open scoped BigOperators NNReal ENNReal

/-- Uniform sampling from `[0,1]`: no normalization is needed because its
Lebesgue measure is exactly one. -/
def uniformLevel : Measure ℝ := volume.restrict (Icc 0 1)

instance uniformLevel_isProbabilityMeasure : IsProbabilityMeasure uniformLevel := by
  constructor
  simp [uniformLevel, Real.volume_Icc]

/-- Every individual level, including both boundary levels, has probability zero. -/
@[simp] theorem uniformLevel_singleton (d : ℝ) : uniformLevel {d} = 0 := by
  change (volume.restrict (Icc (0 : ℝ) 1)) {d} = 0
  exact measure_singleton d

/-- An extended-distance interval tested against the actual finite level. -/
def levelIntervalEvent (a b : ℝ≥0∞) : Set ℝ :=
  {d | a ≤ (d.toNNReal : ℝ≥0∞) ∧ (d.toNNReal : ℝ≥0∞) ≤ b}

theorem measurableSet_levelIntervalEvent (a b : ℝ≥0∞) :
    MeasurableSet (levelIntervalEvent a b) := by
  exact (measurableSet_le measurable_const
    measurable_real_toNNReal.coe_nnreal_ennreal).inter
      (measurableSet_le measurable_real_toNNReal.coe_nnreal_ennreal measurable_const)

/-- On the support of the sampling measure, finite endpoints give an ordinary
real interval, clipped at the top of the sampling interval. -/
theorem levelIntervalEvent_coe_inter_unit (a b : ℝ≥0) :
    levelIntervalEvent a b ∩ Icc (0 : ℝ) 1 = Icc (a : ℝ) (min 1 (b : ℝ)) := by
  ext d
  simp only [levelIntervalEvent, mem_inter_iff, mem_ofPred_eq, mem_Icc,
    ENNReal.coe_le_coe]
  constructor
  · rintro ⟨⟨ha, hb⟩, hd0, hd1⟩
    have ha' : (a : ℝ) ≤ d := by
      simpa only [Real.coe_toNNReal d hd0] using (show (a : ℝ) ≤ d.toNNReal from ha)
    have hb' : d ≤ (b : ℝ) := by
      simpa only [Real.coe_toNNReal d hd0] using (show (d.toNNReal : ℝ) ≤ b from hb)
    exact ⟨ha', le_min hd1 hb'⟩
  · rintro ⟨ha, hb⟩
    have hd0 : 0 ≤ d := a.property.trans ha
    have ha' : a ≤ d.toNNReal := by
      exact_mod_cast (show (a : ℝ) ≤ (d.toNNReal : ℝ) by simpa [Real.coe_toNNReal d hd0] using ha)
    have hb' : d.toNNReal ≤ b := by
      exact_mod_cast (show (d.toNNReal : ℝ) ≤ (b : ℝ) by
        simpa [Real.coe_toNNReal d hd0] using (le_min_iff.mp hb).2)
    exact ⟨⟨ha', hb'⟩, hd0, (le_min_iff.mp hb).1⟩

/-- Exact clipped interval probability for finite nonnegative endpoints.
Reversed intervals have probability zero by truncated subtraction. -/
theorem uniformLevel_interval_coe (a b : ℝ≥0) :
    uniformLevel (levelIntervalEvent a b) = ((min 1 b - a : ℝ≥0) : ℝ≥0∞) := by
  rw [uniformLevel, Measure.restrict_apply (measurableSet_levelIntervalEvent _ _),
    levelIntervalEvent_coe_inter_unit, Real.volume_Icc,
    ENNReal.ofReal_sub (min 1 (b : ℝ)) (q := (a : ℝ)) a.property]
  simp only [ENNReal.coe_sub, ENNReal.coe_min, ENNReal.coe_one,
    ENNReal.ofReal_min, ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal]

/-- Clipping the upper extended endpoint at one does not change the event on
the sampling support, including when that endpoint is infinity. -/
theorem levelIntervalEvent_inter_unit_clip (a b : ℝ≥0∞) :
    levelIntervalEvent a b ∩ Icc (0 : ℝ) 1 =
      levelIntervalEvent a (min 1 b) ∩ Icc (0 : ℝ) 1 := by
  ext d
  simp only [levelIntervalEvent, mem_inter_iff, mem_ofPred_eq, mem_Icc, le_min_iff]
  constructor
  · rintro ⟨⟨ha, hb⟩, hd0, hd1⟩
    have hd : (d.toNNReal : ℝ≥0∞) ≤ 1 := by
      exact_mod_cast (show d.toNNReal ≤ (1 : ℝ≥0) by
        exact_mod_cast (show (d.toNNReal : ℝ) ≤ 1 by simpa [Real.coe_toNNReal d hd0] using hd1))
    exact ⟨⟨ha, hd, hb⟩, hd0, hd1⟩
  · tauto

/-- The exact interval probability remains valid for extended distances.
In particular an infinite lower endpoint contributes zero. -/
theorem uniformLevel_interval (a b : ℝ≥0∞) :
    uniformLevel (levelIntervalEvent a b) = min 1 b - a := by
  by_cases ha : a = ⊤
  · subst a
    simp [levelIntervalEvent]
  · have hb : min 1 b ≠ ⊤ := ne_of_lt ((min_le_left 1 b).trans_lt ENNReal.one_lt_top)
    have hclip : uniformLevel (levelIntervalEvent a b) =
        uniformLevel (levelIntervalEvent a (min 1 b)) := by
      simp only [uniformLevel,
        Measure.restrict_apply (measurableSet_levelIntervalEvent _ _)]
      rw [levelIntervalEvent_inter_unit_clip]
    rw [hclip, ← ENNReal.coe_toNNReal ha, ← ENNReal.coe_toNNReal hb,
      uniformLevel_interval_coe]
    rw [ENNReal.coe_sub, ENNReal.coe_min, ENNReal.coe_one,
      ENNReal.coe_toNNReal ha, ENNReal.coe_toNNReal hb, min_eq_right (min_le_left 1 b)]

/-- Symmetric clipping gives the distance difference used as the paper's
single-pair separation value. -/
theorem uniformLevel_interval_clipped (a b : ℝ≥0∞) :
    uniformLevel (levelIntervalEvent a b) = min 1 b - min 1 a := by
  rw [uniformLevel_interval]
  by_cases ha : a ≤ 1
  · rw [min_eq_right ha]
  · have h1a : 1 ≤ a := le_of_not_ge ha
    rw [min_eq_left h1a, tsub_eq_zero_of_le ((min_le_left 1 b).trans h1a),
      tsub_eq_zero_of_le (min_le_left 1 b)]

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The measurable event that the actual level cut selects a given vertex. -/
def levelHitEvent (G : Digraph V) (w : V → ℝ≥0) (s v : V) : Set ℝ :=
  {d | v ∈ levelCut G w s d.toNNReal}

theorem levelHitEvent_eq_interval (G : Digraph V) (w : V → ℝ≥0) (s v : V) :
    levelHitEvent G w s v = levelIntervalEvent (vertexDistance G w s v)
      (vertexDistance G w s v + (w v : ℝ≥0∞)) := by
  ext d
  exact mem_levelCut G w s v d.toNNReal

theorem measurableSet_levelHitEvent (G : Digraph V) (w : V → ℝ≥0) (s v : V) :
    MeasurableSet (levelHitEvent G w s v) := by
  rw [levelHitEvent_eq_interval]
  exact measurableSet_levelIntervalEvent _ _

/-- Exact probability of selection, including zero for unreachable vertices. -/
theorem uniformLevel_levelHitEvent (G : Digraph V) (w : V → ℝ≥0) (s v : V) :
    uniformLevel (levelHitEvent G w s v) = (levelCutIntervalLength G w s v : ℝ≥0∞) := by
  by_cases h : vertexDistance G w s v = ⊤
  · simp [levelHitEvent_eq_interval, uniformLevel_interval, levelCutIntervalLength, h]
  · rw [levelHitEvent_eq_interval, ← ENNReal.coe_toNNReal h, ← ENNReal.coe_add,
      uniformLevel_interval_coe]
    simp [levelCutIntervalLength, h]

theorem uniformLevel_levelHitEvent_of_distance_top (G : Digraph V) (w : V → ℝ≥0)
    (s v : V) (h : vertexDistance G w s v = ⊤) :
    uniformLevel (levelHitEvent G w s v) = 0 := by
  simp [uniformLevel_levelHitEvent, levelCutIntervalLength, h]

/-- The single-vertex marginal bound needed by Lemma 14. -/
theorem uniformLevel_levelHitEvent_le_weight (G : Digraph V) (w : V → ℝ≥0)
    (s v : V) : uniformLevel (levelHitEvent G w s v) ≤ (w v : ℝ≥0∞) := by
  rw [uniformLevel_levelHitEvent]
  exact ENNReal.coe_le_coe.mpr (levelCutIntervalLength_le_weight G w s v)

/-- Pointwise indicator expansion of the cost of the genuinely new vertices.
No probabilistic or expectation identity is assumed. -/
theorem newLevelCut_cost_indicator_sum (G : Digraph V) (w cost : V → ℝ≥0)
    (s : V) (X : Finset V) (d : ℝ) :
    (cutCost cost (levelCut G w s d.toNNReal \ X) : ℝ≥0∞) =
      ∑ v ∈ Finset.univ \ X,
        (levelHitEvent G w s v).indicator (fun _ => (cost v : ℝ≥0∞)) d := by
  classical
  rw [cutCost, ENNReal.ofNNReal_finsetSum]
  have hset : levelCut G w s d.toNNReal \ X =
      (Finset.univ \ X).filter (fun v => v ∈ levelCut G w s d.toNNReal) := by
    ext v
    simp [and_comm]
  rw [hset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  simp [levelHitEvent, Set.indicator_apply]

theorem measurable_newLevelCut_cost (G : Digraph V) (w cost : V → ℝ≥0)
    (s : V) (X : Finset V) :
    Measurable (fun d : ℝ => (cutCost cost (levelCut G w s d.toNNReal \ X) : ℝ≥0∞)) := by
  simp_rw [newLevelCut_cost_indicator_sum]
  exact Finset.measurable_sum _ (fun v _ =>
    measurable_const.indicator (measurableSet_levelHitEvent G w s v))

/-- Exact expectation of the newly selected cost as a finite sum of marginal
probabilities, proved by integrating the actual cut's indicator expansion. -/
theorem lintegral_newLevelCut_cost (G : Digraph V) (w cost : V → ℝ≥0)
    (s : V) (X : Finset V) :
    (∫⁻ d, (cutCost cost (levelCut G w s d.toNNReal \ X) : ℝ≥0∞) ∂uniformLevel) =
      ∑ v ∈ Finset.univ \ X,
        (cost v : ℝ≥0∞) * (levelCutIntervalLength G w s v : ℝ≥0∞) := by
  simp_rw [newLevelCut_cost_indicator_sum]
  rw [lintegral_finsetSum _ (fun v _ =>
    measurable_const.indicator (measurableSet_levelHitEvent G w s v))]
  apply Finset.sum_congr rfl
  intro v hv
  rw [lintegral_indicator_const (measurableSet_levelHitEvent G w s v),
    uniformLevel_levelHitEvent]

/-- Single-round weighted expectation bound, for any previously accumulated
cut `X`; only vertices outside `X` are charged. -/
theorem lintegral_newLevelCut_cost_le (G : Digraph V) (w cost : V → ℝ≥0)
    (s : V) (X : Finset V) :
    (∫⁻ d, (cutCost cost (levelCut G w s d.toNNReal \ X) : ℝ≥0∞) ∂uniformLevel) ≤
      ∑ v ∈ Finset.univ \ X, ((cost v * w v : ℝ≥0) : ℝ≥0∞) := by
  rw [lintegral_newLevelCut_cost]
  apply Finset.sum_le_sum
  intro v hv
  rw [ENNReal.coe_mul]
  gcongr
  exact levelCutIntervalLength_le_weight G w s v

/-- Lemma 14's single-round expected number of new vertices. -/
theorem lintegral_newLevelCut_card_le (G : Digraph V) (w : V → ℝ≥0)
    (s : V) (X : Finset V) :
    (∫⁻ d, ((levelCut G w s d.toNNReal \ X).card : ℝ≥0∞) ∂uniformLevel) ≤
      ∑ v ∈ Finset.univ \ X, (w v : ℝ≥0∞) := by
  simpa using lintegral_newLevelCut_cost_le G w (fun _ => 1) s X

/-- The nonnegative single-round cost has a finite expectation. -/
theorem integrable_newLevelCut_cost (G : Digraph V) (w cost : V → ℝ≥0)
    (s : V) (X : Finset V) :
    Integrable (fun d : ℝ => (cutCost cost (levelCut G w s d.toNNReal \ X) : ℝ))
      uniformLevel := by
  have hfinite : (∫⁻ d, (cutCost cost (levelCut G w s d.toNNReal \ X) : ℝ≥0∞)
      ∂uniformLevel) ≠ ⊤ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (lintegral_newLevelCut_cost_le G w cost s X)
    exact ENNReal.sum_lt_top.mpr (fun v _ => ENNReal.coe_lt_top)
  simpa only [ENNReal.coe_toReal] using
    integrable_toReal_of_lintegral_ne_top (measurable_newLevelCut_cost G w cost s X).aemeasurable hfinite

/-- The usual real-valued expectation form of the weighted bound. -/
theorem integral_newLevelCut_cost_le (G : Digraph V) (w cost : V → ℝ≥0)
    (s : V) (X : Finset V) :
    (∫ d, (cutCost cost (levelCut G w s d.toNNReal \ X) : ℝ) ∂uniformLevel) ≤
      ((∑ v ∈ Finset.univ \ X, cost v * w v : ℝ≥0) : ℝ) := by
  apply (lintegral_coe_le_coe_iff_integral_le
    (integrable_newLevelCut_cost G w cost s X)).mp
  simpa only [ENNReal.ofNNReal_finsetSum] using lintegral_newLevelCut_cost_le G w cost s X

/-- Lemma 14's single-round bound stated as an ordinary real expectation. -/
theorem integral_newLevelCut_card_le (G : Digraph V) (w : V → ℝ≥0)
    (s : V) (X : Finset V) :
    (∫ d, ((levelCut G w s d.toNNReal \ X).card : ℝ) ∂uniformLevel) ≤
      ((∑ v ∈ Finset.univ \ X, w v : ℝ≥0) : ℝ) := by
  simpa using integral_newLevelCut_cost_le G w (fun _ => 1) s X

/-- The paper's closed separation interval, using genuine extended distances. -/
def levelSeparationEvent (G : Digraph V) (w : V → ℝ≥0) (s u v : V) : Set ℝ :=
  levelIntervalEvent (vertexDistance G w s u) (vertexDistance G w s v)

/-- The distance-difference representation of `val_{s,t}(u,v)` for fixed
source `s` and the fixed weights belonging to demand `(s,t)`. -/
def levelSeparationValue (G : Digraph V) (w : V → ℝ≥0) (s u v : V) : ℝ≥0∞ :=
  min 1 (vertexDistance G w s v) - min 1 (vertexDistance G w s u)

omit [Fintype V] in
theorem measurableSet_levelSeparationEvent (G : Digraph V) (w : V → ℝ≥0)
    (s u v : V) : MeasurableSet (levelSeparationEvent G w s u v) :=
  measurableSet_levelIntervalEvent _ _

omit [Fintype V] in
/-- Exact probability, rather than an assumed hazard parameter. -/
theorem uniformLevel_levelSeparationEvent (G : Digraph V) (w : V → ℝ≥0)
    (s u v : V) :
    uniformLevel (levelSeparationEvent G w s u v) = levelSeparationValue G w s u v :=
  uniformLevel_interval_clipped _ _

omit [Fintype V] in
theorem levelSeparationValue_le_one (G : Digraph V) (w : V → ℝ≥0) (s u v : V) :
    levelSeparationValue G w s u v ≤ 1 :=
  tsub_le_self.trans (min_le_left _ _)

/-- Existence of an actual directed simple path surviving full deletion of
`X`. Both endpoints, as well as all internal vertices, must survive. -/
def LevelResidualPath (G : Digraph V) (X : Finset V) (u v : V) : Prop :=
  ∃ p : SimplePath G u v, ∀ z ∈ p.vertices, z ∉ X

/-- Any property of the finite sampled cut is measurable. This avoids assuming
that an arbitrary existential quantification over paths preserves measurability. -/
theorem measurableSet_levelCut_property (G : Digraph V) (w : V → ℝ≥0)
    (s : V) (P : Finset V → Prop) :
    MeasurableSet {d : ℝ | P (levelCut G w s d.toNNReal)} := by
  classical
  have hfiber (Y : Finset V) : MeasurableSet {d : ℝ | levelCut G w s d.toNNReal = Y} := by
    have hset : {d : ℝ | levelCut G w s d.toNNReal = Y} =
        ⋂ v : V, {d : ℝ | v ∈ levelCut G w s d.toNNReal ↔ v ∈ Y} := by
      ext d
      simp only [mem_ofPred_eq, mem_iInter, Finset.ext_iff]
    rw [hset]
    exact MeasurableSet.iInter fun v =>
      (measurableSet_levelHitEvent G w s v).iff (MeasurableSet.const _)
  have hset : {d : ℝ | P (levelCut G w s d.toNNReal)} =
      ⋃ Y : Finset V, {d : ℝ | levelCut G w s d.toNNReal = Y} ∩ {d : ℝ | P Y} := by
    ext d
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro hd
      exact ⟨_, rfl, hd⟩
    · rintro ⟨Y, hY, hP⟩
      simpa [hY] using hP
  rw [hset]
  exact MeasurableSet.iUnion fun Y => (hfiber Y).inter (MeasurableSet.const _)

theorem measurableSet_levelResidualPath (G : Digraph V) (w : V → ℝ≥0)
    (s u v : V) (X : Finset V) :
    MeasurableSet {d : ℝ | LevelResidualPath G (X ∪ levelCut G w s d.toNNReal) u v} :=
  measurableSet_levelCut_property G w s (fun Y => LevelResidualPath G (X ∪ Y) u v)

/-- Every level in the closed separation event kills the residual path.
At the upper endpoint, `v` itself is selected. Strict-upper levels use the
proved adjacent-crossing geometry of `levelCut_source_or_cutsPair`. -/
theorem levelSeparationEvent_no_residualPath (G : Digraph V) (w : V → ℝ≥0)
    (s u v : V) (X : Finset V) {d : ℝ}
    (hd : d ∈ levelSeparationEvent G w s u v) :
    ¬LevelResidualPath G (X ∪ levelCut G w s d.toNNReal) u v := by
  rcases hd with ⟨hu, hv⟩
  rintro ⟨p, hp⟩
  by_cases hlt : (d.toNNReal : ℝ≥0∞) < vertexDistance G w s v
  · rcases levelCut_source_or_cutsPair G w s d.toNNReal hu hlt with hsource | hcut
    · exact hp u p.source_mem_vertices (Finset.mem_union_right _ hsource)
    · obtain ⟨z, hz, hselect⟩ := hcut p
      have hz' : z ∈ p.vertices := (Finset.mem_sdiff.mp hz).1
      exact hp z hz' (Finset.mem_union_right _ hselect)
  · have heq : (d.toNNReal : ℝ≥0∞) = vertexDistance G w s v := le_antisymm hv (le_of_not_gt hlt)
    have hselect : v ∈ levelCut G w s d.toNNReal := by
      rw [mem_levelCut, heq]
      exact ⟨le_rfl, le_self_add⟩
    exact hp v p.target_mem_vertices (Finset.mem_union_right _ hselect)

/-- A direct probabilistic geometric bound: the probability of residual
connectivity after this actual round is at most one minus the separation value. -/
theorem uniformLevel_residualPath_le (G : Digraph V) (w : V → ℝ≥0)
    (s u v : V) (X : Finset V) :
    uniformLevel {d | LevelResidualPath G (X ∪ levelCut G w s d.toNNReal) u v} ≤
      1 - levelSeparationValue G w s u v := by
  calc
    _ ≤ uniformLevel (levelSeparationEvent G w s u v)ᶜ := by
      apply measure_mono
      intro d hd hsep
      exact levelSeparationEvent_no_residualPath G w s u v X hsep hd
    _ = _ := by
      rw [measure_compl (measurableSet_levelSeparationEvent G w s u v)
        (measure_ne_top _ _), measure_univ, uniformLevel_levelSeparationEvent]

end

end DirectedFlowCutGap
