import DirectedFlowCutGap.LevelCutProbability
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# The actual finite law of a sampled level cut

Push forward the proved uniform-level measure to finite cut outcomes, then use
its exact PMF. This is a bridge for finite adaptive composition, not an assumed
cut oracle or a proof of the complete adaptive algorithm.
-/
namespace DirectedFlowCutGap.FiniteCutLaw
noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal ENNReal Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A distinct outcome type gives finite cut sets their discrete sigma algebra. -/
@[ext] structure Outcome (V : Type*) where
  cut : Finset V
  deriving DecidableEq, Fintype

instance : MeasurableSpace (Outcome V) := ⊤
instance : MeasurableSingletonClass (Outcome V) := ⟨fun _ => trivial⟩

/-- Actual level-cut outcome, with the same finite-level convention as the paper. -/
def draw (G : Digraph V) (w : V → ℝ≥0) (s : V) (d : ℝ) : Outcome V :=
  ⟨levelCut G w s d.toNNReal⟩

theorem measurable_draw (G : Digraph V) (w : V → ℝ≥0) (s : V) :
    Measurable (draw G w s) := by
  intro A hA
  exact measurableSet_levelCut_property G w s (fun X => (⟨X⟩ : Outcome V) ∈ A)

/-- A real measure pushforward, not arbitrary nonnegative weights. -/
def cutMeasure (G : Digraph V) (w : V → ℝ≥0) (s : V) : Measure (Outcome V) :=
  uniformLevel.map (draw G w s)

instance cutMeasure_probability (G : Digraph V) (w : V → ℝ≥0) (s : V) :
    IsProbabilityMeasure (cutMeasure G w s) := by
  unfold cutMeasure
  infer_instance

/-- The finite probability mass function of the actual uniform-level cut. -/
def cutPMF (G : Digraph V) (w : V → ℝ≥0) (s : V) : PMF (Outcome V) :=
  (cutMeasure G w s).toPMF

@[simp] theorem cutPMF_toMeasure (G : Digraph V) (w : V → ℝ≥0) (s : V) :
    (cutPMF G w s).toMeasure = uniformLevel.map (draw G w s) := by
  exact Measure.toPMF_toMeasure _

theorem cutPMF_apply (G : Digraph V) (w : V → ℝ≥0) (s : V) (Y : Outcome V) :
    cutPMF G w s Y = uniformLevel {d : ℝ | draw G w s d = Y} := by
  rw [cutPMF, Measure.toPMF_apply, cutMeasure,
    Measure.map_apply (measurable_draw G w s) (measurableSet_singleton Y)]
  rfl

/-- Every positive-probability outcome is attained by a genuine level in [0,1]. -/
theorem support_exists_level (G : Digraph V) (w : V → ℝ≥0) (s : V)
    {Y : Outcome V} (hY : Y ∈ (cutPMF G w s).support) :
    ∃ d : ℝ≥0, d ≤ 1 ∧ levelCut G w s d = Y.cut := by
  have hne : cutPMF G w s Y ≠ 0 := hY
  rw [cutPMF_apply, uniformLevel] at hne
  have hmeas : MeasurableSet {d : ℝ | draw G w s d = Y} :=
    (measurable_draw G w s) (measurableSet_singleton Y)
  rw [Measure.restrict_apply hmeas] at hne
  have hn : ({d : ℝ | draw G w s d = Y} ∩ Icc 0 1).Nonempty := by
    by_contra h
    have he : {d : ℝ | draw G w s d = Y} ∩ Icc 0 1 = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [he, measure_empty] at hne
    exact hne rfl
  obtain ⟨d, hdraw, hd0, hd1⟩ := hn
  refine ⟨d.toNNReal, ?_, ?_⟩
  · exact_mod_cast (show (d.toNNReal : ℝ) ≤ 1 by simpa [Real.coe_toNNReal _ hd0] using hd1)
  · exact congrArg Outcome.cut hdraw

/-- A genuine unit level for each supported outcome; zero off the support. -/
def realizeLevel (G : Digraph V) (w : V → ℝ≥0) (s : V) (Y : Outcome V) : ℝ≥0 :=
  if h : Y ∈ (cutPMF G w s).support then
    (support_exists_level G w s h).choose else 0

theorem realizeLevel_le_one (G : Digraph V) (w : V → ℝ≥0) (s : V) (Y : Outcome V) :
    realizeLevel G w s Y ≤ 1 := by
  unfold realizeLevel
  split_ifs with h
  · exact (support_exists_level G w s h).choose_spec.1
  · norm_num

theorem realizeLevel_cut (G : Digraph V) (w : V → ℝ≥0) (s : V)
    {Y : Outcome V} (hY : Y ∈ (cutPMF G w s).support) :
    levelCut G w s (realizeLevel G w s Y) = Y.cut := by
  simp only [realizeLevel, dite_eq_left hY]
  exact (support_exists_level G w s hY).choose_spec.2

/-- Support cuts really separate every feasible selected source demand. -/
theorem support_cutsPair (G : Digraph V) (w : V → ℝ≥0) (s t : V)
    (hfar : 1 ≤ vertexDistance G w s t) {Y : Outcome V}
    (hY : Y ∈ (cutPMF G w s).support) : CutsPair G Y.cut s t := by
  obtain ⟨d, hd, he⟩ := support_exists_level G w s hY
  rw [← he]
  exact levelCut_cuts_source_demand_unit G w hfar d hd

/-- The exact discrete expectation agrees with the original real experiment. -/
theorem expectation_eq_integral (G : Digraph V) (w : V → ℝ≥0) (s : V)
    (f : Outcome V → ℝ) :
    (∑ Y, (cutPMF G w s Y).toReal * f Y) =
      ∫ d, f (draw G w s d) ∂uniformLevel := by
  calc
    _ = ∫ Y, f Y ∂(cutPMF G w s).toMeasure := by
      simpa only [smul_eq_mul] using (PMF.integral_eq_sum (cutPMF G w s) f).symm
    _ = _ := by
      rw [cutPMF_toMeasure]
      exact integral_map (measurable_draw G w s).aemeasurable
        (measurable_of_finite f).aestronglyMeasurable

/-- The finite law has the actual expected-new-cost guarantee. -/
theorem expected_new_cost_le (G : Digraph V) (w cost : V → ℝ≥0)
    (s : V) (X : Finset V) :
    (∑ Y, (cutPMF G w s Y).toReal * (cutCost cost (Y.cut \ X) : ℝ)) ≤
      ((∑ v ∈ Finset.univ \ X, cost v * w v : ℝ≥0) : ℝ) := by
  rw [expectation_eq_integral]
  exact integral_newLevelCut_cost_le G w cost s X

/-- Unit costs give the finite expected-new-cardinality guarantee. -/
theorem expected_new_card_le (G : Digraph V) (w : V → ℝ≥0)
    (s : V) (X : Finset V) :
    (∑ Y, (cutPMF G w s Y).toReal * ((Y.cut \ X).card : ℝ)) ≤
      ((∑ v ∈ Finset.univ \ X, w v : ℝ≥0) : ℝ) := by
  simpa [cutCost] using expected_new_cost_le G w (fun _ => 1) s X

end
end DirectedFlowCutGap.FiniteCutLaw
