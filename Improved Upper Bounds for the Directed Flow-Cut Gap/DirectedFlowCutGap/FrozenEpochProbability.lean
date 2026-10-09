import DirectedFlowCutGap.LevelCutProbability
import DirectedFlowCutGap.FiniteSurvival
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Logic.Equiv.Fintype
import Mathlib.GroupTheory.Perm.Fin

/-!
# The genuine frozen-epoch experiment

A permutation of the finite demand labels is sampled uniformly, independently
of one uniform real level in `[0,1]` for each label. The virtual cut is the union
of the actual original-graph level cuts for a permutation prefix. The finite
subset law is proved by an explicit permutation of each fiber, rather than
postulated as a sampling assumption.

All stopped-process statements concern the joint event of reaching a round
and still having a path. They require only pointwise agreement with the frozen
virtual process on the reached event; there is no conditional-uniformity claim.
-/

namespace DirectedFlowCutGap.FrozenEpochProbability

noncomputable section

set_option maxHeartbeats 400000

open MeasureTheory Set
open scoped BigOperators NNReal ENNReal

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Independent uniform levels, one for each frozen demand label. -/
def levelsMeasure (E : Type*) [Fintype E] : Measure (E → ℝ) :=
  Measure.pi fun _ => uniformLevel

instance levelsMeasure_probability : IsProbabilityMeasure (levelsMeasure E) := by
  unfold levelsMeasure
  infer_instance

/-- A genuinely uniform measure on a nonempty finite type. -/
def finiteUniform (A : Type*) [Fintype A] [Nonempty A] [MeasurableSpace A] : Measure A :=
  (PMF.uniformOfFintype A).toMeasure

instance finiteUniform_probability (A : Type*) [Fintype A] [Nonempty A]
    [MeasurableSpace A] : IsProbabilityMeasure (finiteUniform A) := by
  unfold finiteUniform
  infer_instance

@[simp] theorem finiteUniform_singleton {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (a : A) :
    finiteUniform A {a} = (Fintype.card A : ℝ≥0∞)⁻¹ := by
  unfold finiteUniform
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply]

/-- Exact finite mixture formula, including its normalization. -/
theorem finiteUniform_prod_apply {A Ω : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {S : Set (A × Ω)} (hS : MeasurableSet S) :
    ((finiteUniform A).prod μ) S =
      (∑ a : A, μ {d | (a, d) ∈ S}) / (Fintype.card A : ℝ≥0∞) := by
  rw [Measure.prod_apply hS, lintegral_fintype]
  simp only [finiteUniform_singleton, div_eq_mul_inv, Finset.sum_mul]
  rfl

/-- Real-valued finite mixture formula for a probability experiment. -/
theorem finiteUniform_prod_apply_toReal {A Ω : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {S : Set (A × Ω)} (hS : MeasurableSet S) :
    (((finiteUniform A).prod μ) S).toReal =
      (∑ a : A, (μ {d | (a, d) ∈ S}).toReal) / (Fintype.card A : ℝ) := by
  rw [finiteUniform_prod_apply μ hS, ENNReal.toReal_div,
    ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  simp

/-- The finite sample space of subsets of exactly `k` labels. -/
abbrev SizedSubset (E : Type*) [Fintype E] (k : ℕ) :=
  ↥((Finset.univ : Finset E).powersetCard k)

@[simp] theorem sizedSubset_card (k : ℕ) :
    Fintype.card (SizedSubset E k) = (Fintype.card E).choose k := by
  simp [SizedSubset]

theorem sizedSubset_mem (k : ℕ) (S : SizedSubset E k) : S.val.card = k :=
  (Finset.mem_powersetCard.mp S.property).2

/-- Relabeling a fixed prefix by a permutation. -/
def permutedSubset (A : Finset E) (π : Equiv.Perm E) : SizedSubset E A.card :=
  ⟨A.image π, Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _, Finset.card_image_of_injective A π.injective⟩⟩

/-- Equally sized finite subsets are related by an actual permutation. -/
theorem exists_perm_image_eq {S T : Finset E} (h : S.card = T.card) :
    ∃ τ : Equiv.Perm E, S.image τ = T := by
  classical
  let e : S ≃ T := Fintype.equivOfCardEq (by simpa using h)
  refine ⟨e.extendSubtype, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact e.extendSubtype_mem x hx
  · simpa [Finset.card_image_of_injective S e.extendSubtype.injective] using h.ge

/-- The map on permutation fibers is postcomposition by a permutation carrying
one target subset to the other. This proves the fixed-size-subset law. -/
theorem permutedSubset_fiber_card_eq (A : Finset E)
    (S T : SizedSubset E A.card) :
    Fintype.card {π : Equiv.Perm E // permutedSubset A π = S} =
      Fintype.card {π : Equiv.Perm E // permutedSubset A π = T} := by
  classical
  obtain ⟨τ, hτ⟩ := exists_perm_image_eq
    ((sizedSubset_mem _ S).trans (sizedSubset_mem _ T).symm)
  have himage (π : Equiv.Perm E) :
      (permutedSubset A (τ * π)).val = (permutedSubset A π).val.image τ := by
    simp [permutedSubset, Finset.image_image, Function.comp_def, Equiv.Perm.mul_apply]
  let e : {π : Equiv.Perm E // permutedSubset A π = S} ≃
      {π : Equiv.Perm E // permutedSubset A π = T} :=
    { toFun := fun π => ⟨τ * π.val, by
        apply Subtype.ext
        rw [himage, π.property, hτ]⟩
      invFun := fun π => ⟨τ⁻¹ * π.val, by
        apply Subtype.ext
        apply Finset.image_injective τ.injective
        rw [← himage, mul_inv_cancel_left, π.property, hτ]⟩
      left_inv := by intro π; apply Subtype.ext; simp
      right_inv := by intro π; apply Subtype.ext; simp }
  exact Fintype.card_congr e

/-- A finite map with equally sized fibers sends the uniform average to the
uniform average. The fiber sizes and normalization are derived by summation. -/
theorem average_eq_of_equal_fibers {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] [DecidableEq B] (f : A → B)
    (h : ∀ b c, Fintype.card {a // f a = b} = Fintype.card {a // f a = c})
    (g : B → ℝ) :
    (∑ a, g (f a)) / (Fintype.card A : ℝ) =
      (∑ b, g b) / (Fintype.card B : ℝ) := by
  classical
  let b₀ : B := Classical.choice inferInstance
  let m : ℕ := Fintype.card {a // f a = b₀}
  have hs (g : B → ℝ) : ∑ a, g (f a) = (m : ℝ) * ∑ b, g b := by
    rw [← Fintype.sum_fiberwise f]
    simp_rw [show ∀ b (a : {a // f a = b}), g (f a.val) = g b from
      fun b a => congrArg g a.property]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp_rw [h _ b₀]
    exact (Finset.mul_sum _ _ _).symm
  have hc : (Fintype.card A : ℝ) = (m : ℝ) * Fintype.card B := by
    simpa using hs (fun _ => 1)
  have hA : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hs]
  apply (div_eq_div_iff hA hB).mpr
  rw [hc]
  ring

/-- Exact fixed-size subset law, stated for every real test function. -/
theorem permutation_average_eq_subsetAverage (A : Finset E) (f : Finset E → ℝ) :
    (∑ π : Equiv.Perm E, f (A.image π)) / (Fintype.card (Equiv.Perm E) : ℝ) =
      FiniteSurvival.subsetAverage Finset.univ A.card f := by
  classical
  letI : Nonempty (SizedSubset E A.card) := ⟨permutedSubset A 1⟩
  have h := average_eq_of_equal_fibers (permutedSubset A)
    (permutedSubset_fiber_card_eq A) (fun S => f S.val)
  simpa [permutedSubset, FiniteSurvival.subsetAverage, SizedSubset,
    Finset.sum_coe_sort, Finset.sum_attach] using h

/-- The first `i` positions in a fixed enumeration, subsequently permuted.
The proof argument allows both endpoints `i=0` and `i=|E|`. -/
def initialPrefix (order : Fin (Fintype.card E) ≃ E) (i : ℕ)
    (hi : i ≤ Fintype.card E) : Finset E :=
  Finset.univ.map ((Fin.castLEEmb hi).trans order.toEmbedding)

@[simp] theorem initialPrefix_card (order : Fin (Fintype.card E) ≃ E)
    (i : ℕ) (hi : i ≤ Fintype.card E) : (initialPrefix order i hi).card = i := by
  simp [initialPrefix]

@[simp] theorem initialPrefix_zero (order : Fin (Fintype.card E) ≃ E)
    (hi : 0 ≤ Fintype.card E) : initialPrefix order 0 hi = ∅ := by
  simp [initialPrefix]

@[simp] theorem initialPrefix_full (order : Fin (Fintype.card E) ≃ E)
    (hi : Fintype.card E ≤ Fintype.card E) :
    initialPrefix order (Fintype.card E) hi = Finset.univ := by
  apply Finset.eq_univ_of_card
  simp

local instance permutationMeasurableSpace : MeasurableSpace (Equiv.Perm E) := ⊤

/-- Uniform permutation, independent of all the uniform levels. -/
def experiment (E : Type*) [Fintype E] [DecidableEq E] : Measure (Equiv.Perm E × (E → ℝ)) :=
  (finiteUniform (Equiv.Perm E)).prod (levelsMeasure E)

instance experiment_probability : IsProbabilityMeasure (experiment E) := by
  unfold experiment
  infer_instance

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual accumulated cut after the labels in `S` have been sampled. -/
def frozenCut (G : Digraph V) (w : E → V → ℝ≥0) (s : E → V)
    (X₀ : Finset V) (S : Finset E) (d : E → ℝ) : Finset V :=
  X₀ ∪ S.biUnion (fun e => levelCut G (w e) (s e) (d e).toNNReal)

theorem measurable_frozenCut (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) (X₀ : Finset V) (S : Finset E) :
    Measurable (frozenCut G w s X₀ S) := by
  classical
  apply measurable_finset_iff.mpr
  intro v
  simp only [frozenCut, Finset.mem_union, Finset.mem_biUnion]
  exact measurable_const.or (Measurable.exists fun e =>
    measurable_const.and ((measurableSet_setOfPred.mp
      (measurableSet_levelHitEvent G (w e) (s e) v)).comp (measurable_pi_apply e)))

/-- Every event determined by the actual finite cut is measurable. -/
theorem measurableSet_frozenCut_property (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) (X₀ : Finset V) (A : Finset E) (P : Finset V → Prop) :
    MeasurableSet {ω : Equiv.Perm E × (E → ℝ) |
      P (frozenCut G w s X₀ (A.image ω.1) ω.2)} := by
  have hm : Measurable (fun ω : Equiv.Perm E × (E → ℝ) =>
      frozenCut G w s X₀ (A.image ω.1) ω.2) := by
    apply measurable_from_prod_countable_right
    intro π
    exact measurable_frozenCut G w s X₀ (A.image π)
  exact (Set.toFinite {X : Finset V | P X}).measurableSet.preimage hm

/-- No sampled separation interval is hit on the selected subset. -/
def avoids (G : Digraph V) (w : E → V → ℝ≥0) (s : E → V)
    (u v : V) (S : Finset E) : Set (E → ℝ) :=
  (S : Set E).pi (fun e => (levelSeparationEvent G (w e) (s e) u v)ᶜ)

/-- Independence is proved by the finite product measure rectangle identity. -/
theorem levelsMeasure_avoids (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) (u v : V) (S : Finset E) :
    levelsMeasure E (avoids G w s u v S) =
      ∏ e ∈ S, (1 - levelSeparationValue G (w e) (s e) u v) := by
  rw [levelsMeasure, avoids, Measure.pi_pi_finset]
  apply Finset.prod_congr rfl
  intro e he
  rw [measure_compl (measurableSet_levelSeparationEvent _ _ _ _ _)
    (measure_ne_top _ _), measure_univ, uniformLevel_levelSeparationEvent]

/-- Deterministic geometric coupling: a surviving true path avoids every
separation event for every sampled label. -/
theorem residualPath_mem_avoids (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) (X₀ : Finset V) (u v : V) (S : Finset E) (d : E → ℝ)
    (h : LevelResidualPath G (frozenCut G w s X₀ S d) u v) :
    d ∈ avoids G w s u v S := by
  intro e he hsep
  apply levelSeparationEvent_no_residualPath G (w e) (s e) u v X₀ hsep
  obtain ⟨p, hp⟩ := h
  refine ⟨p, fun z hz hmem => hp z hz ?_⟩
  rcases Finset.mem_union.mp hmem with hX | hcut
  · exact Finset.mem_union_left _ hX
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, he, hcut⟩)

/-- Actual conditional-on-a-fixed-subset graph survival is bounded by the
proved product of complementary separation probabilities. -/
theorem levelsMeasure_residualPath_le (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) (X₀ : Finset V) (u v : V) (S : Finset E) :
    levelsMeasure E {d | LevelResidualPath G (frozenCut G w s X₀ S d) u v} ≤
      ∏ e ∈ S, (1 - levelSeparationValue G (w e) (s e) u v) := by
  rw [← levelsMeasure_avoids G w s u v S]
  exact measure_mono fun d hd => residualPath_mem_avoids G w s X₀ u v S d hd

/-- Real form of the exact independent avoidance probability. -/
theorem levelsMeasure_avoids_toReal (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) (u v : V) (S : Finset E) :
    (levelsMeasure E (avoids G w s u v S)).toReal =
      ∏ e ∈ S, (1 - (levelSeparationValue G (w e) (s e) u v).toReal) := by
  rw [levelsMeasure_avoids, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro e he
  rw [ENNReal.toReal_sub_of_le (levelSeparationValue_le_one _ _ _ _ _)
    ENNReal.one_ne_top, ENNReal.toReal_one]

/-- The full virtual experiment satisfies Lemma 16's exponential tail.
The empty label type and the zero/full prefix endpoints are included. -/
theorem experiment_residualPath_le_exp (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) (X₀ : Finset V) (u v : V) (A : Finset E) :
    ((experiment E) {ω | LevelResidualPath G
      (frozenCut G w s X₀ (A.image ω.1) ω.2) u v}).toReal ≤
      Real.exp (-(A.card : ℝ) *
        (∑ e, (levelSeparationValue G (w e) (s e) u v).toReal) /
          (Fintype.card E : ℝ)) := by
  classical
  let a : E → ℝ := fun e => 1 - (levelSeparationValue G (w e) (s e) u v).toReal
  have ha (e : E) : 0 ≤ a e := by
    apply sub_nonneg.mpr
    exact (ENNReal.toReal_mono ENNReal.one_ne_top
      (levelSeparationValue_le_one G (w e) (s e) u v)).trans_eq ENNReal.toReal_one
  by_cases hE : Fintype.card E = 0
  · have hA : A.card = 0 := Nat.eq_zero_of_le_zero (hE ▸ Finset.card_le_univ A)
    simp only [hA, Nat.cast_zero, neg_zero, zero_mul, zero_div, Real.exp_zero]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using
      (prob_le_one (μ := experiment E)
        (s := {ω | LevelResidualPath G (frozenCut G w s X₀ (A.image ω.1) ω.2) u v})))
  rw [experiment, finiteUniform_prod_apply_toReal (levelsMeasure E)
    (measurableSet_frozenCut_property G w s X₀ A (fun X => LevelResidualPath G X u v))]
  calc
    _ ≤ (∑ π : Equiv.Perm E, ∏ e ∈ A.image π, a e) /
        (Fintype.card (Equiv.Perm E) : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro π hπ
      rw [← levelsMeasure_avoids_toReal G w s u v]
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      exact measure_mono fun d hd => residualPath_mem_avoids G w s X₀ u v _ d hd
    _ = FiniteSurvival.subsetAverage Finset.univ A.card
        (fun S => ∏ e ∈ S, a e) := permutation_average_eq_subsetAverage A (fun S => ∏ e ∈ S, a e)
    _ ≤ Real.exp (-(A.card : ℝ) * (∑ e, (1 - a e)) / (Fintype.card E : ℝ)) := by
      simpa using FiniteSurvival.subset_product_average_le_exp
        (Finset.univ : Finset E) a (by simpa using Nat.pos_of_ne_zero hE)
        (fun e _ => ha e) A.card (by simpa using Finset.card_le_univ A)
    _ = _ := by simp [a]

/-- A stopped process is compared on its reached event only. Its event of
reaching this round and retaining a path is a subset of virtual survival. -/
theorem stopped_joint_event_subset (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) (X₀ : Finset V) (u v : V) (A : Finset E)
    (reaches : Equiv.Perm E × (E → ℝ) → Prop)
    (actualCut : Equiv.Perm E × (E → ℝ) → Finset V)
    (hagrees : ∀ ω, reaches ω → actualCut ω = frozenCut G w s X₀ (A.image ω.1) ω.2) :
    {ω | reaches ω ∧ LevelResidualPath G (actualCut ω) u v} ⊆
      {ω | LevelResidualPath G (frozenCut G w s X₀ (A.image ω.1) ω.2) u v} := by
  intro ω hω
  change LevelResidualPath G (frozenCut G w s X₀ (A.image ω.1) ω.2) u v
  rw [← hagrees ω hω.1]
  exact hω.2

/-- The stopped epoch bound is a joint-event bound, with no conditioning on
survival or on the epoch reaching the requested round. -/
theorem experiment_stopped_joint_le_exp (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) (X₀ : Finset V) (u v : V) (A : Finset E)
    (reaches : Equiv.Perm E × (E → ℝ) → Prop)
    (actualCut : Equiv.Perm E × (E → ℝ) → Finset V)
    (hagrees : ∀ ω, reaches ω → actualCut ω = frozenCut G w s X₀ (A.image ω.1) ω.2) :
    ((experiment E) {ω | reaches ω ∧ LevelResidualPath G (actualCut ω) u v}).toReal ≤
      Real.exp (-(A.card : ℝ) *
        (∑ e, (levelSeparationValue G (w e) (s e) u v).toReal) /
          (Fintype.card E : ℝ)) := by
  apply le_trans _ (experiment_residualPath_le_exp G w s X₀ u v A)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact measure_mono (stopped_joint_event_subset G w s X₀ u v A reaches actualCut hagrees)


/-- The exponential tail expressed with a literal length-`i` permutation prefix. -/
theorem prefix_residualPath_le_exp (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) (X₀ : Finset V) (u v : V)
    (order : Fin (Fintype.card E) ≃ E) (i : ℕ) (hi : i ≤ Fintype.card E) :
    ((experiment E) {ω | LevelResidualPath G
      (frozenCut G w s X₀ ((initialPrefix order i hi).image ω.1) ω.2) u v}).toReal ≤
      Real.exp (-(i : ℝ) *
        (∑ e, (levelSeparationValue G (w e) (s e) u v).toReal) /
          (Fintype.card E : ℝ)) := by
  simpa using experiment_residualPath_le_exp G w s X₀ u v (initialPrefix order i hi)

/-- The exact permutation-averaged avoidance law, prior to Maclaurin's bound. -/
theorem experiment_avoids_toReal (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) (u v : V) (A : Finset E) :
    ((experiment E) {ω | ω.2 ∈ avoids G w s u v (A.image ω.1)}).toReal =
      FiniteSurvival.subsetAverage Finset.univ A.card
        (fun S => ∏ e ∈ S, (1 - (levelSeparationValue G (w e) (s e) u v).toReal)) := by
  have hm : MeasurableSet {ω : Equiv.Perm E × (E → ℝ) |
      ω.2 ∈ avoids G w s u v (A.image ω.1)} := by
    apply Measurable.setOf
    apply measurable_from_prod_countable_right
    intro π
    apply measurableSet_setOfPred.mp
    change MeasurableSet (avoids G w s u v (A.image π))
    exact MeasurableSet.pi (Finset.countable_toSet (A.image π)) fun e _ =>
      (measurableSet_levelSeparationEvent G (w e) (s e) u v).compl
  rw [experiment, finiteUniform_prod_apply_toReal (levelsMeasure E) hm]
  change (∑ π : Equiv.Perm E, (levelsMeasure E (avoids G w s u v (A.image π))).toReal) /
    (Fintype.card (Equiv.Perm E) : ℝ) = _
  simp_rw [levelsMeasure_avoids_toReal]
  exact permutation_average_eq_subsetAverage A
    (fun S => ∏ e ∈ S, (1 - (levelSeparationValue G (w e) (s e) u v).toReal))

/-- Evaluation at any one fixed position of a uniform permutation is uniform.
The equivalence of the evaluation fibers is multiplication by a transposition. -/
theorem permutation_evaluation_average (x : E) (f : E → ℝ) :
    (∑ π : Equiv.Perm E, f (π x)) / (Fintype.card (Equiv.Perm E) : ℝ) =
      (∑ e, f e) / (Fintype.card E : ℝ) := by
  classical
  letI : Nonempty E := ⟨x⟩
  apply average_eq_of_equal_fibers (fun π : Equiv.Perm E => π x)
  intro y z
  let τ : Equiv.Perm E := Equiv.swap y z
  apply Fintype.card_congr
  exact
    { toFun := fun π => ⟨τ * π.val, by simp [τ, Equiv.Perm.mul_apply, π.property]⟩
      invFun := fun π => ⟨τ * π.val, by simp [τ, Equiv.Perm.mul_apply, π.property]⟩
      left_inv := by intro π; apply Subtype.ext; simp [τ, ← mul_assoc]
      right_inv := by intro π; apply Subtype.ext; simp [τ, ← mul_assoc] }

/-- Exact expected sum of arbitrary label masses in a permutation prefix.
No positivity or nonempty-label assumption is needed. -/
theorem permutation_sum_average (A : Finset E) (f : E → ℝ) :
    (∑ π : Equiv.Perm E, ∑ e ∈ A.image π, f e) /
        (Fintype.card (Equiv.Perm E) : ℝ) =
      (A.card : ℝ) / (Fintype.card E : ℝ) * ∑ e, f e := by
  classical
  have himage (π : Equiv.Perm E) : ∑ e ∈ A.image π, f e = ∑ e ∈ A, f (π e) :=
    Finset.sum_image (fun a _ b _ h => π.injective h)
  simp_rw [himage]
  rw [Finset.sum_comm, Finset.sum_div]
  simp_rw [permutation_evaluation_average]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

/-- Pointwise union bound for the genuinely new cut vertices. -/
theorem frozenCut_new_card_le (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) (X₀ : Finset V) (S : Finset E) (d : E → ℝ) :
    (frozenCut G w s X₀ S d \ X₀).card ≤
      ∑ e ∈ S, (levelCut G (w e) (s e) (d e).toNNReal \ X₀).card := by
  classical
  have hset : frozenCut G w s X₀ S d \ X₀ =
      S.biUnion (fun e => levelCut G (w e) (s e) (d e).toNNReal \ X₀) := by
    ext v
    simp only [frozenCut, Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion]
    constructor
    · rintro ⟨hX | ⟨e, he, hv⟩, hn⟩
      · exact False.elim (hn hX)
      · exact ⟨e, he, hv, hn⟩
    · rintro ⟨e, he, hv, hn⟩
      exact ⟨Or.inr ⟨e, he, hv⟩, hn⟩
  rw [hset]
  exact Finset.card_biUnion_le

/-- For each fixed subset, the expected new-cut size is bounded by the sum
of its frozen outside masses, using the proved one-round marginal theorem. -/
theorem lintegral_frozenCut_new_card_le (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) (X₀ : Finset V) (S : Finset E) :
    (∫⁻ d, ((frozenCut G w s X₀ S d \ X₀).card : ℝ≥0∞) ∂levelsMeasure E) ≤
      ∑ e ∈ S, ∑ v ∈ Finset.univ \ X₀, (w e v : ℝ≥0∞) := by
  have hm (e : E) : Measurable (fun d : E → ℝ =>
      ((levelCut G (w e) (s e) (d e).toNNReal \ X₀).card : ℝ≥0∞)) := by
    simpa [Function.comp_def] using (measurable_newLevelCut_cost G (w e) (fun _ => 1) (s e) X₀).comp
      (measurable_pi_apply e)
  calc
    _ ≤ ∫⁻ d, ∑ e ∈ S,
        ((levelCut G (w e) (s e) (d e).toNNReal \ X₀).card : ℝ≥0∞) ∂levelsMeasure E := by
      apply lintegral_mono
      intro d
      dsimp only
      exact_mod_cast frozenCut_new_card_le G w s X₀ S d
    _ = ∑ e ∈ S, ∫⁻ d,
        ((levelCut G (w e) (s e) (d e).toNNReal \ X₀).card : ℝ≥0∞) ∂levelsMeasure E :=
      lintegral_finsetSum _ (fun e _ => hm e)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro e he
      have hp : MeasurePreserving (Function.eval e) (levelsMeasure E) uniformLevel :=
        measurePreserving_eval (fun _ : E => uniformLevel) e
      have hx := hp.lintegral_comp (f := fun d : ℝ =>
        ((levelCut G (w e) (s e) d.toNNReal \ X₀).card : ℝ≥0∞)) (by
          simpa using measurable_newLevelCut_cost G (w e) (fun _ => 1) (s e) X₀)
      rw [hx]
      exact lintegral_newLevelCut_card_le G (w e) (s e) X₀


/-- The frozen mass outside the epoch's initial cut. -/
def outsideMass (X₀ : Finset V) (w : V → ℝ≥0) : ℝ≥0 :=
  ∑ v ∈ Finset.univ \ X₀, w v

/-- The exact prefix average also holds for nonnegative masses. -/
theorem permutation_sum_average_nnreal (A : Finset E) (f : E → ℝ≥0) :
    (∑ π : Equiv.Perm E, ∑ e ∈ A.image π, f e) /
        (Fintype.card (Equiv.Perm E) : ℝ≥0) =
      (A.card : ℝ≥0) / (Fintype.card E : ℝ≥0) * ∑ e, f e := by
  exact_mod_cast permutation_sum_average A (fun e => (f e : ℝ))

/-- Lemma 14's genuine prefix expectation. The new vertices in the entire
union are counted only once. The right side is finite, including when `E`
is empty, where both sides are zero. -/
theorem lintegral_experiment_new_card_le (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) (X₀ : Finset V) (A : Finset E) :
    (∫⁻ ω, ((frozenCut G w s X₀ (A.image ω.1) ω.2 \ X₀).card : ℝ≥0∞)
      ∂experiment E) ≤
      (((A.card : ℝ≥0) / (Fintype.card E : ℝ≥0) * ∑ e, outsideMass X₀ (w e) : ℝ≥0) : ℝ≥0∞) := by
  classical
  have hm : Measurable (fun ω : Equiv.Perm E × (E → ℝ) =>
      ((frozenCut G w s X₀ (A.image ω.1) ω.2 \ X₀).card : ℝ≥0∞)) := by
    apply measurable_from_prod_countable_right
    intro π
    change Measurable (fun d : E → ℝ => ((frozenCut G w s X₀ (A.image π) d \ X₀).card : ℝ≥0∞))
    exact (measurable_of_finite (fun X : Finset V => ((X \ X₀).card : ℝ≥0∞))).comp
      (measurable_frozenCut G w s X₀ (A.image π))
  have hP : (Fintype.card (Equiv.Perm E) : ℝ≥0) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [experiment, lintegral_prod _ hm.aemeasurable, lintegral_fintype]
  simp only [finiteUniform_singleton]
  calc
    _ ≤ ∑ π : Equiv.Perm E,
        (∑ e ∈ A.image π, (outsideMass X₀ (w e) : ℝ≥0∞)) *
          (Fintype.card (Equiv.Perm E) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro π hπ
      apply mul_le_mul' _ le_rfl
      simpa only [outsideMass, ENNReal.ofNNReal_finsetSum] using
        lintegral_frozenCut_new_card_le G w s X₀ (A.image π)
    _ = (((∑ π : Equiv.Perm E, ∑ e ∈ A.image π, outsideMass X₀ (w e)) /
        (Fintype.card (Equiv.Perm E) : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_div hP]
      simp only [ENNReal.ofNNReal_finsetSum, ENNReal.coe_natCast,
        div_eq_mul_inv, Finset.sum_mul]
    _ = _ := by rw [permutation_sum_average_nnreal]

/-- A stopped prefix can only spend less than the corresponding virtual
prefix. This is the truncation comparison used at a deterministic horizon
chosen from the epoch-start history. -/
theorem lintegral_stopped_new_card_le (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) (X₀ : Finset V) (A : Finset E)
    (stoppedCut : Equiv.Perm E × (E → ℝ) → Finset V)
    (hsubset : ∀ ω, stoppedCut ω ⊆ frozenCut G w s X₀ (A.image ω.1) ω.2) :
    (∫⁻ ω, ((stoppedCut ω \ X₀).card : ℝ≥0∞) ∂experiment E) ≤
      (((A.card : ℝ≥0) / (Fintype.card E : ℝ≥0) * ∑ e, outsideMass X₀ (w e) : ℝ≥0) : ℝ≥0∞) := by
  apply le_trans _ (lintegral_experiment_new_card_le G w s X₀ A)
  apply lintegral_mono
  intro ω
  dsimp only
  exact_mod_cast Finset.card_le_card (Finset.sdiff_subset_sdiff_left X₀ (hsubset ω))


/-- The probability of any particular fixed-size subset is exactly the
reciprocal binomial coefficient, derived from the permutation counting law. -/
theorem uniformPermutation_subset_probability (A T : Finset E) (hT : T.card = A.card) :
    (finiteUniform (Equiv.Perm E) {π | A.image π = T}).toReal =
      1 / ((Fintype.card E).choose A.card : ℝ) := by
  classical
  have hm : MeasurableSet {π : Equiv.Perm E | A.image π = T} :=
    (Set.toFinite _).measurableSet
  have ht : T ∈ (Finset.univ : Finset E).powersetCard A.card := by
    simp [Finset.mem_powersetCard, hT]
  have h := permutation_average_eq_subsetAverage A (fun S => if S = T then 1 else 0)
  rw [finiteUniform, PMF.toMeasure_uniformOfFintype_apply _ hm, ENNReal.toReal_div]
  simpa [FiniteSurvival.subsetAverage, ht, Fintype.card_subtype] using h

/-- The prefix expected-size bound with its literal round index. -/
theorem lintegral_prefix_new_card_le (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) (X₀ : Finset V) (order : Fin (Fintype.card E) ≃ E)
    (i : ℕ) (hi : i ≤ Fintype.card E) :
    (∫⁻ ω, ((frozenCut G w s X₀ ((initialPrefix order i hi).image ω.1) ω.2 \ X₀).card : ℝ≥0∞)
      ∂experiment E) ≤
      (((i : ℝ≥0) / (Fintype.card E : ℝ≥0) * ∑ e, outsideMass X₀ (w e) : ℝ≥0) : ℝ≥0∞) := by
  simpa using lintegral_experiment_new_card_le G w s X₀ (initialPrefix order i hi)

/-- At round zero, the virtual cut is exactly the epoch-start cut. -/
@[simp] theorem frozenCut_empty (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) (X₀ : Finset V) (d : E → ℝ) :
    frozenCut G w s X₀ ∅ d = X₀ := by
  simp [frozenCut]

/-- An empty label type permits no rounds and incurs no new vertices. -/
@[simp] theorem frozenCut_of_isEmpty [IsEmpty E] (G : Digraph V)
    (w : E → V → ℝ≥0) (s : E → V) (X₀ : Finset V) (A : Finset E) (d : E → ℝ) :
    frozenCut G w s X₀ A d = X₀ := by
  rw [Finset.eq_empty_of_isEmpty A, frozenCut_empty]

/-- At the full prefix, every label is used, independently of permutation. -/
theorem frozenCut_full_prefix (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) (X₀ : Finset V) (order : Fin (Fintype.card E) ≃ E)
    (π : Equiv.Perm E) (d : E → ℝ) :
    frozenCut G w s X₀ ((initialPrefix order (Fintype.card E) le_rfl).image π) d =
      frozenCut G w s X₀ Finset.univ d := by
  rw [initialPrefix_full]
  congr 1
  exact Finset.image_univ_of_surjective π.surjective

end

end DirectedFlowCutGap.FrozenEpochProbability
