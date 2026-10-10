import DirectedFlowCutGap.BinaryZeroAvoidingProvider
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Same-query cost failure for the actual zero-avoiding provider

The actual provider is a deterministic pushforward of its one cut-provider
call at the retained penalized binary row. Its output cost failure is charged
only to that same query's cost failure. A `none` answer is charged only when
the original positive-support fallback itself exceeds the requested budget.

The original cut-provider quality bound remains a pointwise hypothesis at
the actual query; no uniform-over-all-queries hypothesis is introduced here.
Physical failure flags are unrelated to these proof-only real cost events.
Structural validity and zero avoidance hold on every branch. Alpha is arbitrary,
and every potential in the cost guarantee uses the original input capacities.

This is a proof-only companion. It neither changes the executable provider nor
proves an adaptive union bound. The imported provider, packing, graph-bound and
selector modules include pending drafts; this source is also uncompiled.
-/

namespace DirectedFlowCutGap.BinaryZeroAvoidingProbability

open scoped BigOperators ENNReal NNRat
open BinaryFractionalRows BinaryApproximatePacking BinaryApproximatePackingZeros
open BinaryZeroAvoidingProvider BinaryZeroAvoidingSelector ZeroAvoidingSelector

noncomputable section

variable {m : ℕ}

def answerCost (c : Row m) (a : Answer m) : ℝ :=
  ∑ i ∈ (BinaryFractionalCore.decodeChoice a.choice).column, tableValue c i

def supportCost (w c : Row m) : ℝ :=
  ∑ i ∈ positiveSupport (tableValue w), tableValue c i

def outputFailure (w c : Row m) (α : ℝ) : Set (Answer m) :=
  {a | α * mwPotential (tableValue w) (tableValue c) < answerCost c a}

theorem tableValue_eq_capacity (c : Row m) (i : Fin m) :
    tableValue c i = (FractionalCover.value (capacities c) i : ℝ) := by
  rw [tableValue_apply, capacities_value]
  unfold FractionalCoverRawCore.rational
  norm_cast

/-- Exact bridge to the packing controller's rational length, at the same
retained binary query and returned choice. -/
theorem answerCost_eq_length (c : Row m) (a : Answer m) :
    answerCost c a = (FractionalCover.length (capacities c)
      (BinaryFractionalCore.decodeChoice a.choice).column : ℝ) := by
  simp only [answerCost, FractionalCover.length, Rat.cast_sum, tableValue_eq_capacity]

theorem potential_eq_objective (w c : Row m) :
    mwPotential (tableValue w) (tableValue c) =
      (FractionalCover.objective (capacities w) (capacities c) : ℝ) := by
  simp only [mwPotential, FractionalCover.objective, Rat.cast_sum, Rat.cast_mul,
    tableValue_eq_capacity, mul_comm]

/-- The original valid-or-none provider's per-query cost event. In particular,
`failed = false` is not a cost certificate, and `failed = true` is not required
for membership. The `none` case makes absence of a returned cut explicit. -/
def queryFailure (w d : Row m) (α : ℝ)
    {columns : Set (FractionalCover.Column m)} : Set (CutAnswer columns) :=
  {a | match a.mask with
    | none => True
    | some x => α * mwPotential (tableValue w) (tableValue d) <
        ∑ i ∈ column x, tableValue d i}

/-- The sharper event omits even a failed query when the actual support
fallback already meets the original-input budget. -/
def chargedFailure (w c : Row m) (α : ℝ)
    {columns : Set (FractionalCover.Column m)} : Set (CutAnswer columns) :=
  {a | α * mwPotential (tableValue w) (tableValue c) < supportCost w c ∧
    a ∈ queryFailure w (prepare w c).costs α}

theorem chargedFailure_subset (w c : Row m) (α : ℝ)
    (columns : Set (FractionalCover.Column m)) :
    chargedFailure w c α (columns := columns) ⊆
      queryFailure w (prepare w c).costs α := fun _ h => h.2

theorem queryFailure_some_iff (w c : Row m) (α : ℝ)
    {columns : Set (FractionalCover.Column m)} (a : CutAnswer columns)
    (x : BinaryZeroAvoidingProvider.Mask m) (ha : a.mask = some x) :
    a ∈ queryFailure w (prepare w c).costs α ↔
      α * mwPotential (tableValue w) (tableValue c) <
        ∑ i ∈ column x, tableValue (prepare w c).costs i := by
  simp only [queryFailure, Set.mem_ofPred_eq, ha, prepare_potential]

theorem chargedFailure_none_iff (w c : Row m) (α : ℝ)
    {columns : Set (FractionalCover.Column m)} (a : CutAnswer columns)
    (ha : a.mask = none) :
    a ∈ chargedFailure w c α ↔
      α * mwPotential (tableValue w) (tableValue c) < supportCost w c := by
  simp only [chargedFailure, queryFailure, Set.mem_ofPred_eq, ha, and_true]

theorem chargedFailure_eq_empty (w c : Row m) (α : ℝ)
    (columns : Set (FractionalCover.Column m))
    (hgood : supportCost w c ≤ α * mwPotential (tableValue w) (tableValue c)) :
    chargedFailure w c α (columns := columns) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  exact (not_lt_of_ge hgood) ha.1

/-- All masks, including `none` fallback and a rejected candidate, obey the
actual original-support cost ceiling. -/
theorem completion_cost_le_support {w c : Row m}
    {columns : Set (FractionalCover.Column m)} {a : CutAnswer columns}
    (r : Completion w columns (prepare w c) a) :
    answerCost c r.answer ≤ supportCost w c := by
  change (∑ i ∈ Raw.cut r.answer.choice.mask, tableValue c i) ≤ _
  rw [r.mask_eq]
  cases a.mask with
  | none =>
      rw [select_none]
      change (∑ i ∈ Raw.cut (support w).1, tableValue c i) ≤ supportCost w c
      simp only [support_correct, supportCost, le_refl]
  | some x =>
      rw [select_some_cut, choose_cost_eq _ _ (tableValue_nonneg c)]
      exact choose_budget _ _ _

theorem completion_none_cost {w c : Row m}
    {columns : Set (FractionalCover.Column m)} {a : CutAnswer columns}
    (r : Completion w columns (prepare w c) a) (ha : a.mask = none) :
    answerCost c r.answer = supportCost w c := by
  change (∑ i ∈ Raw.cut r.answer.choice.mask, tableValue c i) = _
  rw [r.mask_eq, ha, select_none]
  change (∑ i ∈ Raw.cut (support w).1, tableValue c i) = supportCost w c
  simp only [support_correct, supportCost]

/-- None is neither assumed good nor automatically charged: its actual
fallback cost determines precisely whether output cost failure occurs. -/
theorem completion_none_failure_iff {w c : Row m}
    {columns : Set (FractionalCover.Column m)} {a : CutAnswer columns}
    (r : Completion w columns (prepare w c) a) (ha : a.mask = none) (α : ℝ) :
    r.answer ∈ outputFailure w c α ↔
      α * mwPotential (tableValue w) (tableValue c) < supportCost w c := by
  change _ < answerCost c r.answer ↔ _
  rw [completion_none_cost r ha]

/-- The successful-mask implication is exactly the frozen provider theorem.
Its contrapositive uses no assumption about any physical metadata field. -/
theorem completion_failure_subset {w c : Row m}
    {columns : Set (FractionalCover.Column m)} {a : CutAnswer columns}
    (r : Completion w columns (prepare w c) a) (α : ℝ)
    (hbad : r.answer ∈ outputFailure w c α) :
    a ∈ chargedFailure w c α := by
  have hb : α * mwPotential (tableValue w) (tableValue c) < answerCost c r.answer := hbad
  refine ⟨hb.trans_le (completion_cost_le_support r), ?_⟩
  cases ha : a.mask with
  | none => simp only [queryFailure, Set.mem_ofPred_eq, ha]
  | some x =>
      simp only [queryFailure, Set.mem_ofPred_eq, ha]
      by_contra h
      have hg := r.preserves_factor rfl x ha α (le_of_not_gt h)
      exact (not_lt_of_ge hg) hb

/-- The actual monadic body makes precisely this one query. -/
theorem provider_map (w c : Row m) (columns : Set (FractionalCover.Column m))
    (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (draw : CutProvider PMF columns) :
    provider w columns hS hempty draw c =
      (draw (prepare w c).costs).map
        (fun a => (finish w c columns hS hempty (prepare w c) rfl a).asSafe) := rfl

theorem auxiliaryProvider_map (w c : Row m) (columns : Set (FractionalCover.Column m))
    (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (draw : CutProvider PMF columns) :
    auxiliaryProvider w columns hS hempty draw c =
      (draw (prepare w c).costs).map
        (fun a => (finish w c columns hS hempty (prepare w c) rfl a).asAuxiliary) := rfl

/-- Changing the erased capacity certificate preserves the entire answer law,
including actual operations, failures, trials and consumed bits. -/
theorem provider_answer_law (w c : Row m) (columns : Set (FractionalCover.Column m))
    (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (draw : CutProvider PMF columns) :
    (provider w columns hS hempty draw c).map Subtype.val =
      (auxiliaryProvider w columns hS hempty draw c).map Subtype.val := by
  simp only [provider_map, auxiliaryProvider_map, PMF.map_comp,
    Function.comp_def, Completion.asSafe, Completion.asAuxiliary]

theorem provider_failure_le_charged (w c : Row m)
    (columns : Set (FractionalCover.Column m))
    (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (draw : CutProvider PMF columns) (α : ℝ) :
    (provider w columns hS hempty draw c).toOuterMeasure
        {a | a.1 ∈ outputFailure w c α} ≤
      (draw (prepare w c).costs).toOuterMeasure (chargedFailure w c α) := by
  rw [provider_map, PMF.toOuterMeasure_map_apply]
  apply (draw (prepare w c).costs).toOuterMeasure.mono
  intro a ha
  exact completion_failure_subset
    (finish w c columns hS hempty (prepare w c) rfl a) α ha

theorem auxiliaryProvider_failure_le_charged (w c : Row m)
    (columns : Set (FractionalCover.Column m))
    (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (draw : CutProvider PMF columns) (α : ℝ) :
    (auxiliaryProvider w columns hS hempty draw c).toOuterMeasure
        {a | a.1 ∈ outputFailure w c α} ≤
      (draw (prepare w c).costs).toOuterMeasure (chargedFailure w c α) := by
  rw [auxiliaryProvider_map, PMF.toOuterMeasure_map_apply]
  apply (draw (prepare w c).costs).toOuterMeasure.mono
  intro a ha
  exact completion_failure_subset
    (finish w c columns hS hempty (prepare w c) rfl a) α ha

/-- Only a cost-quality bound at this actual penalized query is required. -/
theorem provider_failure_le (w c : Row m)
    (columns : Set (FractionalCover.Column m))
    (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (draw : CutProvider PMF columns) (α : ℝ) (ε : ℝ≥0∞)
    (hquery : (draw (prepare w c).costs).toOuterMeasure
      (queryFailure w (prepare w c).costs α) ≤ ε) :
    (provider w columns hS hempty draw c).toOuterMeasure
      {a | a.1 ∈ outputFailure w c α} ≤ ε :=
  (provider_failure_le_charged w c columns hS hempty draw α).trans
    (((draw (prepare w c).costs).toOuterMeasure.mono
      (chargedFailure_subset w c α columns)).trans hquery)

theorem auxiliaryProvider_failure_le (w c : Row m)
    (columns : Set (FractionalCover.Column m))
    (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (draw : CutProvider PMF columns) (α : ℝ) (ε : ℝ≥0∞)
    (hquery : (draw (prepare w c).costs).toOuterMeasure
      (queryFailure w (prepare w c).costs α) ≤ ε) :
    (auxiliaryProvider w columns hS hempty draw c).toOuterMeasure
      {a | a.1 ∈ outputFailure w c α} ≤ ε :=
  (auxiliaryProvider_failure_le_charged w c columns hS hempty draw α).trans
    (((draw (prepare w c).costs).toOuterMeasure.mono
      (chargedFailure_subset w c α columns)).trans hquery)

/-- A cheap support fallback makes the output cost event empty, even if the
cut provider always returns `none` or marks every answer physically failed. -/
theorem provider_failure_zero_of_support (w c : Row m)
    (columns : Set (FractionalCover.Column m))
    (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (draw : CutProvider PMF columns) (α : ℝ)
    (hgood : supportCost w c ≤ α * mwPotential (tableValue w) (tableValue c)) :
    (provider w columns hS hempty draw c).toOuterMeasure
      {a | a.1 ∈ outputFailure w c α} = 0 := by
  apply le_antisymm _ zero_le
  have h := provider_failure_le_charged w c columns hS hempty draw α
  simpa only [chargedFailure_eq_empty w c α columns hgood,
    MeasureTheory.measure_empty] using h

theorem auxiliaryProvider_failure_zero_of_support (w c : Row m)
    (columns : Set (FractionalCover.Column m))
    (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (draw : CutProvider PMF columns) (α : ℝ)
    (hgood : supportCost w c ≤ α * mwPotential (tableValue w) (tableValue c)) :
    (auxiliaryProvider w columns hS hempty draw c).toOuterMeasure
      {a | a.1 ∈ outputFailure w c α} = 0 := by
  apply le_antisymm _ zero_le
  have h := auxiliaryProvider_failure_le_charged w c columns hS hempty draw α
  simpa only [chargedFailure_eq_empty w c α columns hgood,
    MeasureTheory.measure_empty] using h

/-- Every result of the auxiliary provider still has an attained ORIGINAL
input bottleneck and an original valid zero-free mask, unconditionally. -/
theorem auxiliaryProvider_original_safe (w c : Row m)
    (columns : Set (FractionalCover.Column m))
    (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (draw : CutProvider PMF columns)
    (a : SafeAnswer (auxiliary w) (zeroFreeColumns w columns))
    (ha : a ∈ (auxiliaryProvider w columns hS hempty draw c).support) :
    SafeChoice w (zeroFreeColumns w columns) a.1.choice := by
  rw [auxiliaryProvider_map] at ha
  obtain ⟨b, _, hb⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
  subst a
  exact (finish w c columns hS hempty (prepare w c) rfl b).safe

end

end DirectedFlowCutGap.BinaryZeroAvoidingProbability
