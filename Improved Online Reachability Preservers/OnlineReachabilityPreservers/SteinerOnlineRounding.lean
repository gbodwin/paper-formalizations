import Mathlib.Algebra.Order.BigOperators.Expect
import OnlineReachabilityPreservers.SteinerFiniteSampling
import OnlineReachabilityPreservers.SteinerForestRounding

/-! Prefix and counting lemmas for fixed-seed online rounding. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped BigOperators

private theorem weightedCoverLoop_increases {E : Type*} [DecidableEq E]
    (search : (E → ℕ) → Option (Finset E)) (fuel : ℕ) (initial : E → ℕ) :
    initial ≤ (weightedCoverLoop search fuel initial).1 := by
  induction fuel generalizing initial with
  | zero => exact le_rfl
  | succ fuel ih =>
    cases h : search initial with
    | none => simp [weightedCoverLoop, h]
    | some cut =>
      simp only [weightedCoverLoop, h]
      exact (le_chargeWeightedCut cut initial).trans (ih _)

section Network

variable {V : Type*} [LinearOrder V] [Fintype V]

private theorem weightedNetworkRun_increases (edges : Arcs V) (weight : V × V → ℕ)
    (requests : List (WeightedNetworkDemand V)) (initial : V × V → ℕ) :
    initial ≤ (weightedNetworkRun edges weight requests initial).1 := by
  induction requests generalizing initial with
  | nil => exact le_rfl
  | cons q rest ih =>
    simp only [weightedNetworkRun]
    exact (weightedCoverLoop_increases _ _ initial).trans (ih _)

private theorem weightedNetworkRun_append_charges (edges : Arcs V) (weight : V × V → ℕ)
    (left right : List (WeightedNetworkDemand V)) (initial : V × V → ℕ) :
    (weightedNetworkRun edges weight (left ++ right) initial).1 =
      (weightedNetworkRun edges weight right (weightedNetworkRun edges weight left initial).1).1 := by
  induction left generalizing initial with
  | nil => rfl
  | cons q rest ih =>
    simpa only [List.cons_append, weightedNetworkRun] using
      ih (weightedNetworkStep edges weight q initial).1

theorem forestFractionalRun_charges_mono (G : Arcs V) (height : ℕ) {D E : List (V × V)}
    (prefixOf : D <+: E) : (forestFractionalRun G height D).1 ≤ (forestFractionalRun G height E).1 := by
  obtain ⟨rest, rfl⟩ := prefixOf
  simp only [forestFractionalRun, List.map_append, weightedNetworkRun_append_charges]
  exact weightedNetworkRun_increases _ _ _ _

end Network

section Probability

variable {I J Ω : Type*} [Fintype J] [Fintype Ω]

/-- Outcomes with the same profile need to be counted only once in a
union bound. The profiles are used in the analysis of fixed seeds. -/
theorem finiteProbability_biUnion_profiles_le [DecidableEq Ω] [DecidableEq J]
    (s : Finset I) (profile : I → J) (event : I → Finset Ω) {μ : ℝ} (nonneg : 0 ≤ μ)
    (bound : ∀ i ∈ s, finiteProbability (event i) ≤ μ)
    (constant : ∀ i ∈ s, ∀ j ∈ s, profile i = profile j → event i = event j) :
    finiteProbability (s.biUnion event) ≤ (Fintype.card J : ℝ) * μ := by
  classical
  let bucket := fun j => (s.filter (fun i => profile i = j)).biUnion event
  have unionEq : s.biUnion event = (univ : Finset J).biUnion bucket := by
    ext ω
    simp only [bucket, mem_biUnion, mem_univ, mem_filter, true_and]
    exact ⟨fun ⟨i, hi, hω⟩ => ⟨profile i, i, ⟨hi, rfl⟩, hω⟩,
      fun ⟨_, i, hi, hω⟩ => ⟨i, hi.1, hω⟩⟩
  rw [unionEq]
  refine (finiteProbability_biUnion_le _ _).trans ?_
  calc
    _ ≤ ∑ _ : J, μ := by
      apply sum_le_sum
      intro j _
      cases (s.filter (fun i => profile i = j)).eq_empty_or_nonempty with
      | inl empty =>
        change finiteProbability ((s.filter _).biUnion event) ≤ μ
        rw [empty, biUnion_empty]
        simpa [finiteProbability] using nonneg
      | inr nonempty =>
        obtain ⟨i, h⟩ := nonempty
        have parts := mem_filter.mp h
        have same : bucket j = event i := by
          ext ω
          simp only [bucket, mem_biUnion, mem_filter]
          exact ⟨fun ⟨v, ⟨hv, hv'⟩, hω⟩ => (constant v hv i parts.1 (hv'.trans parts.2.symm)) ▸ hω,
            fun hω => ⟨i, parts, hω⟩⟩
        rw [same]
        exact bound i parts.1
    _ = _ := by simp

end Probability

section ForestCosts

variable {V : Type*} {height : ℕ} [LinearOrder V] [Fintype V]

local instance : DecidableEq (ForestNetworkVertex V height) :=
  (inferInstance : LinearOrder (ForestNetworkVertex V height)).toDecidableEq

private theorem forestMetricUnits_mono (G : Arcs V) (scale : ℕ)
    {old new : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ}
    (increase : old ≤ new) (e : HeightForestVertex V height × HeightForestVertex V height) :
    forestMetricUnits G old scale e ≤ forestMetricUnits G new scale e := by
  simp only [forestMetricUnits]
  split
  · split
    · exact le_rfl
    · exact roundedWeightedCapacity_mono (Nat.pos_of_ne_zero ‹heightForestWeight G e ≠ 0›) (increase _)
  · exact le_rfl

private theorem forestLegUnits_mono (G : Arcs V) (scale : ℕ) {r : V} {side : Bool}
    {old new : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ}
    (increase : old ≤ new) : forestLegUnits G old scale r side ≤ forestLegUnits G new scale r side :=
  fun _ => forestMetricUnits_mono G scale increase _

private theorem forestPaidArc_history {G : Arcs V} {e : HeightForestVertex V height × HeightForestVertex V height}
    (link : e ∈ heightForest G height) (positive : 0 < heightForestWeight G e) :
    let r := heightForestRoot e.1
    let side := roundingArcSide e
    let child := roundingArcHistory e
    child ≠ heightRoot ∧ heightForestLegArc r side child = e := by
  obtain ⟨root, _, present⟩ := mem_biUnion.mp link
  rcases mem_union.mp present with sides | center
  · rcases mem_union.mp sides with left | right
    · obtain ⟨⟨a, b⟩, edge, rfl⟩ := mem_map.mp left
      obtain ⟨nonempty, _, rfl⟩ := inwardHeightTree_edge_iff.mp edge
      exact ⟨fun eq => nonempty (congrArg Subtype.val eq), rfl⟩
    · obtain ⟨⟨a, b⟩, edge, rfl⟩ := mem_map.mp right
      obtain ⟨nonempty, _, rfl⟩ := inwardHeightTree_edge_iff.mp (edge_reverseArcs.mp edge)
      exact ⟨fun eq => nonempty (congrArg Subtype.val eq), rfl⟩
  · obtain eq := mem_singleton.mp center
    rw [eq] at positive
    simp [heightForestWeight, heightForestRootLink] at positive

private noncomputable def forestArcTierEvent (G : Arcs V)
    (charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ)
    (scale : ℕ) (r : V) (side : Bool) (child : HeightNode V height) (tier : Fin (scale.log2 + 1)) :
    Finset (ForestRoundingSample V height scale) := by
  classical
  exact coordinatePreimage r (coordinatePreimage tier
    (lowThreshold (forestSeedSize scale) (2 ^ tier.val) ×ˢ
      coordinatePreimage side
        (selectedHistoryEvent (forestSeedSize scale)
          (historyCutoff (scale.log2 + 1) tier.val (forestLegUnits G charges scale r side)) child)))

@[simp]
private theorem mem_forestArcTierEvent {G : Arcs V}
    {charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ}
    {scale : ℕ} {r : V} {side : Bool} {child : HeightNode V height} {tier : Fin (scale.log2 + 1)}
    {sample : ForestRoundingSample V height scale} :
    sample ∈ forestArcTierEvent G charges scale r side child tier ↔
      (sample r tier).1.val < 2 ^ tier.val ∧ forestLegSelected G charges scale r tier (sample r tier) side child := by
  simp [forestArcTierEvent, lowThreshold, forestLegSelected, selectedHistoryEvent]

private theorem forestArcTierEvent_probability (G : Arcs V)
    (charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ)
    (scale : ℕ) (r : V) (side : Bool) (child : HeightNode V height) (tier : Fin (scale.log2 + 1)) :
    finiteProbability (forestArcTierEvent G charges scale r side child tier) =
      (historyCapacityUnits tier.val (forestLegUnits G charges scale r side) child : ℝ) /
        (forestSeedSize scale : ℝ) := by
  classical
  let sampleSize := forestSeedSize scale
  have samplePositive : 0 < sampleSize := by dsimp [sampleSize, forestSeedSize]; positivity
  let zero : Fin sampleSize := ⟨0, samplePositive⟩
  have seed : Nonempty (ForestRootSample V height scale) := ⟨zero, fun _ _ => zero⟩
  have seeds : Nonempty (Fin (scale.log2 + 1) → ForestRootSample V height scale) := ⟨fun _ => seed.some⟩
  have historySeed : Nonempty (historySample V height sampleSize) := ⟨fun _ => zero⟩
  have tierLe : tier.val ≤ scale.log2 + 1 := tier.isLt.le
  unfold forestArcTierEvent
  rw [finiteProbability_coordinatePreimage, finiteProbability_coordinatePreimage,
    finiteProbability_product, finiteProbability_coordinatePreimage]
  change finiteProbability (lowThreshold sampleSize (2 ^ tier.val)) * historyCap sampleSize
      (historyCutoff (scale.log2 + 1) tier.val (forestLegUnits G charges scale r side)) child = _
  rw [finiteProbability, lowThreshold_card, Fintype.card_fin, historyCap_dyadic tierLe]
  have powBound : 2 ^ tier.val ≤ sampleSize := Nat.pow_le_pow_right (by decide) tierLe
  have tierNe : (((2 ^ tier.val : ℕ) : ℝ)) ≠ 0 := by positivity
  have sampleNe : (sampleSize : ℝ) ≠ 0 := (Nat.cast_pos.mpr samplePositive).ne'
  rw [min_eq_right powBound]
  change (((2 ^ tier.val : ℕ) : ℝ) / sampleSize) * _ =
    (historyCapacityUnits tier.val (forestLegUnits G charges scale r side) child : ℝ) / (sampleSize : ℝ)
  field_simp [tierNe, sampleNe]

private theorem historyAncestorCutoffs_eq {u : HeightNode V height}
    (sampleTier tier : ℕ) {A B : HeightNode V height → ℕ}
    (profile : ∀ a ∈ historyAncestors u, historyCapacityUnits tier A a = historyCapacityUnits tier B a)
    {a : HeightNode V height} (ancestor : a ∈ historyAncestors u) :
    historyCutoff sampleTier tier A a = historyCutoff sampleTier tier B a := by
  unfold historyCutoff
  split
  · rfl
  · have parent : heightParent a ∈ historyAncestors u :=
      mem_historyAncestors.mpr ((List.dropLast_prefix _).trans (mem_historyAncestors.mp ancestor))
    rw [profile a ancestor, profile (heightParent a) parent]

private def historyProfile (tier : ℕ) (A : HeightNode V height → ℕ) (u : HeightNode V height) :
    historyAncestors u → Option (Fin (tier + 1)) :=
  fun a =>
    let value := historyCapacityUnits tier A a.val
    if value = 0 then none else
      some ⟨value.log2, Nat.lt_succ_of_le (by
        have le := historyCapacityUnits_bounded tier A a.val
        simpa only [← Nat.log2_eq_log_two, Nat.log2_two_pow]
          using Nat.log_mono_right le (b := 2))⟩

private theorem historyProfile_recovers (tier : ℕ) (A : HeightNode V height → ℕ)
    (u : HeightNode V height) (a : historyAncestors u) :
    (match historyProfile tier A u a with
      | none => 0
      | some j => 2 ^ j.val) = historyCapacityUnits tier A a.val := by
  rcases historyCapacityUnits_power tier A a.val with zero | ⟨k, _, value⟩
  · simp [historyProfile, zero]
  · simp [historyProfile, value]

private noncomputable def forestTierPrefixEvent (G : Arcs V) (scale : ℕ) (D : List (V × V))
    (r : V) (side : Bool) (child : HeightNode V height) (tier : Fin (scale.log2 + 1)) :
    Finset (ForestRoundingSample V height scale) := by
  classical
  exact D.inits.toFinset.biUnion fun P =>
    forestArcTierEvent G (forestFractionalRun G height P).1 scale r side child tier

/-- At a fixed tier the union over many prefixes has at most as many
distinct events as there are capacity profiles on the arc's ancestors. -/
theorem forestArcTier_anyPrefix_bound (G : Arcs V) (scale : ℕ)
    (D : List (V × V)) (r : V) (side : Bool) (child : HeightNode V height)
    (notRoot : child ≠ heightRoot) (tier : Fin (scale.log2 + 1)) :
    let finalUnits := forestLegUnits G (forestFractionalRun G height D).1 scale r side child
    finiteProbability (forestTierPrefixEvent G scale D r side child tier) ≤
      ((scale.log2 + 2 : ℕ) : ℝ) ^ (height + 1) * (2 * finalUnits / (forestSeedSize scale : ℝ)) := by
  classical
  let event := fun P : List (V × V) =>
    forestArcTierEvent G (forestFractionalRun G height P).1 scale r side child tier
  let U := fun P : List (V × V) => forestLegUnits G (forestFractionalRun G height P).1 scale r side
  let finalUnits := U D child
  let J := historyAncestors child → Option (Fin (tier.val + 1))
  have bound (P : List (V × V)) (hp : P ∈ D.inits.toFinset) :
      finiteProbability (event P) ≤ 2 * (finalUnits : ℝ) / (forestSeedSize scale : ℝ) := by
    have pref := (List.mem_inits _ _).mp (List.mem_toFinset.mp hp)
    have units := forestLegUnits_mono G scale (r := r) (side := side) (forestFractionalRun_charges_mono G height pref)
    have capped := historyCapacityUnits_le tier.val (U P) (u := child) (v := child) List.prefix_rfl
    have upper : historyCapacityUnits tier.val (U P) child ≤ 2 * finalUnits := by
      simp only [rootCappedCapacity, notRoot, ↓reduceIte] at capped
      exact capped.trans ((min_le_right _ _).trans ((dyadicCapacity_bounds (U P child)).2.trans
        (Nat.mul_le_mul_left _ (units child))))
    dsimp only [event]
    rw [forestArcTierEvent_probability]
    exact div_le_div_of_nonneg_right (by exact_mod_cast upper) (by positivity)
  have constant (P : List (V × V)) (_ : P ∈ D.inits.toFinset)
      (Q : List (V × V)) (_ : Q ∈ D.inits.toFinset)
      (equal : historyProfile tier.val (U P) child = historyProfile tier.val (U Q) child) :
      event P = event Q := by
    have profile (a) (ha : a ∈ historyAncestors child) :
        historyCapacityUnits tier.val (U P) a = historyCapacityUnits tier.val (U Q) a := by
      have eq := congrFun equal ⟨a, ha⟩
      rw [← historyProfile_recovers tier.val (U P) child ⟨a, ha⟩, eq,
        historyProfile_recovers]
    ext sample
    simp only [event, mem_forestArcTierEvent, forestLegSelected]
    unfold thresholdPath
    have same (a) (ha : a ∈ historyAncestors child) :=
      historyAncestorCutoffs_eq (scale.log2 + 1) tier.val profile ha
    exact and_congr_right (fun _ =>
      ⟨fun h a ha => (same a ha) ▸ h a ha, fun h a ha => (same a ha).symm ▸ h a ha⟩)
  have count : Fintype.card J ≤ (scale.log2 + 2) ^ (height + 1) := by
    dsimp only [J]
    rw [Fintype.card_fun, Fintype.card_option, Fintype.card_fin, Fintype.card_coe]
    exact (Nat.pow_le_pow_left (by omega : tier.val + 1 + 1 ≤ scale.log2 + 2) _).trans
      (Nat.pow_le_pow_right (by omega) (historyAncestors_card_le child))
  have total := finiteProbability_biUnion_profiles_le D.inits.toFinset
    (fun P => historyProfile tier.val (U P) child) event (by positivity) bound constant
  have realBound : (Fintype.card J : ℝ) ≤ ((scale.log2 + 2 : ℕ) : ℝ) ^ (height + 1) :=
    by exact_mod_cast count
  exact total.trans (mul_le_mul_of_nonneg_right realBound (by positivity))

end ForestCosts

end OnlineReachabilityPreservers
