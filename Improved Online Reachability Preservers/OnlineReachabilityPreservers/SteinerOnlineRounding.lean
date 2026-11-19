import Mathlib.Algebra.Order.BigOperators.Expect
import OnlineReachabilityPreservers.SteinerEarlyRound
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

local instance onlineForestNetworkDecidableEq : DecidableEq (ForestNetworkVertex V height) :=
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

def earlyRoundingFactor (G : Arcs V) (height : ℕ) : ℕ :=
  let W := forestScale G height
  2 * earlyTrialCount V height * (W.log2 + 1) * (W.log2 + 2) ^ (height + 1)

private noncomputable def earlyLinkPurchaseEvent (G : Arcs V) (height : ℕ) (D : List (V × V))
    (e : HeightForestVertex V height × HeightForestVertex V height) : Finset (EarlyRoundSample G height) := by
  classical
  exact univ.filter fun sample => e ∈ earlyMetricPurchases G height D sample

private theorem earlyLinkPurchaseEvent_probability (G : Arcs V) (D : List (V × V))
    {e : HeightForestVertex V height × HeightForestVertex V height} (inside : e ∈ heightForest G height)
    (positive : 0 < heightForestWeight G e) :
    let W := forestScale G height
    let units := forestMetricUnits G (forestFractionalRun G height D).1 W e
    finiteProbability (earlyLinkPurchaseEvent G height D e) ≤
      (earlyRoundingFactor G height : ℝ) * (units : ℝ) / W := by
  classical
  let W := forestScale G height
  let T := earlyTrialCount V height
  let r := heightForestRoot e.1
  let side := roundingArcSide e
  let child := roundingArcHistory e
  let x := forestMetricUnits G (forestFractionalRun G height D).1 W e
  obtain ⟨notRoot, leg⟩ := forestPaidArc_history inside positive
  have unitEq : forestLegUnits G (forestFractionalRun G height D).1 W r side child = x :=
    congrArg (forestMetricUnits G (forestFractionalRun G height D).1 W) leg
  let tierEvent := fun tier : Fin (W.log2 + 1) => forestTierPrefixEvent G W D r side child tier
  let batch := fun i : Fin T => (univ : Finset (Fin (W.log2 + 1))).biUnion fun tier =>
    coordinatePreimage i (tierEvent tier)
  have inclusion : earlyLinkPurchaseEvent G height D e ⊆ (univ : Finset (Fin T)).biUnion batch := by
    intro sample member
    have bought : e ∈ earlyMetricPurchases G height D sample := by
      simpa [earlyLinkPurchaseEvent] using member
    obtain ⟨P, hp, chosen⟩ := mem_biUnion.mp bought
    by_cases empty : P = []
    · simp [empty] at chosen
    have selected : e ∈ earlyMetricAt G height P sample := by simpa [empty] using chosen
    obtain ⟨i, _, seen⟩ := mem_biUnion.mp selected
    have either := (mem_filter.mp seen).2
    rcases either with zero | ⟨tier, group⟩
    · exact (positive.ne' zero).elim
    refine mem_biUnion.mpr ⟨i, mem_univ _, mem_biUnion.mpr ⟨tier, mem_univ _, ?_⟩⟩
    apply mem_coordinatePreimage.mpr
    exact mem_biUnion.mpr ⟨P, hp, mem_forestArcTierEvent.mpr group⟩
  have seedPositive : 0 < forestSeedSize W := by unfold forestSeedSize; positivity
  let initial : Fin (forestSeedSize W) := ⟨0, seedPositive⟩
  have nonempty : Nonempty (ForestRoundingSample V height W) :=
    ⟨fun _ _ => ⟨initial, fun _ _ => initial⟩⟩
  let C := ((W.log2 + 2 : ℕ) : ℝ) ^ (height + 1)
  have tierBound (i : Fin T) (tier : Fin (W.log2 + 1)) :
      finiteProbability (coordinatePreimage i (tierEvent tier)) ≤
        C * (2 * (x : ℝ) / (forestSeedSize W : ℝ)) := by
    rw [finiteProbability_coordinatePreimage]
    simpa only [unitEq] using forestArcTier_anyPrefix_bound G W D r side child notRoot tier
  have oneTrial (i : Fin T) :
      finiteProbability (batch i) ≤ (W.log2 + 1 : ℝ) * (C * (2 * (x : ℝ) / (forestSeedSize W : ℝ))) := by
    apply (finiteProbability_biUnion_le _ _).trans
    calc
      _ ≤ ∑ _ : Fin (W.log2 + 1), C * (2 * (x : ℝ) / (forestSeedSize W : ℝ)) :=
        sum_le_sum fun tier _ => tierBound i tier
      _ = _ := by simp
  have size : (W : ℝ) ≤ (forestSeedSize W : ℝ) := by exact_mod_cast (Nat.lt_log2_self (n := W)).le
  refine (finiteProbability_mono inclusion).trans ((finiteProbability_biUnion_le _ _).trans ?_)
  calc
    _ ≤ ∑ _ : Fin T, (W.log2 + 1 : ℝ) * (C * (2 * (x : ℝ) / (forestSeedSize W : ℝ))) :=
      sum_le_sum fun i _ => oneTrial i
    _ = (T : ℝ) * ((W.log2 + 1 : ℝ) * (C * (2 * (x : ℝ) / (forestSeedSize W : ℝ)))) := by simp
    _ ≤ (T : ℝ) * ((W.log2 + 1 : ℝ) * (C * (2 * (x : ℝ) / W))) := by
      have ratio := div_le_div_of_nonneg_left (show 0 ≤ 2 * (x : ℝ) by positivity)
        (Nat.cast_pos.mpr (forestScale_pos G height)) size
      gcongr
    _ = _ := by simp only [earlyRoundingFactor, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
      Nat.cast_ofNat, Nat.cast_one, T, W, C, div_eq_mul_inv]; ring

private theorem earlyMetricPurchases_sub (G : Arcs V) (height : ℕ) (D : List (V × V))
    (sample : EarlyRoundSample G height) : earlyMetricPurchases G height D sample ⊆ heightForest G height := by
  intro e he
  obtain ⟨P, _, chosen⟩ := mem_biUnion.mp he
  by_cases empty : P = []
  · simp [empty] at chosen
  have seen : e ∈ earlyMetricAt G height P sample := by simpa [empty] using chosen
  exact roundedForestTrials_sub _ _ _ _ _ seen

theorem earlyMetric_weight_mean_le (G : Arcs V) (height : ℕ) (D : List (V × V)) :
    let W := forestScale G height
    let edges := forestNetworkPriced G (heightForest G height)
    let weight := forestNetworkWeight (height := height) G
    let out := forestFractionalRun G height D
    (𝔼 sample : EarlyRoundSample G height,
      ∑ e ∈ earlyMetricPurchases G height D sample, (heightForestWeight G e : ℝ)) ≤
      (earlyRoundingFactor G height : ℝ) *
        ∑ e ∈ edges, (weight e : ℝ) * ((roundedWeightedCapacity (weight e) (out.1 e) : ℝ) / W) := by
  classical
  let H := heightForest G height
  let cost := fun (e : HeightForestVertex V height × HeightForestVertex V height) =>
    (heightForestWeight G e : ℝ)
  let W := forestScale G height
  let paid := H.filter (fun e => 0 < heightForestWeight G e)
  let picked := fun (sample : EarlyRoundSample G height) (e : HeightForestVertex V height × HeightForestVertex V height) =>
    if e ∈ earlyMetricPurchases G height D sample then cost e else 0
  let units := forestMetricUnits G (forestFractionalRun G height D).1 W
  have sumOnH (sample : EarlyRoundSample G height) :
      (∑ e ∈ earlyMetricPurchases G height D sample, cost e) = ∑ e ∈ H, picked sample e := by
    rw [← Finset.sum_filter]
    have eq : H.filter (fun e => e ∈ earlyMetricPurchases G height D sample) =
        earlyMetricPurchases G height D sample := by
      ext e
      exact ⟨fun h => (mem_filter.mp h).2, fun h =>
        mem_filter.mpr ⟨earlyMetricPurchases_sub G height D sample h, h⟩⟩
    rw [eq]
  have expectation (e : HeightForestVertex V height × HeightForestVertex V height) :
      (𝔼 sample : EarlyRoundSample G height, picked sample e) =
        cost e * finiteProbability (earlyLinkPurchaseEvent G height D e) := by
    rw [Finset.expect_eq_sum_div_card]
    change (∑ sample : EarlyRoundSample G height,
        if e ∈ earlyMetricPurchases G height D sample then cost e else 0) / _ = _
    rw [← Finset.sum_filter]
    simp only [earlyLinkPurchaseEvent, finiteProbability, sum_const, nsmul_eq_mul, card_univ]
    ring
  have totalMean : (𝔼 sample : EarlyRoundSample G height,
      ∑ e ∈ earlyMetricPurchases G height D sample, cost e) =
      ∑ e ∈ H, cost e * finiteProbability (earlyLinkPurchaseEvent G height D e) := by
    simp_rw [sumOnH, Finset.expect_sum_comm, expectation]
  change (𝔼 sample : EarlyRoundSample G height,
    ∑ e ∈ earlyMetricPurchases G height D sample, cost e) ≤ _
  rw [totalMean]
  have dropZero :
      (∑ e ∈ H, cost e * finiteProbability (earlyLinkPurchaseEvent G height D e)) =
        ∑ e ∈ paid, cost e * finiteProbability (earlyLinkPurchaseEvent G height D e) := by
    rw [Finset.sum_filter]
    apply sum_congr rfl
    intro e _
    by_cases pos : 0 < heightForestWeight G e
    · simp [pos]
    have zero : heightForestWeight G e = 0 := Nat.eq_zero_of_not_pos pos
    simp [cost, zero]
  rw [dropZero]
  have step (e) (he : e ∈ paid) :
      cost e * finiteProbability (earlyLinkPurchaseEvent G height D e) ≤
        (earlyRoundingFactor G height : ℝ) * (cost e * ((units e : ℝ) / W)) := by
    obtain ⟨inside, positive⟩ := mem_filter.mp he
    have bound := earlyLinkPurchaseEvent_probability G D inside positive
    calc
      _ ≤ cost e * ((earlyRoundingFactor G height : ℝ) * (units e : ℝ) / W) :=
        mul_le_mul_of_nonneg_left bound (by dsimp [cost]; positivity)
      _ = _ := by ring
  refine (sum_le_sum step).trans_eq ?_
  rw [← Finset.mul_sum]
  change (earlyRoundingFactor G height : ℝ) * (∑ e ∈ paid, cost e * ((units e : ℝ) / W)) =
    (earlyRoundingFactor G height : ℝ) *
      ∑ e ∈ forestNetworkPriced G H, (forestNetworkWeight G e : ℝ) *
        ((roundedWeightedCapacity (forestNetworkWeight G e) ((forestFractionalRun G height D).1 e) : ℝ) / W)
  rw [forestNetworkPriced, Finset.sum_map]
  congr 1
  apply sum_congr rfl
  intro e he
  obtain ⟨inside, positive⟩ := mem_filter.mp he
  simp [units, forestMetricUnits, H, inside, positive.ne', cost, forestNetworkWeight]
  rfl

/-- Expected original edge cost of the instantiated early online
algorithm on a fixed feasible trace of distinct demands. -/
theorem earlyRoundedGraph_mean_le [Nonempty V] (G Z : Arcs V) (sub : Z ⊆ G)
    {height : ℕ} (heightPos : 0 < height) (D : List (V × V)) (distinct : D.Nodup)
    (nonempty : 0 < D.length) (feasible : ∀ d ∈ D, Reach Z d.1 d.2) :
    let W := forestScale G height
    let p := D.length
    (𝔼 sample : EarlyRoundSample G height, ((earlyRoundedGraph G height D sample).card : ℝ)) ≤
      (earlyRoundingFactor G height : ℝ) *
        (2 + ((W.log2 + 1 : ℕ) : ℝ) *
          (12 * (height : ℝ) * (p : ℝ) ^ (1 / (height : ℝ)) *
            ((Nat.sqrt p : ℝ) + 1) * (Z.card : ℝ))) + 2 := by
  classical
  let picked (sample : EarlyRoundSample G height) :=
    ∑ e ∈ earlyMetricPurchases G height D sample, (heightForestWeight G e : ℝ)
  let penalty (sample : EarlyRoundSample G height) : ℝ :=
    if sample ∈ earlyFallbackSamples G height D then G.card else 0
  have point (sample : EarlyRoundSample G height) :
      ((earlyRoundedGraph G height D sample).card : ℝ) ≤ picked sample + penalty sample := by
    by_cases fail : earlyRoundFallback G height D sample
    · have p0 : 0 ≤ picked sample := sum_nonneg (fun _ _ => by positivity)
      have h : sample ∈ earlyFallbackSamples G height D := by simpa [earlyFallbackSamples] using fail
      simp only [earlyRoundedGraph, fail, penalty, h, ↓reduceIte]
      linarith only [p0]
    · have h : sample ∉ earlyFallbackSamples G height D := by simpa [earlyFallbackSamples] using fail
      simp only [earlyRoundedGraph, fail, penalty, h, ↓reduceIte, add_zero]
      dsimp only [picked]
      exact_mod_cast expandHeightForest_cost G (earlyMetricPurchases G height D sample)
  have penaltyMean : (𝔼 sample : EarlyRoundSample G height, penalty sample) =
      (G.card : ℝ) * finiteProbability (earlyFallbackSamples G height D) := by
    rw [Finset.expect_eq_sum_div_card]
    simp only [penalty]
    rw [← Finset.sum_filter, filter_mem_eq_inter, univ_inter]
    simp only [finiteProbability, sum_const, nsmul_eq_mul, card_univ]
    ring
  have pcount : D.toFinset.card = D.length := List.toFinset_card_of_nodup distinct
  have net := (forestFractionalRun_bound G Z sub D feasible (pcount.symm ▸ nonempty) heightPos).2
  have cost := earlyMetric_weight_mean_le G height D
  have fallback := earlyFallback_expectedCost_le G heightPos D distinct
    (fun d hd => reach_mono sub (feasible d hd))
  calc
    _ ≤ (𝔼 sample : EarlyRoundSample G height, (picked sample + penalty sample)) :=
      Finset.expect_le_expect (fun sample _ => point sample)
    _ ≤ _ := by
      rw [Finset.expect_add_distrib, penaltyMean]
      refine add_le_add (cost.trans ?_) fallback
      exact mul_le_mul_of_nonneg_left (by simpa only [pcount, forestScale] using net) (by positivity)

end ForestCosts

end OnlineReachabilityPreservers
