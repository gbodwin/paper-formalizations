import Mathlib.Analysis.Complex.Exponential
import OnlineReachabilityPreservers.SteinerDyadicRounding
import OnlineReachabilityPreservers.SteinerForestFlow

/-! One trial of integral rounding for the paired metric forest. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} {height : ℕ} [LinearOrder V] [Fintype V]

local instance : DecidableEq (ForestNetworkVertex V height) :=
  (inferInstance : LinearOrder (ForestNetworkVertex V height)).toDecidableEq

def heightForestLegArc (r : V) (side : Bool) (u : HeightNode V height) :
    HeightForestVertex V height × HeightForestVertex V height :=
  if side then (heightCopy r true (heightParent u), heightCopy r true u)
  else (heightCopy r false u, heightCopy r false (heightParent u))

omit [LinearOrder V] [Fintype V] in
theorem forestLegArc_eq_map (r : V) (side : Bool) (u : HeightNode V height) :
    forestLegArc r side u = forestNetworkCopy.prodMap forestNetworkCopy (heightForestLegArc r side u) := by
  cases side <;> rfl

def roundingArcSide (e : HeightForestVertex V height × HeightForestVertex V height) : Bool :=
  heightForestSide e.1

def roundingArcHistory (e : HeightForestVertex V height × HeightForestVertex V height) : HeightNode V height :=
  if roundingArcSide e then heightForestHistory e.2 else heightForestHistory e.1

omit [LinearOrder V] [Fintype V] in
@[simp]
theorem roundingArcSide_leg (r : V) (side : Bool) (u : HeightNode V height) :
    roundingArcSide (heightForestLegArc r side u) = side := by cases side <;> rfl

omit [LinearOrder V] [Fintype V] in
@[simp]
theorem roundingArcHistory_leg (r : V) (side : Bool) (u : HeightNode V height) :
    roundingArcHistory (heightForestLegArc r side u) = u := by cases side <;> rfl

omit [LinearOrder V] [Fintype V] in
@[simp]
theorem roundingArcRoot_leg (r : V) (side : Bool) (u : HeightNode V height) :
    heightForestRoot (heightForestLegArc r side u).1 = r := by cases side <;> rfl

/-- All metric arcs have fixed initial data. Temporary terminal attachments
do not contribute to their capacities. -/
def forestMetricUnits (G : Arcs V)
    (charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ) (scale : ℕ)
    (e : HeightForestVertex V height × HeightForestVertex V height) : ℕ :=
  if e ∈ heightForest G height then
    if heightForestWeight G e = 0 then scale else
      roundedWeightedCapacity (heightForestWeight G e)
        (charges (forestNetworkCopy.prodMap forestNetworkCopy e))
  else 0

private theorem forestMetricUnits_mem {G : Arcs V}
    {charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ} {scale : ℕ}
    {e : HeightForestVertex V height × HeightForestVertex V height}
    (positive : 0 < forestMetricUnits G charges scale e) : e ∈ heightForest G height := by
  by_contra absent
  simp [forestMetricUnits, absent] at positive

theorem forestMetricUnits_eq_capacity (G : Arcs V) (d : V × V)
    (charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ) (scale : ℕ)
    (e : HeightForestVertex V height × HeightForestVertex V height) :
    (forestMetricUnits G charges scale e : ℤ) =
      weightedNetworkCapacity (forestNetworkPriced G (heightForest G height))
        (forestNetworkDemand G height d) (forestNetworkWeight G) charges scale
        (forestNetworkCopy.prodMap forestNetworkCopy e) := by
  let copy : HeightForestVertex V height ↪ ForestNetworkVertex V height := forestNetworkCopy
  let embed := copy.prodMap copy
  let f := embed e
  have noEntry : f ∉ forestNetworkEntries d.1 := by
    intro h
    obtain ⟨_, _, eq⟩ := mem_image.mp h
    have wrong : (1 : ℕ) = 0 := congrArg (fun p => (ofLex p.1).1.val) eq
    contradiction
  have noExit : f ∉ forestNetworkExits d.2 := by
    intro h
    obtain ⟨_, _, eq⟩ := mem_image.mp h
    have wrong : (2 : ℕ) = 0 := congrArg (fun p => (ofLex p.2).1.val) eq
    contradiction
  have free : f ∈ (forestNetworkDemand G height d).free ↔
      e ∈ heightForest G height ∧ heightForestWeight G e = 0 := by
    change f ∈ forestNetworkZero G height ∪ forestNetworkEntries d.1 ∪ forestNetworkExits d.2 ↔ _
    simp only [mem_union, noEntry, noExit, or_false, forestNetworkZero, mem_map, mem_filter]
    exact ⟨fun ⟨a, ha, eq⟩ => (embed.injective eq) ▸ ha, fun he => ⟨e, he, rfl⟩⟩
  have priced : f ∈ forestNetworkPriced G (heightForest G height) ↔
      e ∈ heightForest G height ∧ 0 < heightForestWeight G e := by
    simp only [forestNetworkPriced, mem_map, mem_filter]
    exact ⟨fun ⟨a, ha, eq⟩ => (embed.injective eq) ▸ ha, fun he => ⟨e, he, rfl⟩⟩
  have cost : forestNetworkWeight G f = heightForestWeight G e := rfl
  change (forestMetricUnits G charges scale e : ℤ) =
    weightedNetworkCapacity (forestNetworkPriced G (heightForest G height))
      (forestNetworkDemand G height d) (forestNetworkWeight G) charges scale f
  by_cases link : e ∈ heightForest G height
  · by_cases zero : heightForestWeight G e = 0
    · rw [weightedNetworkCapacity]
      simp [forestMetricUnits, link, zero, free]
    · have positive := Nat.pos_of_ne_zero zero
      have notFree : f ∉ (forestNetworkDemand G height d).free := fun h => zero (free.mp h).2
      have isPriced : f ∈ forestNetworkPriced G (heightForest G height) := priced.mpr ⟨link, positive⟩
      simp only [weightedNetworkCapacity, forestMetricUnits, link, zero, notFree, isPriced, cost, ↓reduceIte]
      rfl
  · rw [weightedNetworkCapacity]
    simp [forestMetricUnits, link, free, priced]

def forestLegUnits (G : Arcs V)
    (charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ) (scale : ℕ)
    (r : V) (side : Bool) (u : HeightNode V height) : ℕ :=
  forestMetricUnits G charges scale (heightForestLegArc r side u)

abbrev forestSeedSize (scale : ℕ) : ℕ := 2 ^ (scale.log2 + 1)

abbrev ForestRootSample (V : Type*) (height scale : ℕ) :=
  Fin (forestSeedSize scale) × (Bool → historySample V height (forestSeedSize scale))

abbrev ForestRoundingSample (V : Type*) (height scale : ℕ) :=
  V → Fin (scale.log2 + 1) → ForestRootSample V height scale

instance (scale : ℕ) : Fintype (ForestRoundingSample V height scale) :=
  @Pi.instFintype V (fun _ => Fin (scale.log2 + 1) → ForestRootSample V height scale)
    inferInstance inferInstance (fun _ => inferInstance)

/-- The root is activated at the scale of the current copy. Each side
then uses its independent ancestor thresholds. -/
def forestLegSelected (G : Arcs V)
    (charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ) (scale : ℕ)
    (r : V) (tier : Fin (scale.log2 + 1)) (sample : ForestRootSample V height scale)
    (side : Bool) (u : HeightNode V height) : Prop :=
  thresholdPath (forestSeedSize scale) (historyCutoff (scale.log2 + 1) tier.val
    (forestLegUnits G charges scale r side)) (historyAncestors u) (sample.2 side)

instance (G : Arcs V)
    (charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ) (scale : ℕ)
    (r : V) (tier : Fin (scale.log2 + 1)) (sample : ForestRootSample V height scale)
    (side : Bool) (u : HeightNode V height) :
    Decidable (forestLegSelected G charges scale r tier sample side u) := by
  unfold forestLegSelected
  infer_instance

/-- The metric links retained by one trial in the current fractional
state. Every root has one copy at each capacity tier. -/
def roundedForestLinks (G : Arcs V)
    (charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ) (scale : ℕ)
    (sample : ForestRoundingSample V height scale) : Arcs (HeightForestVertex V height) :=
  (heightForest G height).filter fun e => heightForestWeight G e = 0 ∨
    ∃ tier : Fin (scale.log2 + 1),
      let r := heightForestRoot e.1
      let seed := sample r tier
      seed.1.val < 2 ^ tier.val ∧
        forestLegSelected G charges scale r tier seed (roundingArcSide e) (roundingArcHistory e)

theorem roundedForestLinks_sub (G : Arcs V)
    (charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ) (scale : ℕ)
    (sample : ForestRoundingSample V height scale) :
    roundedForestLinks G charges scale sample ⊆ heightForest G height := filter_subset _ _

private theorem forestLegSelected_ancestor {G : Arcs V}
    {charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ} {scale : ℕ}
    {r : V} {tier : Fin (scale.log2 + 1)} {sample : ForestRootSample V height scale} {side : Bool}
    {u v : HeightNode V height} (selected : forestLegSelected G charges scale r tier sample side v)
    (ancestor : u.val <+: v.val) :
    forestLegSelected G charges scale r tier sample side u := by
  intro a ha
  exact selected a (mem_historyAncestors.mpr ((mem_historyAncestors.mp ha).trans ancestor))

private theorem forestLegSelected_present {G : Arcs V}
    {charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ} {scale : ℕ}
    {r : V} {tier : Fin (scale.log2 + 1)} {sample : ForestRootSample V height scale} {side : Bool}
    {u : HeightNode V height} (selected : forestLegSelected G charges scale r tier sample side u)
    (nonroot : u ≠ heightRoot) : heightForestLegArc r side u ∈ heightForest G height := by
  have own := selected u (mem_historyAncestors.mpr List.prefix_rfl)
  have cutoffPos := (Nat.zero_le _).trans_lt own
  have capPos : 0 < historyCapacityUnits tier.val (forestLegUnits G charges scale r side) u := by
    by_contra! zero
    have capZero := Nat.eq_zero_of_le_zero zero
    simp [historyCutoff, nonroot, capZero] at cutoffPos
  have capBound := historyCapacityUnits_le tier.val (forestLegUnits G charges scale r side)
    (u := u) (v := u) List.prefix_rfl
  have supply : 0 < forestLegUnits G charges scale r side u := by
    by_contra! zero
    have supplyZero := Nat.eq_zero_of_le_zero zero
    simp [rootCappedCapacity, nonroot, dyadicCapacity, supplyZero] at capBound
    omega
  exact forestMetricUnits_mem supply

private theorem forestRound_leg_arc {G : Arcs V}
    {charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ} {scale : ℕ}
    {r : V} {tier : Fin (scale.log2 + 1)} {sample : ForestRoundingSample V height scale} {side : Bool}
    {u : HeightNode V height} (nonroot : u ≠ heightRoot)
    (activated : (sample r tier).1.val < 2 ^ tier.val)
    (selected : forestLegSelected G charges scale r tier (sample r tier) side u) :
    heightForestLegArc r side u ∈ roundedForestLinks G charges scale sample := by
  have existsLink := forestLegSelected_present selected nonroot
  refine mem_filter.mpr ⟨existsLink, Or.inr ⟨tier, ?_⟩⟩
  simpa only [roundingArcRoot_leg, roundingArcSide_leg, roundingArcHistory_leg] using And.intro activated selected

private theorem forestRound_leg_reach {G : Arcs V}
    {charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ} {scale : ℕ}
    {r : V} {tier : Fin (scale.log2 + 1)} {sample : ForestRoundingSample V height scale} {side : Bool}
    {u : HeightNode V height} (activated : (sample r tier).1.val < 2 ^ tier.val)
    (selected : forestLegSelected G charges scale r tier (sample r tier) side u) :
    let links := roundedForestLinks G charges scale sample
    if side then Reach links (heightCopy r true heightRoot) (heightCopy r true u)
    else Reach links (heightCopy r false u) (heightCopy r false heightRoot) := by
  let links := roundedForestLinks G charges scale sample
  have all (k : ℕ) : ∀ v : HeightNode V height, v.val.length = k →
      forestLegSelected G charges scale r tier (sample r tier) side v →
      if side then Reach links (heightCopy r true heightRoot) (heightCopy r true v)
      else Reach links (heightCopy r false v) (heightCopy r false heightRoot) := by
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro v len vSelected
      by_cases root : v = heightRoot
      · subst v
        cases side <;> exact Relation.ReflTransGen.refl
      have positive : 0 < v.val.length :=
        List.length_pos_of_ne_nil (fun empty => root (Subtype.ext empty))
      have shorter : (heightParent v).val.length < k := by
        change v.val.dropLast.length < k
        rw [List.length_dropLast, ← len]
        omega
      have earlier := ih _ shorter (heightParent v) rfl
        (forestLegSelected_ancestor vSelected (List.dropLast_prefix _))
      have edge := forestRound_leg_arc root activated vSelected
      cases side
      · exact earlier.head edge
      · exact earlier.tail edge
  exact all _ u rfl selected

/-- When both rounded groups have a terminal at one active root, the
rounded metric links serve the original request. -/
theorem roundedForestLinks_serves {G : Arcs V}
    {charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ} {scale : ℕ}
    {r : V} {tier : Fin (scale.log2 + 1)} {sample : ForestRoundingSample V height scale} {d : V × V}
    {u v : HeightNode V height} (activated : (sample r tier).1.val < 2 ^ tier.val)
    (first : sourceLeaf d.1 (heightCopy r false u))
    (last : sinkLeaf d.2 (heightCopy r true v))
    (chooseLeft : forestLegSelected G charges scale r tier (sample r tier) false u)
    (chooseRight : forestLegSelected G charges scale r tier (sample r tier) true v) :
    heightForestServes (roundedForestLinks G charges scale sample) d := by
  let links := roundedForestLinks G charges scale sample
  have left : Reach links (heightCopy r false u) (heightCopy r false heightRoot) :=
    forestRound_leg_reach activated chooseLeft
  have right : Reach links (heightCopy r true heightRoot) (heightCopy r true v) :=
    forestRound_leg_reach activated chooseRight
  have middle : heightForestRootLink r height ∈ links := by
    apply mem_filter.mpr
    refine ⟨mem_biUnion.mpr ⟨r, mem_univ _, mem_union_right _ (mem_singleton_self _)⟩, Or.inl ?_⟩
    simp [heightForestWeight, heightForestRootLink]
  exact ⟨_, _, first, last, (left.tail middle).trans right⟩

noncomputable def forestTrialFailure (G : Arcs V)
    (charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ) (scale : ℕ)
    (d : V × V) : Finset (ForestRoundingSample V height scale) := by
  classical
  exact univ.filter fun sample => ¬ heightForestServes (roundedForestLinks G charges scale sample) d

private theorem roundedForestGroup_bound (G : Arcs V)
    (charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ) (scale : ℕ) (d : V × V)
    (loads : ForestLeafLoads d scale
      (weightedNetworkCapacity (forestNetworkPriced G (heightForest G height))
        (forestNetworkDemand G height d) (forestNetworkWeight G) charges scale))
    (r : V) (side : Bool) (tier : Fin (scale.log2 + 1)) (fits : 2 ^ tier.val ≤ loads.rootUnits r) :
    let units := forestLegUnits G charges scale r side
    let cutoff := historyCutoff (scale.log2 + 1) tier.val units
    let terminals := univ.filter (fun a : HeightNode V height => 0 < loads.leafUnits r side a)
    1 / (height + 1 : ℝ) ≤
      finiteProbability (terminals.biUnion (selectedHistoryEvent (forestSeedSize scale) cutoff)) := by
  apply dyadicHistory_group_probability (Nat.le_of_lt tier.isLt) fits _
    (loads.leafUnits r side) (loads.leaf_total r side)
  intro u notRoot
  have exactArc := forestMetricUnits_eq_capacity G d charges scale (heightForestLegArc r side u)
  rw [← forestLegArc_eq_map] at exactArc
  have bound := loads.ancestor_bound r side u (fun nil => notRoot (Subtype.ext nil))
  rw [← exactArc] at bound
  exact_mod_cast bound

/-- One trial fails on a fixed demand with probability at most the stated
constant depending only on the height. -/
theorem forestTrialFailure_bound (G : Arcs V)
    (charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ) (scale : ℕ) (d : V × V)
    (scalePositive : 0 < scale)
    (covered : weightedNetworkCovered (forestNetworkPriced G (heightForest G height))
      (forestNetworkDemand G height d) (forestNetworkWeight G) charges scale) :
    finiteProbability (forestTrialFailure G charges scale d) ≤ Real.exp (-(1 / (4 * (height + 1 : ℝ) ^ 2))) := by
  classical
  obtain ⟨loads⟩ := forestNetworkCovered_leafLoads G d charges scale covered
  let m := forestSeedSize scale
  let B : ℝ := height + 1
  have bPos : 0 < B := by dsimp [B]; positivity
  have mPos : 0 < m := by dsimp [m, forestSeedSize]; positivity
  have scalePos : (0 : ℝ) < scale := Nat.cast_pos.mpr scalePositive
  have mUpper : m ≤ 2 * scale := by
    change 2 ^ (scale.log2 + 1) ≤ 2 * scale
    rw [pow_succ, mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.log2_self_le scalePositive.ne')
  have rootUpper (r : V) : loads.rootUnits r ≤ scale := by
    have one : loads.rootUnits r ≤ ∑ s, loads.rootUnits s :=
      single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ r)
    exact one.trans_eq loads.root_total
  let tier (r : V) : Fin (scale.log2 + 1) :=
    ⟨(loads.rootUnits r).log2, Nat.lt_succ_of_le
      (by simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right (rootUpper r) (b := 2))⟩
  let leaves (r : V) (side : Bool) :=
    univ.filter (fun a : HeightNode V height => 0 < loads.leafUnits r side a)
  let group (r : V) (side : Bool) : Finset (historySample V height m) :=
    (leaves r side).biUnion (selectedHistoryEvent m
      (historyCutoff (scale.log2 + 1) (tier r).val (forestLegUnits G charges scale r side)))
  let seedEvent (r : V) : Finset (ForestRootSample V height scale) :=
    lowThreshold m (2 ^ (tier r).val) ×ˢ constrainedSamples (group r)
  let rootEvent (r : V) : Finset (Fin (scale.log2 + 1) → ForestRootSample V height scale) :=
    if 0 < loads.rootUnits r then coordinatePreimage (tier r) (seedEvent r) else ∅
  have rootProbability (r : V) : (loads.rootUnits r : ℝ) / (4 * (scale : ℝ) * B ^ 2) ≤
      finiteProbability (rootEvent r) := by
    by_cases positive : 0 < loads.rootUnits r
    · have fits : 2 ^ (tier r).val ≤ loads.rootUnits r := Nat.log2_self_le positive.ne'
      have smaller : loads.rootUnits r ≤ 2 * 2 ^ (tier r).val := by
        have hi := Nat.lt_log2_self (n := loads.rootUnits r)
        change loads.rootUnits r ≤ 2 * 2 ^ (loads.rootUnits r).log2
        rw [mul_comm, ← pow_succ]
        exact hi.le
      have rootBalance : (loads.rootUnits r : ℝ) / (4 * (scale : ℝ)) ≤
          ((2 ^ (tier r).val : ℕ) : ℝ) / m := by
        refine (div_le_div_iff₀ (by positivity) (Nat.cast_pos.mpr mPos)).mpr ?_
        have mul : (loads.rootUnits r : ℝ) * (m : ℝ) ≤
            (2 * ((2 ^ (tier r).val : ℕ) : ℝ)) * (2 * (scale : ℝ)) := by
          exact_mod_cast Nat.mul_le_mul smaller mUpper
        nlinarith only [mul]
      have sideBound (side : Bool) : 1 / B ≤ finiteProbability (group r side) :=
        roundedForestGroup_bound G charges scale d loads r side (tier r) fits
      have hitCoin : finiteProbability (lowThreshold m (2 ^ (tier r).val)) =
          ((2 ^ (tier r).val : ℕ) : ℝ) / m := by
        rw [finiteProbability, lowThreshold_card, Fintype.card_fin,
          min_eq_right (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt (tier r).isLt))]
      have liftSeed : finiteProbability (rootEvent r) = finiteProbability (seedEvent r) := by
        have nonempty : Nonempty (ForestRootSample V height scale) :=
          ⟨⟨⟨0, mPos⟩, fun _ _ => ⟨0, mPos⟩⟩⟩
        simp only [rootEvent, positive, ↓reduceIte, finiteProbability_coordinatePreimage]
      rw [liftSeed]
      dsimp only [seedEvent]
      rw [finiteProbability_product, hitCoin,
        finiteProbability_constrainedSamples, Fintype.prod_bool]
      calc
        _ = ((loads.rootUnits r : ℝ) / (4 * (scale : ℝ))) * ((1 / B) * (1 / B)) := by
          simp only [div_eq_mul_inv, mul_inv, one_mul, pow_two]
          ring
        _ ≤ _ := mul_le_mul rootBalance
          (mul_le_mul (sideBound true) (sideBound false) (by positivity) (finiteProbability_nonneg _))
          (by positivity) (by positivity)
    · have zero : loads.rootUnits r = 0 := Nat.eq_zero_of_not_pos positive
      simp [rootEvent, zero, finiteProbability]
  let missed (r : V) : Finset (Fin (scale.log2 + 1) → ForestRootSample V height scale) :=
    univ.filter fun sample => sample ∉ rootEvent r
  have contained : forestTrialFailure G charges scale d ⊆ constrainedSamples missed := by
    intro sample fails
    have fail : ¬ heightForestServes (roundedForestLinks G charges scale sample) d := by
      simpa [forestTrialFailure] using fails
    simp only [constrainedSamples, missed, mem_filter, mem_univ, true_and]
    intro r succeeds
    by_cases pos : 0 < loads.rootUnits r
    · have packaged : sample r (tier r) ∈ seedEvent r := by simpa [rootEvent, pos] using succeeds
      obtain ⟨gate, groups⟩ := mem_product.mp packaged
      have activated : (sample r (tier r)).1.val < 2 ^ (tier r).val := (mem_filter.mp gate).2
      have two : ∀ side, (sample r (tier r)).2 side ∈ group r side := by
        simpa [constrainedSamples] using groups
      obtain ⟨a, ha, left⟩ := mem_biUnion.mp (two false)
      obtain ⟨b, hb, right⟩ := mem_biUnion.mp (two true)
      have first := loads.leaf_valid r false a (mem_filter.mp ha).2
      have last := loads.leaf_valid r true b (mem_filter.mp hb).2
      exact fail (roundedForestLinks_serves activated first last
        (mem_thresholdPathsEvent.mp left) (mem_thresholdPathsEvent.mp right))
    · simp [rootEvent, pos] at succeeds
  refine (finiteProbability_mono contained).trans ?_
  rw [finiteProbability_constrainedSamples]
  have complement (r : V) : finiteProbability (missed r) = 1 - finiteProbability (rootEvent r) := by
    let S := Fin (scale.log2 + 1) → ForestRootSample V height scale
    have nonempty : Nonempty S := ⟨fun _ => ⟨⟨0, mPos⟩, fun _ _ => ⟨0, mPos⟩⟩⟩
    have pos : (0 : ℝ) < Fintype.card S := Nat.cast_pos.mpr Fintype.card_pos
    have eq := card_filter_add_card_filter_not (s := (univ : Finset S)) (fun sample => sample ∈ rootEvent r)
    have count : (missed r).card + (rootEvent r).card = Fintype.card S := by
      have onlyRoot : (univ : Finset S).filter (fun sample => sample ∈ rootEvent r) = rootEvent r := by ext x; simp
      rw [onlyRoot, card_univ] at eq
      exact (Nat.add_comm _ _).trans eq
    have cardEq : (missed r).card = Fintype.card S - (rootEvent r).card := by omega
    simp only [finiteProbability, cardEq]
    rw [Nat.cast_sub (Finset.card_le_univ _), sub_div, div_self pos.ne']
  calc
    _ ≤ ∏ r : V, Real.exp (-((loads.rootUnits r : ℝ) / (4 * (scale : ℝ) * B ^ 2))) := by
      apply prod_le_prod₀ (fun r _ => finiteProbability_nonneg _)
      intro r _
      rw [complement]
      exact (sub_le_sub_left (rootProbability r) 1).trans
        (by simpa only [sub_eq_add_neg, add_comm] using
          Real.add_one_le_exp (-((loads.rootUnits r : ℝ) / (4 * (scale : ℝ) * B ^ 2))))
    _ = _ := by
      rw [← Real.exp_sum, sum_neg_distrib, ← Finset.sum_div, ← Nat.cast_sum, loads.root_total]
      congr 2
      field_simp [scalePos.ne', bPos.ne']
      rfl

end OnlineReachabilityPreservers
