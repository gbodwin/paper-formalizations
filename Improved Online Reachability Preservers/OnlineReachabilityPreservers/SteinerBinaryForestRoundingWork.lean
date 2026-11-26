import OnlineReachabilityPreservers.SteinerBinaryWeightedUnitsWork
import OnlineReachabilityPreservers.SteinerRoundingWork

/-! Apply the stored-row forest rounding tests to the binary weighted state. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} {h : ℕ} [LinearOrder V] [Fintype V]

local instance forestRoundingVertexDecidableEq : DecidableEq (ForestNetworkVertex V h) :=
  (inferInstance : LinearOrder (ForestNetworkVertex V h)).toDecidableEq

private theorem forestMetricUnits_eq_without_attachments (G : Arcs V)
    (charges : ForestNetworkVertex V h × ForestNetworkVertex V h → ℕ) (scale : ℕ)
    (e : HeightForestVertex V h × HeightForestVertex V h) (s t : V) :
    let key := forestNetworkCopy.prodMap forestNetworkCopy e
    let network : WeightedNetworkDemand (ForestNetworkVertex V h) :=
      ⟨forestNetworkZero G h,forestNetworkSource s,forestNetworkSink t⟩
    (forestMetricUnits G charges scale e : ℤ) =
      weightedNetworkCapacity (forestNetworkPriced G (heightForest G h)) network (forestNetworkWeight G) charges scale key := by
  let key := forestNetworkCopy.prodMap forestNetworkCopy e
  have noEntry : key ∉ forestNetworkEntries s := by
    intro found
    obtain ⟨_,_,equal⟩ := Finset.mem_image.mp found
    have wrong : (1 : ℕ) = 0 := congrArg (fun p => (ofLex p.1).1.val) equal
    contradiction
  have noExit : key ∉ forestNetworkExits t := by
    intro found
    obtain ⟨_,_,equal⟩ := Finset.mem_image.mp found
    have wrong : (2 : ℕ) = 0 := congrArg (fun p => (ofLex p.2).1.val) equal
    contradiction
  rw [forestMetricUnits_eq_capacity G (s,t) charges scale e]
  change weightedNetworkCapacity _ (forestNetworkDemand G h (s,t)) _ _ _ key = _
  simp only [weightedNetworkCapacity,forestNetworkDemand,mem_union,noEntry,noExit,or_false]
  rfl

/-- Query units on a forest link using its two embedded network labels. -/
def forestBinaryUnitsWithWork (readLabel : ForestNetworkVertex V h → List Bool × ℕ)
    (free : List (List Bool × List Bool)) (ceiling : List Bool) (width scale : ℕ)
    (rows : List (BinaryWeightedPairRow (ForestNetworkVertex V h)))
    (e : HeightForestVertex V h × HeightForestVertex V h) : ℕ × ℕ :=
  let left := readLabel (forestNetworkCopy e.1)
  let right := readLabel (forestNetworkCopy e.2)
  let units := binaryWeightedUnitsAtWithWork (left.1,right.1) free ceiling width scale rows
  (units.1,left.2+right.2+units.2+8)

/-- The binary paid state reproduces the metric units clipped at scale.
The supplied free rows contain just the forest's zero-cost links. -/
theorem forestBinaryUnitsWithWork_spec (G : Arcs V)
    (charges : ForestNetworkVertex V h × ForestNetworkVertex V h → ℕ)
    (free : List (ForestNetworkVertex V h × ForestNetworkVertex V h)) (freeExact : free.toFinset = forestNetworkZero G h)
    (ceiling : List Bool) (width scale : ℕ) (ceilingValue : binaryWordValue ceiling = scale)
    (wide : max ceiling.length scale ≤ width)
    (readLabel : ForestNetworkVertex V h → List Bool × ℕ) (labelFee labels costWidth amountWidth : ℕ)
    (injective : Function.Injective (fun v => (readLabel v).1))
    (bounded : ∀ v, (readLabel v).1.length ≤ labels) (labelWork : ∀ v, (readLabel v).2 ≤ labelFee)
    (rows : List (BinaryWeightedPairRow (ForestNetworkVertex V h))) (complete : ∀ key, key ∈ rows.map BinaryWeightedPairRow.arc)
    (encoded : ∀ row ∈ rows, row.Encodes (forestNetworkPriced G (heightForest G h)) (forestNetworkWeight G)
      charges (fun v => (readLabel v).1) costWidth amountWidth)
    (e : HeightForestVertex V h × HeightForestVertex V h) :
    let code := fun v => (readLabel v).1
    let out := forestBinaryUnitsWithWork readLabel (binaryEncodeArcs code free) ceiling width scale rows e
    out.1 = min (forestMetricUnits G charges scale e) scale ∧
    out.2 ≤ 2*labelFee+binaryWeightedUnitsAtWorkBudget rows.length free.length labels costWidth amountWidth width scale+8 := by
  let paid := forestNetworkPriced G (heightForest G h)
  let key := forestNetworkCopy.prodMap forestNetworkCopy e
  let code := fun v => (readLabel v).1
  let s := heightForestRoot e.1
  let t := heightForestRoot e.2
  let out := binaryWeightedUnitsAtWithWork (code key.1,code key.2) (binaryEncodeArcs code free) ceiling width scale rows
  obtain ⟨units,work⟩ := binaryWeightedUnitsAtWithWork_spec paid (forestNetworkWeight G) charges
    (forestNetworkPriced_positive G _) free (forestNetworkSource s) (forestNetworkSink t) scale ceiling ceilingValue
    code injective labels costWidth amountWidth width bounded wide rows key (complete key) encoded
  have exactUnits := forestMetricUnits_eq_without_attachments G charges scale e s t
  change (out.1 : ℤ) = min (weightedNetworkCapacity paid ⟨free.toFinset,_,_⟩ (forestNetworkWeight G) charges scale key) _ at units
  rw [freeExact,← exactUnits] at units
  have equal : out.1 = min (forestMetricUnits G charges scale e) scale := by
    exact_mod_cast units
  have leftWork := labelWork key.1
  have rightWork := labelWork key.2
  refine ⟨equal,?_⟩
  change (readLabel key.1).2+(readLabel key.2).2+out.2+8 ≤ _
  change out.2 ≤ _ at work
  omega

/-- Share a binary unit reader across all reached tiers and trials. -/
def roundedForestTrialsFromBinaryStateWithWork
    (links : {es : List (HeightForestVertex V h × HeightForestVertex V h) // es.Nodup})
    (weight : HeightForestVertex V h × HeightForestVertex V h → ℕ × ℕ)
    (readLabel : ForestNetworkVertex V h → List Bool × ℕ) (free : List (List Bool × List Bool))
    (ceiling : List Bool) (width scale trials : ℕ)
    (rows : List (BinaryWeightedPairRow (ForestNetworkVertex V h)))
    (sample : ForestTrialArrayWithSeedWork V h scale trials) : Arcs (HeightForestVertex V h) × ℕ × ℕ :=
  roundedForestTrialsFromUnitRowsWithWordWork links weight
    (forestBinaryUnitsWithWork readLabel free ceiling width scale rows) scale trials sample

/-- Reading the binary state gives the same rounded forest as the charge
function. Clipping is invisible to the tests in every possible tier. -/
theorem roundedForestTrialsFromBinaryStateWithWork_refines (G : Arcs V)
    (links : {es : List (HeightForestVertex V h × HeightForestVertex V h) // es.Nodup})
    (linksExact : links.val.toFinset = heightForest G h)
    (weight : HeightForestVertex V h × HeightForestVertex V h → ℕ × ℕ) (weightFee : ℕ)
    (weights : ∀ e, (weight e).1 = heightForestWeight G e) (weightWork : ∀ e, (weight e).2 ≤ weightFee)
    (charges : ForestNetworkVertex V h × ForestNetworkVertex V h → ℕ)
    (free : List (ForestNetworkVertex V h × ForestNetworkVertex V h)) (freeExact : free.toFinset = forestNetworkZero G h)
    (ceiling : List Bool) (width scale trials : ℕ) (scalePos : 0 < scale)
    (ceilingValue : binaryWordValue ceiling = scale) (wide : max ceiling.length scale ≤ width)
    (readLabel : ForestNetworkVertex V h → List Bool × ℕ) (labelFee labels costWidth amountWidth : ℕ)
    (injective : Function.Injective (fun v => (readLabel v).1))
    (bounded : ∀ v, (readLabel v).1.length ≤ labels) (labelWork : ∀ v, (readLabel v).2 ≤ labelFee)
    (rows : List (BinaryWeightedPairRow (ForestNetworkVertex V h))) (complete : ∀ key, key ∈ rows.map BinaryWeightedPairRow.arc)
    (encoded : ∀ row ∈ rows, row.Encodes (forestNetworkPriced G (heightForest G h)) (forestNetworkWeight G)
      charges (fun v => (readLabel v).1) costWidth amountWidth)
    (sample : ForestTrialArrayWithSeedWork V h scale trials) (seedFee : ℕ)
    (seedWork : ∀ i, forestSampleWorkBound (sample i) seedFee) :
    let code := fun v => (readLabel v).1
    let out := roundedForestTrialsFromBinaryStateWithWork links weight readLabel (binaryEncodeArcs code free)
      ceiling width scale trials rows sample
    let unitFee := 2*labelFee+binaryWeightedUnitsAtWorkBudget rows.length free.length labels costWidth amountWidth width scale+8
    out.1 = roundedForestTrials G charges scale trials (fun i => forestRoundingSampleValues scale (sample i)) ∧
    out.2.1 ≤ forestUnitTrialRowsWordBudget h scale trials (heightForest G h).card weightFee unitFee ∧
    out.2.2 ≤ trials*((heightForest G h).card*((scale.log2+1)*((h+2)*seedFee))) := by
  let code := fun v => (readLabel v).1
  let units := forestBinaryUnitsWithWork readLabel (binaryEncodeArcs code free) ceiling width scale rows
  let reference := forestMetricUnits G charges scale
  have correct (e : HeightForestVertex V h × HeightForestVertex V h) :=
    forestBinaryUnitsWithWork_spec G charges free freeExact ceiling width scale ceilingValue wide
      readLabel labelFee labels costWidth amountWidth injective bounded labelWork rows complete encoded e
  have cutoff (root : V) (side : Bool) (tier : Fin (scale.log2+1)) (node : HeightNode V h) :
      historyCutoff (scale.log2+1) tier.val (fun a => (units (heightForestLegArc root side a)).1) node =
        historyCutoff (scale.log2+1) tier.val (fun a => reference (heightForestLegArc root side a)) node := by
    have tierLe : 2^tier.val ≤ scale :=
      (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (Nat.le_of_lt_succ tier.isLt)).trans
        (Nat.log2_self_le scalePos.ne')
    have values : (fun a => (units (heightForestLegArc root side a)).1) =
        (fun a => min (reference (heightForestLegArc root side a)) scale) :=
      funext fun a => (correct (heightForestLegArc root side a)).1
    rw [values]
    exact historyCutoff_clip_units _ _ _ tierLe _ _
  obtain ⟨graph,work,reads⟩ := roundedForestTrialsFromUnitRowsWithWordWork_refines (heightForest G h) links
    linksExact weight units reference scale trials sample weightFee _ seedFee weightWork (fun e => (correct e).2) seedWork cutoff
  refine ⟨graph.trans ?_,work,reads⟩
  rw [funext weights]
  rfl

end OnlineReachabilityPreservers
