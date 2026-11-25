import OnlineReachabilityPreservers.SteinerEarlyRound

/-! Count weight lookups in finite rounding trials, including ancestor minima and threshold tests. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [DecidableEq V] [Fintype V] {height : ℕ}

private def rowWithWork {I A : Type*} (f : I → A × ℕ) : I ↪ I × (A × ℕ) :=
  ⟨fun v => (v,f v),fun _ _ equal => congrArg Prod.fst equal⟩

private theorem rowWork_le {I A : Type*} (s : Finset I) (f : I → A × ℕ) (B : ℕ)
    (each : ∀ x ∈ s, (f x).2 ≤ B) :
    (∑ r ∈ s.map (rowWithWork f), r.2.2) ≤ s.card*B := by
  rw [sum_map]
  calc
    _ ≤ ∑ _ ∈ s, B := sum_le_sum each
    _ = _ := by simp

private def rootCappedCapacityWithWork (tier : ℕ) (units : HeightNode V height → ℕ × ℕ)
    (v : HeightNode V height) : ℕ × ℕ :=
  if v = heightRoot then (2^tier,0)
  else
    let amount := units v
    (min (2^tier) (dyadicCapacity amount.1),amount.2)

omit [Fintype V] in
private theorem rootCappedCapacityWithWork_spec (tier : ℕ) (units : HeightNode V height → ℕ × ℕ)
    (B : ℕ) (cap : ∀ v, (units v).2 ≤ B) (v : HeightNode V height) :
    let out := rootCappedCapacityWithWork tier units v
    out.1 = rootCappedCapacity tier (fun a => (units a).1) v ∧ out.2 ≤ B := by
  by_cases root : v = heightRoot
  · simp [rootCappedCapacityWithWork,rootCappedCapacity,root]
  · simpa [rootCappedCapacityWithWork,rootCappedCapacity,root] using cap v

/-- Compute the ancestor minimum from one cached row per ancestor. -/
def historyCapacityWithWork (tier : ℕ) (units : HeightNode V height → ℕ × ℕ)
    (v : HeightNode V height) : ℕ × ℕ :=
  let source := historyAncestors v
  let row := rowWithWork (rootCappedCapacityWithWork tier units)
  let results := source.map row
  have present : v ∈ source := mem_historyAncestors.mpr List.prefix_rfl
  (results.inf' ⟨row v,mem_map_of_mem _ present⟩ (fun e => e.2.1),∑ e ∈ results, e.2.2)

theorem historyCapacityWithWork_spec (tier : ℕ) (units : HeightNode V height → ℕ × ℕ)
    (B : ℕ) (bound : ∀ v, (units v).2 ≤ B) (v : HeightNode V height) :
    let out := historyCapacityWithWork tier units v
    out.1 = historyCapacityUnits tier (fun a => (units a).1) v ∧
      out.2 ≤ (height+1)*B := by
  let S := historyAncestors v
  let row := rowWithWork (rootCappedCapacityWithWork tier units)
  let values := S.map row
  have rowSpec (a : HeightNode V height) := rootCappedCapacityWithWork_spec tier units B bound a
  have value : (historyCapacityWithWork tier units v).1 =
      historyCapacityUnits tier (fun a => (units a).1) v := by
    have fixed : S.Nonempty := ⟨v,mem_historyAncestors.mpr List.prefix_rfl⟩
    have mapped : values.Nonempty := fixed.map
    let read (r : HeightNode V height × (ℕ × ℕ)) := r.2.1
    change values.inf' mapped read = S.inf' fixed (rootCappedCapacity tier (fun a => (units a).1))
    calc
      _ = S.inf' fixed (read ∘ row) := Finset.inf'_map read mapped
      _ = _ := congrArg (S.inf' fixed) (funext fun a => (rowSpec a).1)
  refine ⟨value,?_⟩
  simpa only [historyCapacityWithWork] using (rowWork_le S (rootCappedCapacityWithWork tier units) B
    (fun a _ => (rowSpec a).2)).trans (Nat.mul_le_mul_right B (historyAncestors_card_le v))

/-- The two ancestor minima are evaluated once each. -/
def historyCutoffWithWork (sampleTier tier : ℕ) (units : HeightNode V height → ℕ × ℕ)
    (v : HeightNode V height) : ℕ × ℕ :=
  if v = heightRoot then (2^sampleTier,0)
  else
    let top := historyCapacityWithWork tier units v
    let bottom := historyCapacityWithWork tier units (heightParent v)
    (2^sampleTier * top.1 / bottom.1,top.2+bottom.2)

theorem historyCutoffWithWork_spec (sampleTier tier : ℕ) (units : HeightNode V height → ℕ × ℕ)
    (B : ℕ) (bound : ∀ v, (units v).2 ≤ B) (v : HeightNode V height) :
    let out := historyCutoffWithWork sampleTier tier units v
    out.1 = historyCutoff sampleTier tier (fun a => (units a).1) v ∧
      out.2 ≤ 2*(height+1)*B := by
  by_cases root : v = heightRoot
  · simp [historyCutoffWithWork,historyCutoff,root]
  · obtain ⟨top,up⟩ := historyCapacityWithWork_spec tier units B bound v
    obtain ⟨bottom,down⟩ := historyCapacityWithWork_spec tier units B bound (heightParent v)
    simp only [historyCutoffWithWork,historyCutoff,root,ite_false,top,bottom,true_and]
    exact (Nat.add_le_add up down).trans_eq (by ring)

private def finiteAllWithWork {I : Type*} (checks : I → Bool × ℕ) (s : Finset I) : Bool × ℕ :=
  let rows := s.map (rowWithWork checks)
  (decide (¬ (rows.filter fun r => r.2.1 = false).Nonempty),∑ r ∈ rows, r.2.2)

private theorem finiteAllWithWork_spec {I : Type*} (checks : I → Bool × ℕ) (s : Finset I) (B : ℕ)
    (cap : ∀ i ∈ s, (checks i).2 ≤ B) :
    let out := finiteAllWithWork checks s
    (out.1 = true ↔ ∀ i ∈ s, (checks i).1 = true) ∧ out.2 ≤ s.card*B := by
  refine ⟨?_,rowWork_le s checks B cap⟩
  simp only [finiteAllWithWork,decide_eq_true_eq]
  constructor
  · intro no i hi
    by_contra bad
    have flag : (checks i).1 = false := Bool.eq_false_of_not_eq_true bad
    exact no ⟨rowWithWork checks i,mem_filter.mpr ⟨mem_map_of_mem _ hi,flag⟩⟩
  · rintro all ⟨r,hr⟩
    obtain ⟨present,flag⟩ := mem_filter.mp hr
    obtain ⟨i,hi,rfl⟩ := mem_map.mp present
    exact Bool.noConfusion (flag.symm.trans (all i hi))

/-- Check every ancestor using one metered cutoff computation. -/
def thresholdPathWithWork (m : ℕ) (cutoff : HeightNode V height → ℕ × ℕ)
    (ancestors : Finset (HeightNode V height)) (sample : historySample V height m) : Bool × ℕ :=
  finiteAllWithWork (fun a => let c := cutoff a; (decide ((sample a).val < c.1),c.2)) ancestors

omit [Fintype V] [DecidableEq V] in
theorem thresholdPathWithWork_spec (m : ℕ) (cutoff : HeightNode V height → ℕ × ℕ)
    (ancestors : Finset (HeightNode V height)) (sample : historySample V height m)
    (B : ℕ) (cap : ∀ a ∈ ancestors, (cutoff a).2 ≤ B) :
    let out := thresholdPathWithWork m cutoff ancestors sample
    (out.1 = true ↔ thresholdPath m (fun a => (cutoff a).1) ancestors sample) ∧
      out.2 ≤ ancestors.card*B := by
  simpa only [thresholdPathWithWork,thresholdPath,decide_eq_true_eq] using
    finiteAllWithWork_spec (fun a => let c := cutoff a; (decide ((sample a).val < c.1),c.2)) ancestors B cap

/-- Evaluate all ancestor cutoffs for one rounded tree leg. -/
def historyLegWithWork (sampleTier tier : ℕ) (units : HeightNode V height → ℕ × ℕ)
    (sample : historySample V height (2^sampleTier)) (v : HeightNode V height) : Bool × ℕ :=
  thresholdPathWithWork _ (historyCutoffWithWork sampleTier tier units) (historyAncestors v) sample

theorem historyLegWithWork_spec (sampleTier tier : ℕ) (units : HeightNode V height → ℕ × ℕ)
    (B : ℕ) (cap : ∀ a, (units a).2 ≤ B)
    (sample : historySample V height (2^sampleTier)) (v : HeightNode V height) :
    let H := height+1
    let out := historyLegWithWork sampleTier tier units sample v
    (out.1 = true ↔ thresholdPath _ (historyCutoff sampleTier tier (fun a => (units a).1))
      (historyAncestors v) sample) ∧ out.2 ≤ 2*H^2*B := by
  let H := height+1
  let cutoff := historyCutoffWithWork sampleTier tier units
  let anc := historyAncestors v
  have each (a : HeightNode V height) := historyCutoffWithWork_spec sampleTier tier units B cap a
  obtain ⟨chosen, work⟩ := thresholdPathWithWork_spec _ cutoff anc sample (2*H*B) (fun a _ => (each a).2)
  have exactValues : (fun a => (cutoff a).1) = historyCutoff sampleTier tier (fun a => (units a).1) :=
    funext fun a => (each a).1
  refine ⟨exactValues ▸ chosen,work.trans ?_⟩
  calc
    _ ≤ H*(2*H*B) := Nat.mul_le_mul_right _ (historyAncestors_card_le v)
    _ = _ := by ring


private def finiteAnyWithWork {I : Type*} (checks : I → Bool × ℕ) (s : Finset I) : Bool × ℕ :=
  let all := finiteAllWithWork (fun i => let row := checks i; (!row.1,row.2)) s
  (!all.1,all.2)

private theorem finiteAnyWithWork_spec {I : Type*} (checks : I → Bool × ℕ) (s : Finset I) (B : ℕ)
    (cap : ∀ i ∈ s, (checks i).2 ≤ B) :
    let out := finiteAnyWithWork checks s
    (out.1 = true ↔ ∃ i ∈ s, (checks i).1 = true) ∧ out.2 ≤ s.card*B := by
  let negated := fun i => let row := checks i; (!row.1,row.2)
  obtain ⟨value, cost⟩ := finiteAllWithWork_spec negated s B cap
  refine ⟨?_,cost⟩
  change (!(finiteAllWithWork negated s).1) = true ↔ _
  have no : (finiteAllWithWork negated s).1 = false ↔ ¬ (finiteAllWithWork negated s).1 = true := by
    cases (finiteAllWithWork negated s).1 <;> simp
  rw [Bool.not_eq_true', no, value]
  simp only [negated, Bool.not_eq_true', not_forall, exists_prop]
  exact exists_congr (fun i => and_congr_right fun _ => by cases (checks i).1 <;> simp)

section Forest

variable {W : Type*} [LinearOrder W] [Fintype W] {h : ℕ}

private def forestUnitsFromWeights (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale : ℕ)
    (edge : HeightForestVertex W h × HeightForestVertex W h) : ℕ :=
  if edge ∈ links then
    let cost := weight edge
    if cost = 0 then scale
    else roundedWeightedCapacity cost (charges (forestNetworkCopy.prodMap forestNetworkCopy edge))
  else 0

private def roundedForestLinksFromWeights (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale : ℕ)
    (sample : ForestRoundingSample W h scale) : Arcs (HeightForestVertex W h) :=
  let units := forestUnitsFromWeights links weight charges scale
  links.filter fun e => weight e = 0 ∨
    ∃ tier : Fin (scale.log2+1),
      let root := heightForestRoot e.1
      let seed := sample root tier
      let side := roundingArcSide e
      let hist := roundingArcHistory e
      seed.1.val < 2^tier.val ∧
        thresholdPath (forestSeedSize scale) (historyCutoff (scale.log2+1) tier.val
          (fun u => units (heightForestLegArc root side u))) (historyAncestors hist) (seed.2 side)

/-- All trials share the stored forest and hop values. -/
def roundedForestTrialsFromWeights (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale trials : ℕ)
    (sample : ForestTrialArray W h scale trials) : Arcs (HeightForestVertex W h) :=
  univ.biUnion fun i => roundedForestLinksFromWeights links weight charges scale (sample i)

private def forestUnitsWithWork (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale : ℕ)
    (edge : HeightForestVertex W h × HeightForestVertex W h) : ℕ × ℕ :=
  if edge ∈ links then
    let cost := weight edge
    (if cost.1 = 0 then scale else roundedWeightedCapacity cost.1
      (charges (forestNetworkCopy.prodMap forestNetworkCopy edge)),cost.2)
  else (0,0)

omit [Fintype W] in
private theorem forestUnitsWithWork_le (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale B : ℕ)
    (bound : ∀ e, (weight e).2 ≤ B) (edge : HeightForestVertex W h × HeightForestVertex W h) :
    (forestUnitsWithWork links weight charges scale edge).2 ≤ B := by
  unfold forestUnitsWithWork
  split
  · exact bound edge
  · exact Nat.zero_le B

private def roundedForestTierWithWork
    (units : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (scale : ℕ) (sample : ForestRoundingSample W h scale)
    (e : HeightForestVertex W h × HeightForestVertex W h) (tier : Fin (scale.log2+1)) : Bool × ℕ :=
  let root := heightForestRoot e.1
  let seed := sample root tier
  let side := roundingArcSide e
  let hist := roundingArcHistory e
  if seed.1.val < 2^tier.val then
    historyLegWithWork (scale.log2+1) tier.val (fun u => units (heightForestLegArc root side u)) (seed.2 side) hist
  else (false,0)

private theorem roundedForestTierWithWork_spec
    (units : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (scale B : ℕ) (bound : ∀ e, (units e).2 ≤ B) (sample : ForestRoundingSample W h scale)
    (e : HeightForestVertex W h × HeightForestVertex W h) (tier : Fin (scale.log2+1)) :
    let out := roundedForestTierWithWork units scale sample e tier
    let root := heightForestRoot e.1
    let seed := sample root tier
    let side := roundingArcSide e
    let hist := roundingArcHistory e
    (out.1 = true ↔ seed.1.val < 2^tier.val ∧
      thresholdPath (forestSeedSize scale) (historyCutoff (scale.log2+1) tier.val
        (fun u => (units (heightForestLegArc root side u)).1)) (historyAncestors hist) (seed.2 side)) ∧
      out.2 ≤ 2*(h+1)^2*B := by
  let root := heightForestRoot e.1
  let seed := sample root tier
  let side := roundingArcSide e
  let hist := roundingArcHistory e
  by_cases chosen : seed.1.val < 2^tier.val
  · simpa only [roundedForestTierWithWork, root, seed, side, hist, chosen, ite_true, true_and] using
      historyLegWithWork_spec (scale.log2+1) tier.val (fun u => units (heightForestLegArc root side u))
        B (fun u => bound (heightForestLegArc root side u)) (seed.2 side) hist
  · simp [roundedForestTierWithWork, root, seed, chosen]

private def roundedForestLinkWithWork (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale : ℕ)
    (sample : ForestRoundingSample W h scale) (e : HeightForestVertex W h × HeightForestVertex W h) : Bool × ℕ :=
  let cost := weight e
  if cost.1 = 0 then (true,cost.2)
  else
    let units := forestUnitsWithWork links weight charges scale
    let selected := finiteAnyWithWork (roundedForestTierWithWork units scale sample e) univ
    (selected.1,cost.2+selected.2)

private theorem roundedForestLinkWithWork_spec (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale B : ℕ)
    (bound : ∀ e, (weight e).2 ≤ B) (sample : ForestRoundingSample W h scale)
    (e : HeightForestVertex W h × HeightForestVertex W h) :
    let out := roundedForestLinkWithWork links weight charges scale sample e
    let units := forestUnitsWithWork links weight charges scale
    (out.1 = true ↔ (weight e).1 = 0 ∨ ∃ tier : Fin (scale.log2+1),
      let root := heightForestRoot e.1
      let seed := sample root tier
      let side := roundingArcSide e
      let hist := roundingArcHistory e
      seed.1.val < 2^tier.val ∧
        thresholdPath (forestSeedSize scale) (historyCutoff (scale.log2+1) tier.val
          (fun u => (units (heightForestLegArc root side u)).1)) (historyAncestors hist) (seed.2 side)) ∧
    out.2 ≤ (1+(scale.log2+1)*(2*(h+1)^2))*B := by
  let units := forestUnitsWithWork links weight charges scale
  let checked := roundedForestTierWithWork units scale sample e
  have tierCap (t : Fin (scale.log2+1)) := roundedForestTierWithWork_spec units scale B
    (forestUnitsWithWork_le links weight charges scale B bound) sample e t
  by_cases free : (weight e).1 = 0
  · simp only [roundedForestLinkWithWork,free,ite_true,true_or,true_and]
    exact (bound e).trans (Nat.le_mul_of_pos_left _ (by omega))
  · obtain ⟨chosen,work⟩ := finiteAnyWithWork_spec checked univ (2*(h+1)^2*B) (fun t _ => (tierCap t).2)
    simp only [roundedForestLinkWithWork, free, ite_false, false_or]
    refine ⟨?_,?_⟩
    · rw [chosen]
      simpa only [mem_univ, true_and] using exists_congr (fun tier => (tierCap tier).1)
    · calc
        _ ≤ B+(scale.log2+1)*(2*(h+1)^2*B) := Nat.add_le_add (bound e) (by simpa only [card_univ,Fintype.card_fin] using work)
        _ = _ := by ring


omit [Fintype W] in
private theorem forestUnitsWithWork_eq (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale : ℕ) :
    (fun e => (forestUnitsWithWork links weight charges scale e).1) =
      forestUnitsFromWeights links (fun e => (weight e).1) charges scale := by
  funext e
  by_cases present : e ∈ links
  · by_cases free : (weight e).1 = 0 <;> simp [forestUnitsWithWork, forestUnitsFromWeights, present, free]
  · simp [forestUnitsWithWork, forestUnitsFromWeights, present]

private def roundedForestLinksWithWork (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale : ℕ)
    (sample : ForestRoundingSample W h scale) : Arcs (HeightForestVertex W h) × ℕ :=
  let rows := links.map (rowWithWork (roundedForestLinkWithWork links weight charges scale sample))
  ((rows.filter fun r => r.2.1 = true).image Prod.fst,∑ r ∈ rows, r.2.2)

private theorem roundedForestLinksWithWork_spec (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale B : ℕ)
    (bound : ∀ e, (weight e).2 ≤ B) (sample : ForestRoundingSample W h scale) :
    let out := roundedForestLinksWithWork links weight charges scale sample
    out.1 = roundedForestLinksFromWeights links (fun e => (weight e).1) charges scale sample ∧
      out.2 ≤ links.card*((1+(scale.log2+1)*(2*(h+1)^2))*B) := by
  let checks := roundedForestLinkWithWork links weight charges scale sample
  let row := rowWithWork checks
  let rows := links.map row
  have details (e : HeightForestVertex W h × HeightForestVertex W h) :=
    roundedForestLinkWithWork_spec links weight charges scale B bound sample e
  refine ⟨?_,rowWork_le links checks _ (fun e _ => (details e).2)⟩
  ext e
  let units := forestUnitsFromWeights links (fun e => (weight e).1) charges scale
  let allowed := fun e : HeightForestVertex W h × HeightForestVertex W h =>
    (weight e).1 = 0 ∨ ∃ tier : Fin (scale.log2+1),
      let root := heightForestRoot e.1
      let seed := sample root tier
      let side := roundingArcSide e
      let hist := roundingArcHistory e
      seed.1.val < 2^tier.val ∧
        thresholdPath (forestSeedSize scale) (historyCutoff (scale.log2+1) tier.val
          (fun u => units (heightForestLegArc root side u))) (historyAncestors hist) (seed.2 side)
  have selected (a : HeightForestVertex W h × HeightForestVertex W h) :
      (checks a).1 = true ↔ allowed a := by
    have spec := (details a).1
    dsimp only at spec
    simpa only [checks, allowed, units, congrFun (forestUnitsWithWork_eq links weight charges scale)] using spec
  change e ∈ (rows.filter fun r => r.2.1 = true).image Prod.fst ↔ e ∈ links.filter allowed
  constructor
  · intro he
    obtain ⟨result,present,rfl⟩ := mem_image.mp he
    obtain ⟨inside,pass⟩ := mem_filter.mp present
    obtain ⟨a,ha,rfl⟩ := mem_map.mp inside
    exact mem_filter.mpr ⟨ha,(selected a).mp pass⟩
  · intro he
    obtain ⟨inside, pass⟩ := mem_filter.mp he
    exact mem_image.mpr ⟨row e,mem_filter.mpr ⟨mem_map_of_mem _ inside,(selected e).mpr pass⟩,rfl⟩

/-- Count original weight reads over the rounded links in every trial. Each
trial's graph and measured work are computed together. -/
def roundedForestTrialsWithWork (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale trials : ℕ)
    (sample : ForestTrialArray W h scale trials) : Arcs (HeightForestVertex W h) × ℕ :=
  let evaluate := fun i => roundedForestLinksWithWork links weight charges scale (sample i)
  let rows := univ.map (rowWithWork evaluate)
  (rows.biUnion (fun r => r.2.1),∑ r ∈ rows, r.2.2)

theorem roundedForestTrialsWithWork_spec (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale trials B : ℕ)
    (bound : ∀ e, (weight e).2 ≤ B) (sample : ForestTrialArray W h scale trials) :
    let out := roundedForestTrialsWithWork links weight charges scale trials sample
    out.1 = roundedForestTrialsFromWeights links (fun e => (weight e).1) charges scale trials sample ∧
      out.2 ≤ trials*(links.card*((1+(scale.log2+1)*(2*(h+1)^2))*B)) := by
  let evaluate := fun i => roundedForestLinksWithWork links weight charges scale (sample i)
  let row := rowWithWork evaluate
  let rows := univ.map row
  have each (i : Fin trials) := roundedForestLinksWithWork_spec links weight charges scale B bound (sample i)
  refine ⟨?_,?_⟩
  · ext e
    change e ∈ rows.biUnion (fun r => r.2.1) ↔
      e ∈ univ.biUnion (fun i => roundedForestLinksFromWeights links (fun e => (weight e).1) charges scale (sample i))
    constructor
    · intro he
      obtain ⟨result,present,contains⟩ := mem_biUnion.mp he
      obtain ⟨i,_,rfl⟩ := mem_map.mp present
      exact mem_biUnion.mpr ⟨i, mem_univ _, (each i).1 ▸ contains⟩
    · intro he
      obtain ⟨i,_,contains⟩ := mem_biUnion.mp he
      exact mem_biUnion.mpr ⟨row i,mem_map_of_mem _ (mem_univ i),(each i).1.symm ▸ contains⟩
  · simpa only [roundedForestTrialsWithWork,card_univ,Fintype.card_fin] using
      rowWork_le univ evaluate _ (fun i _ => (each i).2)

/-! Count seed reads separately from the existing weight reads. -/

private def rowWithSeedReads {I A : Type*} (f : I → A × ℕ × ℕ) : I ↪ I × (A × ℕ × ℕ) :=
  ⟨fun i => (i,f i),fun _ _ same => congrArg Prod.fst same⟩

private theorem rowSeedReads_le {I A : Type*} (s : Finset I) (f : I → A × ℕ × ℕ) (B : ℕ)
    (each : ∀ i ∈ s, (f i).2.2 ≤ B) :
    (∑ row ∈ s.map (rowWithSeedReads f), row.2.2.2) ≤ s.card*B := by
  rw [sum_map]
  calc
    _ ≤ ∑ _ ∈ s, B := sum_le_sum each
    _ = _ := by simp

private def finiteAnyWithSeedReads {I : Type*} (checks : I → Bool × ℕ × ℕ) (s : Finset I) : Bool × ℕ × ℕ :=
  let rows := s.map (rowWithSeedReads checks)
  (decide ((rows.filter fun r => r.2.1 = true).Nonempty),∑ r ∈ rows, r.2.2.1,∑ r ∈ rows, r.2.2.2)

private theorem finiteAnyWithSeedReads_spec {I : Type*} (checks : I → Bool × ℕ × ℕ)
    (s : Finset I) (B : ℕ) (cap : ∀ i ∈ s, (checks i).2.2 ≤ B) :
    let out := finiteAnyWithSeedReads checks s
    (out.1,out.2.1) = finiteAnyWithWork (fun i => ((checks i).1,(checks i).2.1)) s ∧
      out.2.2 ≤ s.card*B := by
  let rows := s.map (rowWithSeedReads checks)
  let projection := fun i => ((checks i).1,(checks i).2.1)
  have newHasOne : (finiteAnyWithSeedReads checks s).1 = true ↔ ∃ i ∈ s, (checks i).1 = true := by
    change decide ((rows.filter fun r => r.2.1 = true).Nonempty) = true ↔ _
    rw [decide_eq_true_eq]
    constructor
    · rintro ⟨r, member⟩
      obtain ⟨packed,flag⟩ := mem_filter.mp member
      obtain ⟨i,inside,rfl⟩ := mem_map.mp packed
      exact ⟨i,inside,flag⟩
    · rintro ⟨i,inside,flag⟩
      exact ⟨rowWithSeedReads checks i,mem_filter.mpr ⟨mem_map_of_mem _ inside,flag⟩⟩
  have oldHasOne := (finiteAnyWithWork_spec projection s (∑ i ∈ s, (checks i).2.1)
    (fun i mem => single_le_sum (f := fun j => (checks j).2.1) (fun _ _ => zero_le) mem)).1
  refine ⟨Prod.ext (Bool.eq_iff_iff.mpr (newHasOne.trans oldHasOne.symm)) ?_,rowSeedReads_le s checks B cap⟩
  dsimp only [finiteAnyWithSeedReads,finiteAnyWithWork,finiteAllWithWork]
  rw [sum_map,sum_map]
  rfl

private def roundedForestTierWithSeedReads
    (units : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (scale : ℕ) (sample : ForestRoundingSample W h scale)
    (e : HeightForestVertex W h × HeightForestVertex W h) (tier : Fin (scale.log2+1)) : Bool × ℕ × ℕ :=
  let root := heightForestRoot e.1
  let seed := sample root tier
  let side := roundingArcSide e
  let hist := roundingArcHistory e
  if seed.1.val < 2^tier.val then
    let ancestors := historyAncestors hist
    let cutoffs := historyCutoffWithWork (scale.log2+1) tier.val (fun u => units (heightForestLegArc root side u))
    let chosen := thresholdPathWithWork _ cutoffs ancestors (seed.2 side)
    (chosen.1,chosen.2,1+ancestors.card)
  else (false,0,1)

private theorem roundedForestTierWithSeedReads_spec
    (units : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (scale : ℕ) (sample : ForestRoundingSample W h scale)
    (e : HeightForestVertex W h × HeightForestVertex W h) (tier : Fin (scale.log2+1)) :
    let out := roundedForestTierWithSeedReads units scale sample e tier
    (out.1,out.2.1) = roundedForestTierWithWork units scale sample e tier ∧ out.2.2 ≤ h+2 := by
  by_cases gate : (sample (heightForestRoot e.1) tier).1.val < 2^tier.val
  · have card := historyAncestors_card_le (roundingArcHistory e)
    simp only [roundedForestTierWithSeedReads,roundedForestTierWithWork,historyLegWithWork,gate,ite_true]
    exact ⟨True.intro,by omega⟩
  · simp only [roundedForestTierWithSeedReads,roundedForestTierWithWork,gate,ite_false]
    exact ⟨True.intro,by omega⟩

private def finiteAllWithSeedWork {I : Type*} (checks : I → Bool × ℕ × ℕ) (s : Finset I) : Bool × ℕ × ℕ :=
  let rows := s.map (rowWithSeedReads checks)
  (decide (¬ (rows.filter fun row => row.2.1 = false).Nonempty),
    ∑ row ∈ rows, row.2.2.1,∑ row ∈ rows, row.2.2.2)

private theorem finiteAllWithSeedWork_spec {I : Type*} (checks : I → Bool × ℕ × ℕ)
    (s : Finset I) (B : ℕ) (bound : ∀ i ∈ s, (checks i).2.2 ≤ B) :
    let out := finiteAllWithSeedWork checks s
    (out.1,out.2.1) = finiteAllWithWork (fun i => ((checks i).1,(checks i).2.1)) s ∧
      out.2.2 ≤ s.card*B := by
  let rows := s.map (rowWithSeedReads checks)
  let project := fun i => ((checks i).1,(checks i).2.1)
  have all : (finiteAllWithSeedWork checks s).1 = true ↔ ∀ i ∈ s, (checks i).1 = true := by
    change decide (¬ (rows.filter fun row => row.2.1 = false).Nonempty) = true ↔ _
    rw [decide_eq_true_eq]
    constructor
    · intro pass i member
      by_contra falseFlag
      have flag := Bool.eq_false_of_not_eq_true falseFlag
      exact pass ⟨rowWithSeedReads checks i,mem_filter.mpr ⟨mem_map_of_mem _ member,flag⟩⟩
    · rintro pass ⟨row,member⟩
      obtain ⟨packed,flag⟩ := mem_filter.mp member
      obtain ⟨i,inside,rfl⟩ := mem_map.mp packed
      exact Bool.noConfusion (flag.symm.trans (pass i inside))
  have old := (finiteAllWithWork_spec project s (∑ i ∈ s, (checks i).2.1)
    (fun i mem => single_le_sum (f := fun j => (checks j).2.1) (fun _ _ => zero_le) mem)).1
  refine ⟨Prod.ext (Bool.eq_iff_iff.mpr (all.trans old.symm)) ?_,rowSeedReads_le s checks B bound⟩
  dsimp only [finiteAllWithSeedWork,finiteAllWithWork]
  rw [sum_map,sum_map]
  rfl

/-- Evaluate one individually metered sample for each ancestor in a path test. -/
def thresholdPathWithSeedWork (m : ℕ) (cutoff : HeightNode W h → ℕ × ℕ)
    (ancestors : Finset (HeightNode W h)) (sample : HeightNode W h → Fin m × ℕ) : Bool × ℕ × ℕ :=
  finiteAllWithSeedWork (fun node =>
    let stop := cutoff node
    let read := sample node
    (decide (read.1.val < stop.1),stop.2,read.2)) ancestors

omit [LinearOrder W] [Fintype W] in
theorem thresholdPathWithSeedWork_spec (m : ℕ) (cutoff : HeightNode W h → ℕ × ℕ)
    (ancestors : Finset (HeightNode W h)) (sample : HeightNode W h → Fin m × ℕ)
    (B : ℕ) (bound : ∀ node ∈ ancestors, (sample node).2 ≤ B) :
    let out := thresholdPathWithSeedWork m cutoff ancestors sample
    (out.1,out.2.1) = thresholdPathWithWork m cutoff ancestors (fun node => (sample node).1) ∧
      out.2.2 ≤ ancestors.card*B :=
  finiteAllWithSeedWork_spec (fun node =>
    let stop := cutoff node
    let read := sample node
    (decide (read.1.val < stop.1),stop.2,read.2)) ancestors B bound

abbrev ForestRoundingSampleWithSeedWork (W : Type*) (h scale : ℕ) :=
  W → Fin (scale.log2+1) → (Fin (forestSeedSize scale) × ℕ) ×
    (Bool → HeightNode W h → Fin (forestSeedSize scale) × ℕ)

def forestRoundingSampleValues (scale : ℕ) (sample : ForestRoundingSampleWithSeedWork W h scale) :
    ForestRoundingSample W h scale := fun root tier =>
  let pair := sample root tier
  (pair.1.1,fun side node => (pair.2 side node).1)

private def roundedForestTierWithSeedWork
    (units : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (scale : ℕ) (sample : ForestRoundingSampleWithSeedWork W h scale)
    (e : HeightForestVertex W h × HeightForestVertex W h) (tier : Fin (scale.log2+1)) : Bool × ℕ × ℕ :=
  let root := heightForestRoot e.1
  let draw := sample root tier
  let side := roundingArcSide e
  let hist := roundingArcHistory e
  if draw.1.1.val < 2^tier.val then
    let cutoffs := historyCutoffWithWork (scale.log2+1) tier.val (fun node => units (heightForestLegArc root side node))
    let passed := thresholdPathWithSeedWork _ cutoffs (historyAncestors hist) (draw.2 side)
    (passed.1,passed.2.1,draw.1.2+passed.2.2)
  else (false,0,draw.1.2)

private theorem roundedForestTierWithSeedWork_spec
    (units : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (scale : ℕ) (sample : ForestRoundingSampleWithSeedWork W h scale)
    (e : HeightForestVertex W h × HeightForestVertex W h) (tier : Fin (scale.log2+1))
    (B : ℕ) (gateBound : ∀ root i, (sample root i).1.2 ≤ B)
    (testBound : ∀ root i side node, ((sample root i).2 side node).2 ≤ B) :
    let out := roundedForestTierWithSeedWork units scale sample e tier
    (out.1,out.2.1) = roundedForestTierWithWork units scale (forestRoundingSampleValues scale sample) e tier ∧
      out.2.2 ≤ (h+2)*B := by
  let root := heightForestRoot e.1
  let side := roundingArcSide e
  let hist := roundingArcHistory e
  let ancestors := historyAncestors hist
  let cutoffs := historyCutoffWithWork (scale.log2+1) tier.val
    (fun node => units (heightForestLegArc root side node))
  have opening := gateBound root tier
  by_cases openGate : (sample (heightForestRoot e.1) tier).1.1.val < 2^tier.val
  · obtain ⟨preserves,meter⟩ := thresholdPathWithSeedWork_spec _ cutoffs ancestors ((sample root tier).2 side) B
      (fun node _ => testBound root tier side node)
    simp only [roundedForestTierWithSeedWork,roundedForestTierWithWork,forestRoundingSampleValues,
      openGate,ite_true,historyLegWithWork]
    refine ⟨preserves,?_⟩
    exact (Nat.add_le_add opening
      (meter.trans (Nat.mul_le_mul_right B (historyAncestors_card_le hist)))).trans_eq (by ring)
  · simp only [roundedForestTierWithSeedWork,roundedForestTierWithWork,forestRoundingSampleValues,
      openGate,ite_false,true_and]
    exact opening.trans (Nat.le_mul_of_pos_left _ (by omega))

/-- Uniform per-access bound for the gate and ancestor readers. -/
def forestSampleWorkBound {scale : ℕ} (sample : ForestRoundingSampleWithSeedWork W h scale) (B : ℕ) : Prop :=
  ∀ root tier,
    (sample root tier).1.2 ≤ B ∧ ∀ side node, ((sample root tier).2 side node).2 ≤ B

private abbrev ForestTierCheck (W : Type*) (h scale : ℕ) :=
  (HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ) →
    HeightForestVertex W h × HeightForestVertex W h → Fin (scale.log2+1) → Bool × ℕ × ℕ

private def ValidForestTierCheck {scale : ℕ} (check : ForestTierCheck W h scale)
    (sample : ForestRoundingSample W h scale) (bound : ℕ) : Prop :=
  ∀ units e tier,
    let result := check units e tier
    (result.1,result.2.1) = roundedForestTierWithWork units scale sample e tier ∧ result.2.2 ≤ bound

@[inline] private def roundedForestLinkWithSeedTally (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale : ℕ)
    (check : ForestTierCheck W h scale) (e : HeightForestVertex W h × HeightForestVertex W h) : Bool × ℕ × ℕ :=
  let cost := weight e
  if cost.1 = 0 then (true,cost.2,0)
  else
    let units := forestUnitsWithWork links weight charges scale
    let selected := finiteAnyWithSeedReads (check units e) univ
    (selected.1,cost.2+selected.2.1,selected.2.2)

private theorem roundedForestLinkWithSeedTally_spec (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale : ℕ)
    (check : ForestTierCheck W h scale) (sample : ForestRoundingSample W h scale) (B : ℕ)
    (valid : ValidForestTierCheck check sample B) (e : HeightForestVertex W h × HeightForestVertex W h) :
    let out := roundedForestLinkWithSeedTally links weight charges scale check e
    (out.1,out.2.1) = roundedForestLinkWithWork links weight charges scale sample e ∧
      out.2.2 ≤ (scale.log2+1)*B := by
  let units := forestUnitsWithWork links weight charges scale
  let checked := check units e
  have each (tier : Fin (scale.log2+1)) := valid units e tier
  obtain ⟨same,reads⟩ := finiteAnyWithSeedReads_spec checked univ B (fun i _ => (each i).2)
  have keys : (fun i => ((checked i).1,(checked i).2.1)) = roundedForestTierWithWork units scale sample e :=
    funext fun i => (each i).1
  rw [keys] at same
  by_cases free : (weight e).1 = 0
  · simp [roundedForestLinkWithSeedTally,roundedForestLinkWithWork,free]
  · simp only [roundedForestLinkWithSeedTally,roundedForestLinkWithWork,free,ite_false]
    constructor
    · rw [← same]
    · simpa only [card_univ,Fintype.card_fin] using reads

@[inline] private def roundedForestLinksWithSeedTally (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale : ℕ)
    (check : ForestTierCheck W h scale) : Arcs (HeightForestVertex W h) × ℕ × ℕ :=
  let rows := links.map (rowWithSeedReads (roundedForestLinkWithSeedTally links weight charges scale check))
  ((rows.filter fun r => r.2.1 = true).image Prod.fst,∑ r ∈ rows, r.2.2.1,∑ r ∈ rows, r.2.2.2)

private theorem roundedForestLinksWithSeedTally_spec (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale : ℕ)
    (check : ForestTierCheck W h scale) (sample : ForestRoundingSample W h scale) (B : ℕ)
    (valid : ValidForestTierCheck check sample B) :
    let out := roundedForestLinksWithSeedTally links weight charges scale check
    (out.1,out.2.1) = roundedForestLinksWithWork links weight charges scale sample ∧
      out.2.2 ≤ links.card*((scale.log2+1)*B) := by
  let checked := roundedForestLinkWithSeedTally links weight charges scale check
  let prev := roundedForestLinkWithWork links weight charges scale sample
  have each (e) := roundedForestLinkWithSeedTally_spec links weight charges scale check sample B valid e
  refine ⟨Prod.ext ?_ ?_,rowSeedReads_le links checked _ (fun e _ => (each e).2)⟩
  · ext e
    change e ∈ ((links.map (rowWithSeedReads checked)).filter fun r => r.2.1 = true).image Prod.fst ↔
      e ∈ ((links.map (rowWithWork prev)).filter fun r => r.2.1 = true).image Prod.fst
    simp only [mem_image,mem_filter,mem_map]
    constructor
    · rintro ⟨row,⟨⟨k,mem,rfl⟩,yes⟩,rfl⟩
      exact ⟨rowWithWork prev k,⟨⟨k,mem,rfl⟩,(congrArg Prod.fst (each k).1) ▸ yes⟩,rfl⟩
    · rintro ⟨row,⟨⟨k,mem,rfl⟩,yes⟩,rfl⟩
      exact ⟨rowWithSeedReads checked k,⟨⟨k,mem,rfl⟩,(congrArg Prod.fst (each k).1).symm ▸ yes⟩,rfl⟩
  · dsimp only [roundedForestLinksWithSeedTally,roundedForestLinksWithWork]
    rw [sum_map,sum_map]
    exact sum_congr rfl (fun e _ => congrArg Prod.snd (each e).1)

@[inline] private def roundedForestTrialsWithSeedTally (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale trials : ℕ)
    (check : Fin trials → ForestTierCheck W h scale) : Arcs (HeightForestVertex W h) × ℕ × ℕ :=
  let evaluate := fun i => roundedForestLinksWithSeedTally links weight charges scale (check i)
  let rows := univ.map (rowWithSeedReads evaluate)
  (rows.biUnion (fun r => r.2.1),∑ r ∈ rows, r.2.2.1,∑ r ∈ rows, r.2.2.2)

private theorem roundedForestTrialsWithSeedTally_spec (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale trials : ℕ)
    (check : Fin trials → ForestTierCheck W h scale) (sample : ForestTrialArray W h scale trials)
    (B : ℕ) (valid : ∀ i, ValidForestTierCheck (check i) (sample i) B) :
    let out := roundedForestTrialsWithSeedTally links weight charges scale trials check
    (out.1,out.2.1) = roundedForestTrialsWithWork links weight charges scale trials sample ∧
      out.2.2 ≤ trials*(links.card*((scale.log2+1)*B)) := by
  let evaluate := fun i : Fin trials => roundedForestLinksWithSeedTally links weight charges scale (check i)
  let prev := fun i : Fin trials => roundedForestLinksWithWork links weight charges scale (sample i)
  have each (i : Fin trials) := roundedForestLinksWithSeedTally_spec links weight charges scale
    (check i) (sample i) B (valid i)
  refine ⟨Prod.ext ?_ ?_,?_⟩
  · ext e
    change e ∈ (univ.map (rowWithSeedReads evaluate)).biUnion (fun r => r.2.1) ↔
      e ∈ (univ.map (rowWithWork prev)).biUnion (fun r => r.2.1)
    constructor
    · intro he
      obtain ⟨row,present,contains⟩ := mem_biUnion.mp he
      obtain ⟨i,inside,rfl⟩ := mem_map.mp present
      exact mem_biUnion.mpr ⟨rowWithWork prev i,mem_map_of_mem _ inside,
        congrArg Prod.fst (each i).1 ▸ contains⟩
    · intro he
      obtain ⟨row,present,contains⟩ := mem_biUnion.mp he
      obtain ⟨i,inside,rfl⟩ := mem_map.mp present
      exact mem_biUnion.mpr ⟨rowWithSeedReads evaluate i,mem_map_of_mem _ inside,
        (congrArg Prod.fst (each i).1).symm ▸ contains⟩
  · dsimp only [roundedForestTrialsWithSeedTally,roundedForestTrialsWithWork]
    rw [sum_map,sum_map]
    exact sum_congr rfl (fun i _ => congrArg Prod.snd (each i).1)
  · simpa only [roundedForestTrialsWithSeedTally,card_univ,Fintype.card_fin] using
      rowSeedReads_le univ evaluate _ (fun i _ => (each i).2)

/-- Count the root gates and ancestor sample reads. Retain the earlier
weight tally as the middle field. -/
def roundedForestTrialsWithSeedReads (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale trials : ℕ)
    (sample : ForestTrialArray W h scale trials) : Arcs (HeightForestVertex W h) × ℕ × ℕ :=
  roundedForestTrialsWithSeedTally links weight charges scale trials
    (fun i units => roundedForestTierWithSeedReads units scale (sample i))

theorem roundedForestTrialsWithSeedReads_spec (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale trials : ℕ)
    (sample : ForestTrialArray W h scale trials) :
    let out := roundedForestTrialsWithSeedReads links weight charges scale trials sample
    (out.1,out.2.1) = roundedForestTrialsWithWork links weight charges scale trials sample ∧
      out.2.2 ≤ trials*(links.card*((scale.log2+1)*(h+2))) :=
  roundedForestTrialsWithSeedTally_spec links weight charges scale trials
    (fun i units => roundedForestTierWithSeedReads units scale (sample i)) sample (h+2)
    (fun i units => roundedForestTierWithSeedReads_spec units scale (sample i))

abbrev ForestTrialArrayWithSeedWork (W : Type*) (h scale trials : ℕ) :=
  Fin trials → ForestRoundingSampleWithSeedWork W h scale

/-- Aggregate the work returned by the sampled gates and ancestor tests. -/
def roundedForestTrialsWithSeedWork (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale trials : ℕ)
    (sample : ForestTrialArrayWithSeedWork W h scale trials) : Arcs (HeightForestVertex W h) × ℕ × ℕ :=
  roundedForestTrialsWithSeedTally links weight charges scale trials
    (fun i units => roundedForestTierWithSeedWork units scale (sample i))

theorem roundedForestTrialsWithSeedWork_spec (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale trials : ℕ)
    (sample : ForestTrialArrayWithSeedWork W h scale trials) (B : ℕ)
    (cap : ∀ i, forestSampleWorkBound (sample i) B) :
    let out := roundedForestTrialsWithSeedWork links weight charges scale trials sample
    let plain := fun i => forestRoundingSampleValues scale (sample i)
    (out.1,out.2.1) = roundedForestTrialsWithWork links weight charges scale trials plain ∧
      out.2.2 ≤ trials*(links.card*((scale.log2+1)*((h+2)*B))) :=
  roundedForestTrialsWithSeedTally_spec links weight charges scale trials
    (fun i units => roundedForestTierWithSeedWork units scale (sample i))
    (fun i => forestRoundingSampleValues scale (sample i)) ((h+2)*B)
    (fun i units e tier => roundedForestTierWithSeedWork_spec units scale (sample i) e tier B
      (fun root k => (cap i root k).1) (fun root k side node => (cap i root k).2 side node))

end Forest

end OnlineReachabilityPreservers
