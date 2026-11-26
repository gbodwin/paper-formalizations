import OnlineReachabilityPreservers.SteinerForestLabelWork
import OnlineReachabilityPreservers.SteinerForestNetwork
import OnlineReachabilityPreservers.SteinerPhaseUnionWork

/-! Construct the two current attachment groups by one scan of explicit
height-forest rows. -/

namespace OnlineReachabilityPreservers

open Finset

private def historyLengthWithWordWork {V : Type*} : List V → ℕ × ℕ
  | [] => (0,2)
  | _ :: tail =>
    let rest := historyLengthWithWordWork tail
    (rest.1+1,rest.2+5)

private theorem historyLengthWithWordWork_spec {V : Type*} (history : List V) :
    historyLengthWithWordWork history = (history.length,5*history.length+2) := by
  induction history with
  | nil => rfl
  | cons v tail ih => simp only [historyLengthWithWordWork, ih, List.length_cons, Nat.mul_succ]

variable {V : Type*} [LinearOrder V] {height : ℕ}

local instance attachmentNetworkDecidableEq : DecidableEq (ForestNetworkVertex V height) :=
  (inferInstance : LinearOrder (ForestNetworkVertex V height)).toDecidableEq

private def forestAttachmentChoiceWithWordWork (s t : V) (v : HeightForestVertex V height) : Bool × Bool × ℕ :=
  let depth := historyLengthWithWordWork (heightForestHistory v).val
  if depth.1 = height then
    let label := forestLabelWithWordWork v
    let side := heightForestSide v
    (decide (side = false ∧ label.1 = s),decide (side = true ∧ label.1 = t),depth.2+label.2+14)
  else (false,false,depth.2+7)

private theorem forestAttachmentChoiceWithWordWork_spec (s t : V) (v : HeightForestVertex V height) :
    let out := forestAttachmentChoiceWithWordWork s t v
    out.1 = decide (sourceLeaf s v) ∧ out.2.1 = decide (sinkLeaf t v) ∧ out.2.2 ≤ 10*height+25 := by
  obtain ⟨label, labelWork⟩ := forestLabelWithWordWork_spec v
  have depth := (heightForestHistory v).property
  unfold forestAttachmentChoiceWithWordWork
  rw [historyLengthWithWordWork_spec]
  dsimp only
  by_cases full : (heightForestHistory v).val.length = height
  · simp only [sourceLeaf, sinkLeaf, full, ite_true, label, true_and]
    omega
  · have noEntry : ¬ sourceLeaf s v := fun h => full h.2.1
    have noExit : ¬ sinkLeaf t v := fun h => full h.2.1
    simp only [full, ite_false, noEntry, noExit, decide_false, true_and]
    omega

private def forestEntryArc (s : V) : HeightForestVertex V height ↪
    ForestNetworkVertex V height × ForestNetworkVertex V height :=
  ⟨fun v => (forestNetworkSource s,forestNetworkCopy v),
    fun _ _ same => forestNetworkCopy.injective (congrArg Prod.snd same)⟩

private def forestExitArc (t : V) : HeightForestVertex V height ↪
    ForestNetworkVertex V height × ForestNetworkVertex V height :=
  ⟨fun v => (forestNetworkCopy v,forestNetworkSink t),
    fun _ _ same => forestNetworkCopy.injective (congrArg Prod.fst same)⟩

private def forestAttachmentRowsWithWordWork (s t : V) : List (HeightForestVertex V height) →
    (List (ForestNetworkVertex V height × ForestNetworkVertex V height) ×
      List (ForestNetworkVertex V height × ForestNetworkVertex V height)) × ℕ
  | [] => (([],[]),5)
  | v :: nodes =>
    let rest := forestAttachmentRowsWithWordWork s t nodes
    let choice := forestAttachmentChoiceWithWordWork s t v
    let enter := if choice.1 then forestEntryArc s v :: rest.1.1 else rest.1.1
    let exit := if choice.2.1 then forestExitArc t v :: rest.1.2 else rest.1.2
    ((enter,exit),rest.2+choice.2.2+16)

private theorem forestAttachmentRowsWithWordWork_spec (s t : V) (vertices : List (HeightForestVertex V height)) :
    let out := forestAttachmentRowsWithWordWork s t vertices
    out.1.1 = (vertices.filter (fun v => decide (sourceLeaf s v))).map (forestEntryArc s) ∧
      out.1.2 = (vertices.filter (fun v => decide (sinkLeaf t v))).map (forestExitArc t) ∧
      out.2 ≤ (10*height+41)*vertices.length+5 := by
  induction vertices with
  | nil => simp [forestAttachmentRowsWithWordWork]
  | cons v tail ih =>
    obtain ⟨entries, exits, cost⟩ := ih
    obtain ⟨first, second, checked⟩ := forestAttachmentChoiceWithWordWork_spec s t v
    unfold forestAttachmentRowsWithWordWork
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · rw [first, entries]
      by_cases inGroup : sourceLeaf s v <;> simp [inGroup]
    · rw [second, exits]
      by_cases inGroup : sinkLeaf t v <;> simp [inGroup]
    · rw [List.length_cons, Nat.mul_succ]
      omega

private def forestAttachmentsWithWordWork (s t : V) (vertices : List (HeightForestVertex V height))
    (distinct : vertices.Nodup) :
    (Arcs (ForestNetworkVertex V height) × Arcs (ForestNetworkVertex V height)) × ℕ :=
  let rows := forestAttachmentRowsWithWordWork s t vertices
  let spec := forestAttachmentRowsWithWordWork_spec s t vertices
  have inUnique : rows.1.1.Nodup := spec.1.symm ▸ (distinct.filter _).map (forestEntryArc s).injective
  have outUnique : rows.1.2.Nodup := spec.2.1.symm ▸ (distinct.filter _).map (forestExitArc t).injective
  ((⟨rows.1.1,by simpa using inUnique⟩,⟨rows.1.2,by simpa using outUnique⟩),rows.2+7)

variable [Fintype V]

private theorem forestAttachmentsWithWordWork_spec (s t : V) (vertices : List (HeightForestVertex V height))
    (distinct : vertices.Nodup) (complete : ∀ v, v ∈ vertices) :
    let out := forestAttachmentsWithWordWork s t vertices distinct
    out.1.1 = forestNetworkEntries s ∧ out.1.2 = forestNetworkExits t ∧
      out.1.1.card ≤ vertices.length ∧ out.1.2.card ≤ vertices.length ∧
      out.2 ≤ (10*height+41)*vertices.length+12 := by
  let rows := forestAttachmentRowsWithWordWork s t vertices
  obtain ⟨entries, exits, work⟩ := forestAttachmentRowsWithWordWork_spec s t vertices
  have capacity (pred : HeightForestVertex V height → Bool) :
      (vertices.filter pred).length ≤ vertices.length := List.length_filter_le _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext edge
    change edge ∈ rows.1.1 ↔ edge ∈ forestNetworkEntries s
    change rows.1.1 = _ at entries
    rw [entries]
    simp only [List.mem_map, List.mem_filter, forestNetworkEntries, mem_image, mem_filter, mem_univ,
      true_and, decide_eq_true_eq, complete]
    rfl
  · ext edge
    change edge ∈ rows.1.2 ↔ edge ∈ forestNetworkExits t
    change rows.1.2 = _ at exits
    rw [exits]
    simp only [List.mem_map, List.mem_filter, forestNetworkExits, mem_image, mem_filter, mem_univ,
      true_and, decide_eq_true_eq, complete]
    rfl
  · change rows.1.1.length ≤ vertices.length
    change rows.1.1 = _ at entries
    rw [entries, List.length_map]
    exact capacity _
  · change rows.1.2.length ≤ vertices.length
    change rows.1.2 = _ at exits
    rw [exits, List.length_map]
    exact capacity _
  · exact Nat.add_le_add_right work _

private def forestAttachmentUnionBudget (base extra : ℕ) : ℕ :=
  extra*(12*base+19)+5*base+10

/-- Word work for one request's explicit leaf scan and two arc unions. -/
def forestRequestWordBudget (height vertices free : ℕ) : ℕ :=
  (10*height+41)*vertices+12+forestAttachmentUnionBudget free vertices+
    forestAttachmentUnionBudget (free+vertices) vertices+9

theorem forestRequestWordBudget_le {height vertices vertices' free free' : ℕ}
    (verts : vertices ≤ vertices') (edges : free ≤ free') :
    forestRequestWordBudget height vertices free ≤ forestRequestWordBudget height vertices' free' := by
  unfold forestRequestWordBudget forestAttachmentUnionBudget
  gcongr

/-- Use the complete forest row list for the current demand's attachments. -/
def forestRequestWithWordWork (vertices : List (HeightForestVertex V height)) (distinct : vertices.Nodup)
    (free : Arcs (ForestNetworkVertex V height)) (d : V × V) : WeightedNetworkDemand (ForestNetworkVertex V height) × ℕ :=
  let groups := forestAttachmentsWithWordWork d.1 d.2 vertices distinct
  let start := unionFinsetWithWordWork free groups.1.1
  let endGroup := unionFinsetWithWordWork start.1 groups.1.2
  (⟨endGroup.1,forestNetworkSource d.1,forestNetworkSink d.2⟩,groups.2+start.2+endGroup.2+9)

theorem forestRequestWithWordWork_spec (vertices : List (HeightForestVertex V height)) (distinct : vertices.Nodup)
    (complete : ∀ v, v ∈ vertices) (free : Arcs (ForestNetworkVertex V height)) (d : V × V) :
    let out := forestRequestWithWordWork vertices distinct free d
    out.1 = ⟨free ∪ forestNetworkEntries d.1 ∪ forestNetworkExits d.2,
      forestNetworkSource d.1,forestNetworkSink d.2⟩ ∧
      out.2 ≤ forestRequestWordBudget height vertices.length free.card := by
  let groups := forestAttachmentsWithWordWork d.1 d.2 vertices distinct
  let start := unionFinsetWithWordWork free groups.1.1
  let finish := unionFinsetWithWordWork start.1 groups.1.2
  obtain ⟨inputs, outputs, inCount, outCount, groupWork⟩ :=
    forestAttachmentsWithWordWork_spec d.1 d.2 vertices distinct complete
  obtain ⟨first, firstCost⟩ := unionFinsetWithWordWork_spec free groups.1.1
  obtain ⟨second, secondCost⟩ := unionFinsetWithWordWork_spec start.1 groups.1.2
  have startSize : start.1.card ≤ free.card+vertices.length := by
    change (unionFinsetWithWordWork free groups.1.1).1.card ≤ _
    rw [first]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left inCount _)
  have entryBudget : start.2 ≤ forestAttachmentUnionBudget free.card vertices.length := by
    refine firstCost.trans ?_
    unfold forestAttachmentUnionBudget
    gcongr
  have exitBudget : finish.2 ≤ forestAttachmentUnionBudget (free.card+vertices.length) vertices.length := by
    refine secondCost.trans ?_
    unfold forestAttachmentUnionBudget
    gcongr
  refine ⟨?_, ?_⟩
  · change WeightedNetworkDemand.mk finish.1 _ _ = _
    change finish.1 = _ at second
    change start.1 = _ at first
    change groups.1.1 = _ at inputs
    change groups.1.2 = _ at outputs
    rw [second, first, inputs, outputs]
  · change groups.2+start.2+finish.2+9 ≤ _
    change groups.2 ≤ _ at groupWork
    unfold forestRequestWordBudget
    omega

/-- Prepare the same current requests in order, with the attachment work
accumulated alongside the output list. -/
def forestRequestsWithWordWork (vertices : List (HeightForestVertex V height)) (distinct : vertices.Nodup)
    (free : Arcs (ForestNetworkVertex V height)) :
    List (V × V) → List (WeightedNetworkDemand (ForestNetworkVertex V height)) × ℕ
  | [] => ([],3)
  | d :: D =>
    let now := forestRequestWithWordWork vertices distinct free d
    let later := forestRequestsWithWordWork vertices distinct free D
    (now.1 :: later.1,now.2+later.2+9)

theorem forestRequestsWithWordWork_spec (vertices : List (HeightForestVertex V height)) (distinct : vertices.Nodup)
    (complete : ∀ v, v ∈ vertices) (free : Arcs (ForestNetworkVertex V height)) (D : List (V × V)) :
    let out := forestRequestsWithWordWork vertices distinct free D
    out.1 = D.map (fun d => ⟨free ∪ forestNetworkEntries d.1 ∪ forestNetworkExits d.2,
      forestNetworkSource d.1,forestNetworkSink d.2⟩) ∧
      out.2 ≤ D.length*(forestRequestWordBudget height vertices.length free.card+9)+3 := by
  induction D with
  | nil => simp [forestRequestsWithWordWork]
  | cons d D ih =>
    obtain ⟨head, cost⟩ := forestRequestWithWordWork_spec vertices distinct complete free d
    obtain ⟨tail, work⟩ := ih
    simp only [forestRequestsWithWordWork, head, tail, List.map_cons, true_and,
      List.length_cons, Nat.succ_mul]
    omega

end OnlineReachabilityPreservers
