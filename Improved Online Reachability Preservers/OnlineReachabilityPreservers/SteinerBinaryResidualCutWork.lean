import OnlineReachabilityPreservers.SteinerBinaryReachWork
import OnlineReachabilityPreservers.SteinerCutFlow

/-! Extract the outgoing cut from supplied encoded residual arcs. -/

namespace OnlineReachabilityPreservers

private def reverseBinaryArcRowsWithWork :
    List (List Bool × List Bool) → List (List Bool × List Bool) × ℕ
  | [] => ([],2)
  | e::rest =>
    let tail := reverseBinaryArcRowsWithWork rest
    (e.swap::tail.1,tail.2+5)

private theorem reverseBinaryArcRowsWithWork_spec {V : Type*} (code : V → List Bool)
    (arcs : List (V × V)) :
    reverseBinaryArcRowsWithWork (binaryEncodeArcs code arcs) =
      (binaryEncodeArcs code (arcs.map Prod.swap),2+5*arcs.length) := by
  induction arcs with
  | nil => rfl
  | cons e rest ih =>
    simp only [binaryEncodeArcs,List.map_cons,reverseBinaryArcRowsWithWork,
      show reverseBinaryArcRowsWithWork (List.map (fun a => (code a.1,code a.2)) rest) =
        (binaryEncodeArcs code (rest.map Prod.swap),2+5*rest.length) from ih,
      List.length_cons,Nat.mul_succ,Prod.swap,Nat.add_assoc]

/-- Retain, in the input order, every encoded arc that leaves the listed side. -/
def binaryOutgoingCutWithWork (side : List (List Bool)) :
    List (List Bool × List Bool) → List (List Bool × List Bool) × ℕ
  | [] => ([],2)
  | arc::rest =>
    let source := binaryKeyMemWithWork arc.1 side
    let target := binaryKeyMemWithWork arc.2 side
    let tail := binaryOutgoingCutWithWork side rest
    (if source.1 && !target.1 then arc::tail.1 else tail.1,source.2+target.2+tail.2+10)

variable {V : Type*} [LinearOrder V] [Fintype V]

open Finset

/-- Filtering encoded arcs uses their original list order and decides the
same cut membership on every cell. -/
theorem binaryOutgoingCutWithWork_spec (code : V → List Bool) (injective : Function.Injective code)
    (w : ℕ) (bounded : ∀ v, (code v).length ≤ w) (side : List V) (simple : side.Nodup) (arcs : List (V × V)) :
    let out := binaryOutgoingCutWithWork (side.map code) (binaryEncodeArcs code arcs)
    out.1 = binaryEncodeArcs code (arcs.filter fun arc => decide (arc.1 ∈ side ∧ arc.2 ∉ side)) ∧
      out.2 ≤ 2+arcs.length*(12+2*((5*w+8)*Fintype.card V)) := by
  let unit := (5*w+8)*Fintype.card V
  have length : side.length ≤ Fintype.card V := by
    rw [← List.toFinset_card_of_nodup simple]
    exact card_le_univ _
  induction arcs with
  | nil => simp [binaryEncodeArcs,binaryOutgoingCutWithWork]
  | cons arc rest ih =>
    let source := binaryKeyMemWithWork (code arc.1) (side.map code)
    let target := binaryKeyMemWithWork (code arc.2) (side.map code)
    let tail := binaryOutgoingCutWithWork (side.map code) (binaryEncodeArcs code rest)
    let predicate := fun e : V × V => decide (e.1 ∈ side ∧ e.2 ∉ side)
    obtain ⟨sourceValue,sourceCost⟩ := binaryKeyMemWithWork_encoded_spec code injective w bounded arc.1 side
    obtain ⟨targetValue,targetCost⟩ := binaryKeyMemWithWork_encoded_spec code injective w bounded arc.2 side
    obtain ⟨tailValue,tailCost⟩ := ih
    have passes : (source.1 && !target.1) = predicate arc := by
      change source.1 = _ at sourceValue
      change target.1 = _ at targetValue
      rw [sourceValue,targetValue]
      by_cases first : arc.1 ∈ side <;> by_cases second : arc.2 ∈ side <;> simp [predicate,first,second]
    have sourceBudget : source.2 ≤ 1+unit :=
      sourceCost.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ length) _)
    have targetBudget : target.2 ≤ 1+unit :=
      targetCost.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ length) _)
    refine ⟨?_,?_⟩
    · change (if source.1 && !target.1 then (code arc.1,code arc.2)::tail.1 else tail.1) =
        binaryEncodeArcs code ((arc::rest).filter predicate)
      rw [passes,show tail.1 = _ from tailValue,List.filter_cons]
      split <;> rfl
    · change source.2+target.2+tail.2+10 ≤ 2+(rest.length+1)*(12+2*unit)
      change tail.2 ≤ 2+rest.length*(12+2*unit) at tailCost
      rw [Nat.succ_mul rest.length (12+2*unit)]
      omega

/-- Derive the reachable side from the supplied residual arcs and extract
the outgoing cut of the supplied original arc list. -/
def binaryResidualCutWithWork (arcs residual : List (List Bool × List Bool)) (source : List Bool)
    (depth : ℕ) : List (List Bool × List Bool) × ℕ :=
  let reversed := reverseBinaryArcRowsWithWork residual
  let side := binaryReachInListWithWork reversed.1 source depth
  let cut := binaryOutgoingCutWithWork side.1 arcs
  (cut.1,reversed.2+side.2+cut.2+6)

/-- Work for reversing the residual rows, finding the rooted side, and
scanning the original rows. -/
def binaryResidualCutWorkBudget (n arcs residual labels depth : ℕ) : ℕ :=
  let scans := 2*((5*labels+8)*n)
  2+5*residual+(2+depth*(5+residual*(14+scans)))+(2+arcs*(12+scans))+6

/-- The output keeps exactly the original arc rows leaving the bounded
residual reachable side. The encoded lists are supplied. -/
theorem binaryResidualCutWithWork_spec (code : V → List Bool) (injective : Function.Injective code)
    (w : ℕ) (bounded : ∀ v, (code v).length ≤ w) (arcs residual : List (V × V)) (source : V) (depth : ℕ) :
    let out := binaryResidualCutWithWork (binaryEncodeArcs code arcs) (binaryEncodeArcs code residual) (code source) depth
    let side := reachIn (reverseArcs residual.toFinset) source depth
    out.1 = binaryEncodeArcs code (arcs.filter fun arc => decide (arc.1 ∈ side ∧ arc.2 ∉ side)) ∧
      out.2 ≤ binaryResidualCutWorkBudget (Fintype.card V) arcs.length residual.length w depth := by
  let flipped := residual.map Prod.swap
  let reference := reachInListWithWordWork flipped source depth
  let side := reachIn (reverseArcs residual.toFinset) source depth
  obtain ⟨simple,set, _⟩ := reachInListWithWordWork_spec flipped source depth
  have reverseAsSet : flipped.toFinset = reverseArcs residual.toFinset := by
    ext e
    simp [flipped,reverseArcs,List.mem_map]
  have sameSide : reference.1.toFinset = side := set.trans (congrArg (fun g => reachIn g source depth) reverseAsSet)
  obtain ⟨sameSearch,searchCost⟩ := binaryReachInListWithWork_spec code injective w bounded flipped source depth
  obtain ⟨sameCut,cutCost⟩ := binaryOutgoingCutWithWork_spec code injective w bounded reference.1 simple arcs
  have sameRows :
      (arcs.filter fun e => decide (e.1 ∈ reference.1 ∧ e.2 ∉ reference.1)) =
        (arcs.filter fun e => decide (e.1 ∈ side ∧ e.2 ∉ side)) := by
    apply congrArg (fun predicate => arcs.filter predicate)
    funext e
    rw [decide_eq_decide,← sameSide]
    simp only [List.mem_toFinset]
  change (binaryResidualCutWithWork _ _ _ _).1 = _ ∧ (binaryResidualCutWithWork _ _ _ _).2 ≤ _
  unfold binaryResidualCutWithWork
  rw [reverseBinaryArcRowsWithWork_spec code residual]
  let scanned := binaryReachInListWithWork (binaryEncodeArcs code flipped) (code source) depth
  change scanned.1 = reference.1.map code at sameSearch
  change (binaryOutgoingCutWithWork scanned.1 (binaryEncodeArcs code arcs)).1 = _ ∧
    2+5*residual.length+scanned.2+(binaryOutgoingCutWithWork scanned.1 (binaryEncodeArcs code arcs)).2+6 ≤ _
  rw [sameSearch]
  refine ⟨sameCut.trans (congrArg (binaryEncodeArcs code) sameRows),?_⟩
  have amount : flipped.length = residual.length := List.length_map Prod.swap
  rw [amount] at searchCost
  unfold binaryResidualCutWorkBudget
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add_left searchCost (2+5*residual.length)) cutCost) 6

/-- At the vertex-count depth the resulting arc list describes the cut
of the residual flow, when the supplied residual rows describe that flow. -/
theorem binaryResidualCutWithWork_refines {capacity flow : ArcFlow V}
    (code : V → List Bool) (injective : Function.Injective code) (w : ℕ) (bounded : ∀ v, (code v).length ≤ w)
    (arcs residual : List (V × V)) (source : V) (encodedResidual : residual.toFinset = residualArcs capacity flow) :
    let out := binaryResidualCutWithWork (binaryEncodeArcs code arcs) (binaryEncodeArcs code residual) (code source)
      (Fintype.card V)
    ∃ cut : List (V × V), out.1 = binaryEncodeArcs code cut ∧
      cut.toFinset = outgoingCut arcs.toFinset (residualReach capacity flow source) ∧
      (arcs.Nodup → cut.Nodup) ∧
      out.2 ≤ binaryResidualCutWorkBudget (Fintype.card V) arcs.length residual.length w (Fintype.card V) := by
  obtain ⟨value,work⟩ := binaryResidualCutWithWork_spec code injective w bounded arcs residual source (Fintype.card V)
  rw [encodedResidual] at value
  change _ = binaryEncodeArcs code (arcs.filter fun arc =>
    decide (arc.1 ∈ residualReach capacity flow source ∧ arc.2 ∉ residualReach capacity flow source)) at value
  refine ⟨_,value,?_,fun simple => List.filter_sublist.nodup simple,work⟩
  ext e
  simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq,outgoingCut,mem_filter]

end OnlineReachabilityPreservers
