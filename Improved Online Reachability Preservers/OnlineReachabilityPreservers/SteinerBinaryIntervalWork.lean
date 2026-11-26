import OnlineReachabilityPreservers.SteinerBinaryResidualCutWork

/-! Compute a demand's interval arcs using the encoded graph. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Find the forward reachable list by reversing the supplied arc endpoints. -/
def binaryForwardReachWithWork (arcs : List (List Bool × List Bool)) (source : List Bool) (depth : ℕ) :
    List (List Bool) × ℕ :=
  let reversed := reverseBinaryArcRowsWithWork arcs
  let search := binaryReachInListWithWork reversed.1 source depth
  (search.1,reversed.2+search.2+3)

private def binaryIntervalLayerBudget (n arcs labels depth : ℕ) : ℕ :=
  2+depth*(5+arcs*(14+2*((5*labels+8)*n)))

def binaryForwardReachWorkBudget (n arcs labels depth : ℕ) : ℕ :=
  2+5*arcs+binaryIntervalLayerBudget n arcs labels depth+3

/-- The list positions are those of the search on the reversed arc rows. -/
theorem binaryForwardReachWithWork_spec (code : V → List Bool) (injective : Function.Injective code)
    (w : ℕ) (bounded : ∀ v, (code v).length ≤ w) (arcs : List (V × V)) (source : V) (depth : ℕ) :
    let out := binaryForwardReachWithWork (binaryEncodeArcs code arcs) (code source) depth
    ∃ reached : List V, out.1 = reached.map code ∧ reached.Nodup ∧
      reached.toFinset = reachIn (reverseArcs arcs.toFinset) source depth ∧
      out.2 ≤ binaryForwardReachWorkBudget (Fintype.card V) arcs.length w depth := by
  let reversed := arcs.map Prod.swap
  let result := reachInListWithWordWork reversed source depth
  have reversedSet : reversed.toFinset = reverseArcs arcs.toFinset := by
    ext e
    simp [reversed,reverseArcs,List.mem_map]
  obtain ⟨simple,reached,_⟩ := reachInListWithWordWork_spec reversed source depth
  obtain ⟨same,work⟩ := binaryReachInListWithWork_spec code injective w bounded reversed source depth
  rw [show reversed.length = arcs.length from List.length_map Prod.swap] at work
  refine ⟨result.1,?_,simple,reached.trans (congrArg (fun g => reachIn g source depth) reversedSet),?_⟩
  · simp only [binaryForwardReachWithWork,reverseBinaryArcRowsWithWork_spec]
    exact same
  · simp only [binaryForwardReachWithWork,reverseBinaryArcRowsWithWork_spec,binaryForwardReachWorkBudget,
      binaryIntervalLayerBudget]
    exact Nat.add_le_add_right (Nat.add_le_add_left work _) _

private def binaryIntervalVertexWithWork (forward backward : List (List Bool)) (label : List Bool) : Bool × ℕ :=
  let first := binaryKeyMemWithWork label forward
  let second := binaryKeyMemWithWork label backward
  (first.1 && second.1,first.2+second.2+4)

private theorem binaryIntervalVertexWithWork_spec (code : V → List Bool) (injective : Function.Injective code)
    (w : ℕ) (bounded : ∀ v, (code v).length ≤ w) (forward backward : List V)
    (simpleF : forward.Nodup) (simpleB : backward.Nodup) (v : V) :
    let out := binaryIntervalVertexWithWork (forward.map code) (backward.map code) (code v)
    out.1 = decide (v ∈ forward ∧ v ∈ backward) ∧ out.2 ≤ 6+2*((5*w+8)*Fintype.card V) := by
  let first := binaryKeyMemWithWork (code v) (forward.map code)
  let second := binaryKeyMemWithWork (code v) (backward.map code)
  obtain ⟨firstValue,firstCost⟩ := binaryKeyMemWithWork_encoded_spec code injective w bounded v forward
  obtain ⟨secondValue,secondCost⟩ := binaryKeyMemWithWork_encoded_spec code injective w bounded v backward
  have length {vs : List V} (simple : vs.Nodup) : vs.length ≤ Fintype.card V := by
    rw [← List.toFinset_card_of_nodup simple]
    exact card_le_univ _
  have left : first.2 ≤ 1+(5*w+8)*Fintype.card V :=
    firstCost.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (length simpleF)) _)
  have right : second.2 ≤ 1+(5*w+8)*Fintype.card V :=
    secondCost.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (length simpleB)) _)
  change (first.1 && second.1) = _ ∧ first.2+second.2+4 ≤ _
  rw [show first.1 = _ from firstValue,show second.1 = _ from secondValue]
  refine ⟨?_,by omega⟩
  by_cases present : v ∈ forward <;> simp [present]

private def binaryIntervalArcRowsWithWork (forward backward : List (List Bool)) :
    List (List Bool × List Bool) → List (List Bool × List Bool) × ℕ
  | [] => ([],2)
  | row::rest =>
    let source := binaryIntervalVertexWithWork forward backward row.1
    let target := binaryIntervalVertexWithWork forward backward row.2
    let tail := binaryIntervalArcRowsWithWork forward backward rest
    (if source.1 && target.1 then row::tail.1 else tail.1,source.2+target.2+tail.2+7)

private def binaryIntervalArcRowsWorkBudget (n arcs w : ℕ) : ℕ :=
  2+arcs*(19+4*((5*w+8)*n))

private theorem binaryIntervalArcRowsWithWork_spec (code : V → List Bool) (injective : Function.Injective code)
    (w : ℕ) (bounded : ∀ v, (code v).length ≤ w) (forward backward : List V)
    (simpleF : forward.Nodup) (simpleB : backward.Nodup) (arcs : List (V × V)) :
    let out := binaryIntervalArcRowsWithWork (forward.map code) (backward.map code) (binaryEncodeArcs code arcs)
    let accepted := fun e : V × V =>
      decide ((e.1 ∈ forward ∧ e.1 ∈ backward) ∧ (e.2 ∈ forward ∧ e.2 ∈ backward))
    out.1 = binaryEncodeArcs code (arcs.filter accepted) ∧
      out.2 ≤ binaryIntervalArcRowsWorkBudget (Fintype.card V) arcs.length w := by
  let accepted := fun e : V × V =>
    decide ((e.1 ∈ forward ∧ e.1 ∈ backward) ∧ (e.2 ∈ forward ∧ e.2 ∈ backward))
  let unit := 19+4*((5*w+8)*Fintype.card V)
  induction arcs with
  | nil => simp [binaryIntervalArcRowsWithWork,binaryEncodeArcs,binaryIntervalArcRowsWorkBudget]
  | cons arc rest ih =>
    let source := binaryIntervalVertexWithWork (forward.map code) (backward.map code) (code arc.1)
    let target := binaryIntervalVertexWithWork (forward.map code) (backward.map code) (code arc.2)
    let tail := binaryIntervalArcRowsWithWork (forward.map code) (backward.map code) (binaryEncodeArcs code rest)
    obtain ⟨sourceValue,sourceCost⟩ := binaryIntervalVertexWithWork_spec code injective w bounded forward backward
      simpleF simpleB arc.1
    obtain ⟨targetValue,targetCost⟩ := binaryIntervalVertexWithWork_spec code injective w bounded forward backward
      simpleF simpleB arc.2
    obtain ⟨tailValue,tailCost⟩ := ih
    have passes : (source.1 && target.1) = accepted arc := by
      rw [show source.1 = _ from sourceValue,show target.1 = _ from targetValue]
      by_cases present : arc.1 ∈ forward ∧ arc.1 ∈ backward <;> simp [accepted,present]
    change source.2 ≤ 6+2*((5*w+8)*Fintype.card V) at sourceCost
    change target.2 ≤ 6+2*((5*w+8)*Fintype.card V) at targetCost
    change tail.1 = _ at tailValue
    change tail.2 ≤ 2+rest.length*unit at tailCost
    change (if source.1 && target.1 then (code arc.1,code arc.2)::tail.1 else tail.1) =
        binaryEncodeArcs code ((arc::rest).filter accepted) ∧
      source.2+target.2+tail.2+7 ≤ 2+(rest.length+1)*unit
    refine ⟨?_,?_⟩
    · rw [passes,tailValue,List.filter_cons]
      split <;> rfl
    · rw [Nat.succ_mul rest.length]
      dsimp only [unit] at tailCost ⊢
      omega

/-- Retain exactly the original encoded arc rows with both endpoints
reachable from the source and able to reach the target. -/
def binaryDemandIntervalArcsWithWork (arcs : List (List Bool × List Bool)) (source target : List Bool)
    (depth : ℕ) : List (List Bool × List Bool) × ℕ :=
  let forward := binaryForwardReachWithWork arcs source depth
  let backward := binaryReachInListWithWork arcs target depth
  let result := binaryIntervalArcRowsWithWork forward.1 backward.1 arcs
  (result.1,forward.2+backward.2+result.2+6)

def binaryDemandIntervalArcsWorkBudget (n arcs labels depth : ℕ) : ℕ :=
  binaryForwardReachWorkBudget n arcs labels depth+binaryIntervalLayerBudget n arcs labels depth+
    binaryIntervalArcRowsWorkBudget n arcs labels+6

/-- At vertex-count depth, the encoded list is the exact ordered
restriction to reference interval arcs. -/
theorem binaryDemandIntervalArcsWithWork_spec (code : V → List Bool) (injective : Function.Injective code)
    (w : ℕ) (bounded : ∀ v, (code v).length ≤ w) (arcs : List (V × V)) (demand : V × V) :
    let n := Fintype.card V
    let out := binaryDemandIntervalArcsWithWork (binaryEncodeArcs code arcs) (code demand.1) (code demand.2) n
    out.1 = binaryEncodeArcs code (arcs.filter fun e => decide (e ∈ intervalArcs arcs.toFinset demand)) ∧
      out.2 ≤ binaryDemandIntervalArcsWorkBudget n arcs.length w n := by
  let n := Fintype.card V
  let bits := binaryEncodeArcs code arcs
  let forward := binaryForwardReachWithWork bits (code demand.1) n
  let backward := binaryReachInListWithWork bits (code demand.2) n
  let backwardRef := reachInListWithWordWork arcs demand.2 n
  obtain ⟨forwardRef,forwardValue,simpleF,setF,forwardCost⟩ :=
    binaryForwardReachWithWork_spec code injective w bounded arcs demand.1 n
  obtain ⟨simpleB,setB,_⟩ := reachInListWithWordWork_spec arcs demand.2 n
  obtain ⟨backwardValue,backwardCost⟩ := binaryReachInListWithWork_spec code injective w bounded arcs demand.2 n
  obtain ⟨selected,filterCost⟩ := binaryIntervalArcRowsWithWork_spec code injective w bounded forwardRef backwardRef.1
    simpleF simpleB arcs
  change forward.1 = _ at forwardValue
  change backward.1 = _ at backwardValue
  change forward.2 ≤ _ at forwardCost
  change backward.2 ≤ _ at backwardCost
  have inInterval (v : V) : v ∈ forwardRef ∧ v ∈ backwardRef.1 ↔ v ∈ reachInterval arcs.toFinset demand := by
    change backwardRef.1.toFinset = _ at setB
    rw [← List.mem_toFinset,← List.mem_toFinset,setF,setB]
    exact mem_inter.symm
  have filters :
      (arcs.filter fun e => decide ((e.1 ∈ forwardRef ∧ e.1 ∈ backwardRef.1) ∧
        (e.2 ∈ forwardRef ∧ e.2 ∈ backwardRef.1))) =
        (arcs.filter fun e => decide (e ∈ intervalArcs arcs.toFinset demand)) := by
    apply List.filter_congr
    intro e original
    rw [decide_eq_decide,inInterval,inInterval]
    simp [intervalArcs,original]
  change (binaryIntervalArcRowsWithWork forward.1 backward.1 bits).1 = _ ∧
    forward.2+backward.2+(binaryIntervalArcRowsWithWork forward.1 backward.1 bits).2+6 ≤ _
  rw [forwardValue,backwardValue]
  refine ⟨selected.trans (congrArg (binaryEncodeArcs code) filters),?_⟩
  unfold binaryDemandIntervalArcsWorkBudget
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add forwardCost backwardCost) filterCost) _

end OnlineReachabilityPreservers
