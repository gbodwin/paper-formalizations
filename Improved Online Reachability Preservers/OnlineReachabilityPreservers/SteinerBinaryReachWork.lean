import OnlineReachabilityPreservers.DeterministicListWork

/-! Reverse reachability with explicit bit comparisons of supplied vertex labels. -/

namespace OnlineReachabilityPreservers

open Finset

/-- Compare the two bit lists cell by cell, stopping at the first mismatch. -/
def binaryEqualWithWork : List Bool → List Bool → Bool × ℕ
  | [], [] => (true,3)
  | a::as, b::bs =>
    if a = b then
      let tail := binaryEqualWithWork as bs
      (tail.1,tail.2+5)
    else (false,5)
  | _, _ => (false,3)

theorem binaryEqualWithWork_spec (left right : List Bool) :
    let result := binaryEqualWithWork left right
    result.1 = decide (left = right) ∧ result.2 ≤ 5*left.length+3 := by
  induction left generalizing right with
  | nil => cases right <;> simp [binaryEqualWithWork]
  | cons a as ih =>
    cases right with
    | nil => simp [binaryEqualWithWork]
    | cons b bs =>
      by_cases equal : a = b
      · subst b
        obtain ⟨same,work⟩ := ih bs
        simp only [binaryEqualWithWork,List.cons.injEq,true_and,List.length_cons]
        refine ⟨same,?_⟩
        change (binaryEqualWithWork as bs).2+5 ≤ 5*(as.length+1)+3
        omega
      · simp [binaryEqualWithWork,equal]
        omega

/-- Scan an explicit list of bit strings with short-circuit membership. -/
def binaryKeyMemWithWork (key : List Bool) : List (List Bool) → Bool × ℕ
  | [] => (false,1)
  | current::rest =>
    let same := binaryEqualWithWork key current
    if same.1 then (true,5+same.2) else
      let later := binaryKeyMemWithWork key rest
      (later.1,5+same.2+later.2)

theorem binaryKeyMemWithWork_spec (key : List Bool) (keys : List (List Bool)) :
    let result := binaryKeyMemWithWork key keys
    result.1 = decide (key ∈ keys) ∧ result.2 ≤ 1+(5*key.length+8)*keys.length := by
  induction keys with
  | nil => simp [binaryKeyMemWithWork]
  | cons current rest ih =>
    obtain ⟨equal,firstWork⟩ := binaryEqualWithWork_spec key current
    obtain ⟨member,laterWork⟩ := ih
    by_cases same : key = current
    · have detected : (binaryEqualWithWork key current).1 = true := by simpa [same] using equal
      subst current
      constructor
      · simp [binaryKeyMemWithWork,detected]
      · simp [binaryKeyMemWithWork,detected,List.length_cons,Nat.mul_succ]
        omega
    · have absent : (binaryEqualWithWork key current).1 = false := by simpa [same] using equal
      constructor
      · simp [binaryKeyMemWithWork,absent,List.mem_cons,same,member]
      · simp [binaryKeyMemWithWork,absent,List.length_cons,Nat.mul_succ]
        omega

private def binaryReverseSweepWithWork (reachable : List (List Bool)) :
    List (List Bool × List Bool) → List (List Bool) → List (List Bool) × ℕ
  | [], seen => (seen,1)
  | arc::rest, seen =>
    let target := binaryKeyMemWithWork arc.2 reachable
    let source := binaryKeyMemWithWork arc.1 seen
    let next := if target.1 && !source.1 then arc.1::seen else seen
    let later := binaryReverseSweepWithWork reachable rest next
    (later.1,12+target.2+source.2+later.2)

/-- Encode the endpoints of the arcs in their original list order. -/
def binaryEncodeArcs {V : Type*} (code : V → List Bool) (arcs : List (V × V)) : List (List Bool × List Bool) :=
  arcs.map fun arc => (code arc.1,code arc.2)

variable {V : Type*} [LinearOrder V] [Fintype V]

omit [Fintype V] in
private theorem encoded_membership (code : V → List Bool) (injective : Function.Injective code)
    (width : ℕ) (bounded : ∀ v, (code v).length ≤ width) (key : V) (keys : List V) :
    let measured := binaryKeyMemWithWork (code key) (keys.map code)
    measured.1 = decide (key ∈ keys) ∧ measured.2 ≤ 1+(5*width+8)*keys.length := by
  obtain ⟨same,work⟩ := binaryKeyMemWithWork_spec (code key) (keys.map code)
  have mapped : decide (code key ∈ keys.map code) = decide (key ∈ keys) := by
    rw [decide_eq_decide]
    exact List.mem_map_of_injective injective
  simp only [List.length_map] at work
  refine ⟨same.trans mapped,work.trans ?_⟩
  have coefficient : 5*(code key).length+8 ≤ 5*width+8 := by have h := bounded key; omega
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ coefficient) _

private theorem binaryReverseSweepWithWork_spec (code : V → List Bool) (injective : Function.Injective code)
    (width : ℕ) (bounded : ∀ v, (code v).length ≤ width)
    (reachable : List V) (simpleReach : reachable.Nodup) (arcs : List (V × V)) (seen : List V)
    (simpleSeen : seen.Nodup) :
    let result := binaryReverseSweepWithWork (reachable.map code) (binaryEncodeArcs code arcs) (seen.map code)
    result.1 = (arcs.foldl (reversePredecessorStep reachable) seen).map code ∧
      result.2 ≤ 1+arcs.length*(14+2*((5*width+8)*Fintype.card V)) := by
  induction arcs generalizing seen with
  | nil => simp [binaryEncodeArcs,binaryReverseSweepWithWork]
  | cons arc rest ih =>
    let target := binaryKeyMemWithWork (code arc.2) (reachable.map code)
    let source := binaryKeyMemWithWork (code arc.1) (seen.map code)
    let next := reversePredecessorStep reachable seen arc
    have reachSize : reachable.length ≤ Fintype.card V := by
      rw [← List.toFinset_card_of_nodup simpleReach]
      exact card_le_univ _
    have seenSize : seen.length ≤ Fintype.card V := by
      rw [← List.toFinset_card_of_nodup simpleSeen]
      exact card_le_univ _
    obtain ⟨targetFound,targetCost⟩ := encoded_membership code injective width bounded arc.2 reachable
    obtain ⟨sourceFound,sourceCost⟩ := encoded_membership code injective width bounded arc.1 seen
    have nextValue : (if target.1 && !source.1 then code arc.1::seen.map code else seen.map code) =
        next.map code := by
      change target.1 = _ at targetFound
      change source.1 = _ at sourceFound
      rw [targetFound,sourceFound]
      by_cases incoming : arc.2 ∈ reachable <;> by_cases already : arc.1 ∈ seen <;>
        simp [next,reversePredecessorStep,incoming,already]
    let later := binaryReverseSweepWithWork (reachable.map code) (binaryEncodeArcs code rest) (next.map code)
    obtain ⟨same,laterCost⟩ := ih next (reversePredecessorStep_nodup reachable seen arc simpleSeen)
    have targetBudget : target.2 ≤ 1+(5*width+8)*Fintype.card V :=
      targetCost.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ reachSize) _)
    have sourceBudget : source.2 ≤ 1+(5*width+8)*Fintype.card V :=
      sourceCost.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ seenSize) _)
    change later.2 ≤ _ at laterCost
    simp only [binaryEncodeArcs,List.map_cons,binaryReverseSweepWithWork,List.foldl_cons,List.length_cons]
    change (binaryReverseSweepWithWork _ _ (if target.1 && !source.1 then code arc.1::seen.map code else seen.map code)).1 = _ ∧
      12+target.2+source.2+(binaryReverseSweepWithWork _ _ (if target.1 && !source.1 then code arc.1::seen.map code else seen.map code)).2 ≤ _
    rw [nextValue,Nat.succ_mul rest.length (14+2*((5*width+8)*Fintype.card V))]
    change later.1 = _ ∧ 12+target.2+source.2+later.2 ≤ _
    exact ⟨same,by omega⟩

/-- Bounded reverse search on an explicit list of encoded arcs. The tally
charges list operations and bit comparisons. Its counters are bookkeeping. -/
def binaryReachInListWithWork (arcs : List (List Bool × List Bool)) (target : List Bool) :
    ℕ → List (List Bool) × ℕ
  | 0 => ([target],2)
  | depth+1 =>
    let prior := binaryReachInListWithWork arcs target depth
    let sweep := binaryReverseSweepWithWork prior.1 arcs prior.1
    (sweep.1,4+prior.2+sweep.2)

/-- Given an injective bounded-width encoding, the bit-list search produces
the same ordered list as the word-work search within an explicit budget. -/
theorem binaryReachInListWithWork_spec (code : V → List Bool) (injective : Function.Injective code)
    (width : ℕ) (bounded : ∀ v, (code v).length ≤ width) (arcs : List (V × V)) (target : V) (depth : ℕ) :
    let measured := binaryReachInListWithWork (binaryEncodeArcs code arcs) (code target) depth
    let reference := reachInListWithWordWork arcs target depth
    measured.1 = reference.1.map code ∧
      measured.2 ≤ 2+depth*(5+arcs.length*(14+2*((5*width+8)*Fintype.card V))) := by
  induction depth with
  | zero => simp [binaryReachInListWithWork,reachInListWithWordWork]
  | succ depth ih =>
    let bits := binaryReachInListWithWork (binaryEncodeArcs code arcs) (code target) depth
    let words := reachInListWithWordWork arcs target depth
    obtain ⟨prior,spent⟩ := ih
    obtain ⟨simple,_,_⟩ := reachInListWithWordWork_spec arcs target depth
    obtain ⟨output,work⟩ := binaryReverseSweepWithWork_spec code injective width bounded
      words.1 simple arcs words.1 simple
    change bits.1 = words.1.map code at prior
    change bits.2 ≤ _ at spent
    change (binaryReverseSweepWithWork bits.1 (binaryEncodeArcs code arcs) bits.1).1 =
      (reachInListWithWordWork arcs target (depth+1)).1.map code ∧
      4+bits.2+(binaryReverseSweepWithWork bits.1 (binaryEncodeArcs code arcs) bits.1).2 ≤ _
    rw [reachInListWithWordWork_succ_output arcs target depth,prior,
      Nat.succ_mul depth (5+arcs.length*(14+2*((5*width+8)*Fintype.card V)))]
    exact ⟨output,by omega⟩

/-- Check one encoded demand by a reverse search and an encoded membership scan. -/
def binaryReachTestListWithWork (arcs : List (List Bool × List Bool)) (source target : List Bool) (depth : ℕ) :
    Bool × ℕ :=
  let found := binaryReachInListWithWork arcs target depth
  let member := binaryKeyMemWithWork source found.1
  (member.1,found.2+member.2+4)

/-- The encoded test agrees with the source-level list search. Binary label
construction and counter representation are outside this comparison tally. -/
theorem binaryReachTestListWithWork_spec (code : V → List Bool) (injective : Function.Injective code)
    (width : ℕ) (bounded : ∀ v, (code v).length ≤ width) (arcs : List (V × V)) (source target : V) (depth : ℕ) :
    let measured := binaryReachTestListWithWork (binaryEncodeArcs code arcs) (code source) (code target) depth
    measured.1 = (reachTestListWithWordWork arcs source target depth).1 ∧
      measured.2 ≤ 2+depth*(5+arcs.length*(14+2*((5*width+8)*Fintype.card V)))+
        (5*width+8)*Fintype.card V+5 := by
  let found := binaryReachInListWithWork (binaryEncodeArcs code arcs) (code target) depth
  let words := reachInListWithWordWork arcs target depth
  obtain ⟨same,work⟩ := binaryReachInListWithWork_spec code injective width bounded arcs target depth
  obtain ⟨simple,_,_⟩ := reachInListWithWordWork_spec arcs target depth
  have size : words.1.length ≤ Fintype.card V := by
    rw [← List.toFinset_card_of_nodup simple]
    exact card_le_univ _
  obtain ⟨member,scan⟩ := encoded_membership code injective width bounded source words.1
  obtain ⟨expected,_⟩ := memScanWithWordWork_spec source words.1
  have scanBound : (binaryKeyMemWithWork (code source) (words.1.map code)).2 ≤ 1+(5*width+8)*Fintype.card V :=
    scan.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ size) _)
  change found.1 = words.1.map code at same
  change found.2 ≤ _ at work
  change (binaryKeyMemWithWork (code source) found.1).1 = (memScanWithWordWork source words.1).1 ∧
    found.2+(binaryKeyMemWithWork (code source) found.1).2+4 ≤ _
  rw [same]
  exact ⟨member.trans expected.symm,by omega⟩

end OnlineReachabilityPreservers
