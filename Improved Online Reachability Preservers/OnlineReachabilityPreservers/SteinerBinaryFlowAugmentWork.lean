import OnlineReachabilityPreservers.SteinerBinaryFlowCutWork

/-! Unit augmentation of the signed binary flow cells on a supplied path. -/

namespace OnlineReachabilityPreservers

/-- Add one when `increase` is true and subtract one otherwise.
Magnitude grows by at most one bit, including when the sign changes at zero. -/
def shiftBinaryFlowWithWork (flow : BinarySignedWord) (increase : Bool) : BinarySignedWord × ℕ :=
  if increase = !flow.negative then
    let grown := addBinaryWordsWithWork flow.magnitude [] true
    (⟨flow.negative,grown.1⟩,grown.2+6)
  else
    let zero := binaryZeroWithWork flow.magnitude
    if zero.1 then (⟨!flow.negative,[true]⟩,zero.2+8)
    else
      let shrunk := binaryDecrementWithWork flow.magnitude
      (⟨flow.negative,shrunk.1⟩,zero.2+shrunk.2+8)

theorem shiftBinaryFlowWithWork_spec (flow : BinarySignedWord) (increase : Bool) :
    let out := shiftBinaryFlowWithWork flow increase
    out.1.value = flow.value + (if increase then 1 else -1) ∧
      out.1.magnitude.length ≤ flow.magnitude.length+1 ∧ out.2 ≤ 20*flow.magnitude.length+14 := by
  by_cases grows : increase = !flow.negative
  · subst increase
    rw [shiftBinaryFlowWithWork,ite_eq_left rfl]
    let grown := addBinaryWordsWithWork flow.magnitude [] true
    obtain ⟨value,width,work⟩ := addBinaryWordsWithWork_spec flow.magnitude [] true
    change binaryWordValue grown.1 = binaryWordValue flow.magnitude+0+1 at value
    change grown.1.length ≤ flow.magnitude.length+0+1 at width
    change grown.2 ≤ 20*(flow.magnitude.length+0)+5 at work
    change (BinarySignedWord.mk flow.negative grown.1).value = flow.value+(if !flow.negative then 1 else -1) ∧
      grown.1.length ≤ flow.magnitude.length+1 ∧ grown.2+6 ≤ 20*flow.magnitude.length+14
    refine ⟨?_,by omega,by omega⟩
    cases sign : flow.negative <;> simp [BinarySignedWord.value,sign,value]
    omega
  · rw [shiftBinaryFlowWithWork,ite_eq_right grows]
    have direction : increase = flow.negative := by
      cases increase <;> cases sign : flow.negative <;> simp_all
    subst increase
    let zero := binaryZeroWithWork flow.magnitude
    let shrunk := binaryDecrementWithWork flow.magnitude
    let out : BinarySignedWord × ℕ := if zero.1 then (⟨!flow.negative,[true]⟩,zero.2+8)
      else (⟨flow.negative,shrunk.1⟩,zero.2+shrunk.2+8)
    change out.1.value = flow.value+(if flow.negative then 1 else -1) ∧
      out.1.magnitude.length ≤ flow.magnitude.length+1 ∧ out.2 ≤ 20*flow.magnitude.length+14
    unfold out
    obtain ⟨zeroValue,zeroWork⟩ := binaryZeroWithWork_spec flow.magnitude
    change zero.1 = decide (binaryWordValue flow.magnitude = 0) at zeroValue
    change zero.2 ≤ 4*flow.magnitude.length+3 at zeroWork
    by_cases empty : binaryWordValue flow.magnitude = 0
    · rw [zeroValue,decide_eq_true empty]
      refine ⟨?_,by simp,?_⟩
      · change (BinarySignedWord.mk (!flow.negative) [true]).value =
          flow.value+(if flow.negative then 1 else -1)
        cases sign : flow.negative <;> simp [BinarySignedWord.value,sign,empty] <;> decide
      · change zero.2+8 ≤ 20*flow.magnitude.length+14
        omega
    · rw [zeroValue,decide_eq_false empty]
      obtain ⟨width,work,value⟩ := binaryDecrementWithWork_spec flow.magnitude
      have changed : binaryWordValue shrunk.1+1 = binaryWordValue flow.magnitude :=
        value (Nat.pos_of_ne_zero empty)
      change shrunk.1.length = flow.magnitude.length at width
      change shrunk.2 ≤ 5*flow.magnitude.length+3 at work
      refine ⟨?_,?_,?_⟩
      · change (BinarySignedWord.mk flow.negative shrunk.1).value =
          flow.value+(if flow.negative then 1 else -1)
        cases sign : flow.negative <;> simp [BinarySignedWord.value,sign] <;> omega
      · change shrunk.1.length ≤ flow.magnitude.length+1
        omega
      · change zero.2+shrunk.2+8 ≤ 20*flow.magnitude.length+14
        omega

/-- Test membership of one encoded arc, comparing each of its two labels. -/
def binaryArcMemWithWork (arc : List Bool × List Bool) : List (List Bool × List Bool) → Bool × ℕ
  | [] => (false,2)
  | e::rest =>
    let u := binaryEqualWithWork arc.1 e.1
    let v := binaryEqualWithWork arc.2 e.2
    if u.1 && v.1 then (true,u.2+v.2+7) else
      let tail := binaryArcMemWithWork arc rest
      (tail.1,u.2+v.2+tail.2+8)

private theorem binaryArcMemWithWork_spec {V : Type*} [DecidableEq V]
    (code : V → List Bool) (injective : Function.Injective code)
    (w : ℕ) (bounded : ∀ v, (code v).length ≤ w) (arc : V × V) (path : List (V × V)) :
    let out := binaryArcMemWithWork (code arc.1,code arc.2) (binaryEncodeArcs code path)
    out.1 = decide (arc ∈ path) ∧ out.2 ≤ 2+path.length*(10*w+14) := by
  have widthU := bounded arc.1
  have widthV := bounded arc.2
  induction path with
  | nil => simp [binaryArcMemWithWork,binaryEncodeArcs]
  | cons e rest ih =>
    let u := binaryEqualWithWork (code arc.1) (code e.1)
    let v := binaryEqualWithWork (code arc.2) (code e.2)
    let tail := binaryArcMemWithWork (code arc.1,code arc.2) (binaryEncodeArcs code rest)
    obtain ⟨uValue,uWork⟩ := binaryEqualWithWork_spec (code arc.1) (code e.1)
    obtain ⟨vValue,vWork⟩ := binaryEqualWithWork_spec (code arc.2) (code e.2)
    obtain ⟨tailValue,tailWork⟩ := ih
    have head : (u.1 && v.1) = decide (arc = e) := by
      change u.1 = _ at uValue
      change v.1 = _ at vValue
      rw [uValue,vValue]
      simp only [injective.eq_iff,Prod.ext_iff]
      by_cases first : arc.1 = e.1 <;> simp [first]
    change u.2 ≤ 5*(code arc.1).length+3 at uWork
    change v.2 ≤ 5*(code arc.2).length+3 at vWork
    change tail.2 ≤ 2+rest.length*(10*w+14) at tailWork
    change (if u.1 && v.1 then (true,u.2+v.2+7) else (tail.1,u.2+v.2+tail.2+8)).1 =
        decide (arc ∈ e::rest) ∧
      (if u.1 && v.1 then (true,u.2+v.2+7) else (tail.1,u.2+v.2+tail.2+8)).2 ≤
        2+(rest.length+1)*(10*w+14)
    rw [head,Nat.succ_mul rest.length]
    by_cases same : arc = e
    · rw [decide_eq_true same]
      exact ⟨(decide_eq_true (same ▸ List.mem_cons_self)).symm,by simp only [ite_true]; omega⟩
    · rw [decide_eq_false same]
      exact ⟨by simpa [same] using tailValue,by simp only [Bool.false_eq_true,ite_false]; omega⟩

private def shiftBinaryFlowIfUsedWithWork (flow : BinarySignedWord) (forward backward : Bool) :
    BinarySignedWord × ℕ :=
  if forward = backward then (flow,2) else
    let out := shiftBinaryFlowWithWork flow forward
    (out.1,out.2+2)

private theorem shiftBinaryFlowIfUsedWithWork_spec (flow : BinarySignedWord) (forward backward : Bool) :
    let out := shiftBinaryFlowIfUsedWithWork flow forward backward
    out.1.value = flow.value + (if forward then 1 else 0) - (if backward then 1 else 0) ∧
      out.1.magnitude.length ≤ flow.magnitude.length+1 ∧ out.2 ≤ 20*flow.magnitude.length+16 := by
  have forwardSpec := shiftBinaryFlowWithWork_spec flow true
  have backwardSpec := shiftBinaryFlowWithWork_spec flow false
  cases forward <;> cases backward <;> simp_all [shiftBinaryFlowIfUsedWithWork]
  omega

/-- Scan the supplied flow table, applying the two signed path indicators per row.
Keys and capacity words stay in their original order. -/
def augmentBinaryFlowRowsWithWork (path : List (List Bool × List Bool)) :
    List (BinaryCapacityFlowRow (List Bool × List Bool)) →
      List (BinaryCapacityFlowRow (List Bool × List Bool)) × ℕ
  | [] => ([],2)
  | row::rest =>
    let forward := binaryArcMemWithWork row.arc path
    let backward := binaryArcMemWithWork row.arc.swap path
    let changed := shiftBinaryFlowIfUsedWithWork row.flow forward.1 backward.1
    let tail := augmentBinaryFlowRowsWithWork path rest
    ({ row with flow := changed.1 }::tail.1,forward.2+backward.2+changed.2+tail.2+8)

def augmentBinaryFlowRowsWorkBudget (rows path labels flowWidth : ℕ) : ℕ :=
  2+rows*(2*(2+path*(10*labels+14))+20*flowWidth+24)

variable {V : Type*} [LinearOrder V]

/-- The updated words encode the exact reference flow on the same cells.
The path is supplied, and repeated path rows are interpreted by membership. -/
theorem augmentBinaryFlowRowsWithWork_refines (code : V → List Bool) (injective : Function.Injective code)
    (w : ℕ) (bounded : ∀ v, (code v).length ≤ w) (flow : ArcFlow V)
    (rows : List (BinaryCapacityFlowRow (V × V))) (path : List (V × V)) (width : ℕ)
    (decoded : ∀ row ∈ rows, row.flow.value = flow row.arc ∧ row.flow.magnitude.length ≤ width) :
    let out := augmentBinaryFlowRowsWithWork (binaryEncodeArcs code path) (binaryEncodeCapacityFlowRows code rows)
    ∃ updated : List (BinaryCapacityFlowRow (V × V)),
      out.1 = binaryEncodeCapacityFlowRows code updated ∧
      updated.map (fun row => (row.arc,row.capacity)) = rows.map (fun row => (row.arc,row.capacity)) ∧
      (∀ row ∈ updated, row.flow.value = augmentArcFlow flow path.toFinset row.arc ∧
        row.flow.magnitude.length ≤ width+1) ∧
      out.2 ≤ augmentBinaryFlowRowsWorkBudget rows.length path.length w width := by
  induction rows with
  | nil => exact ⟨[],rfl,rfl,by simp,by simp [augmentBinaryFlowRowsWithWork,augmentBinaryFlowRowsWorkBudget,
      binaryEncodeCapacityFlowRows]⟩
  | cons row rows ih =>
    let key := (code row.arc.1,code row.arc.2)
    let forward := binaryArcMemWithWork key (binaryEncodeArcs code path)
    let backward := binaryArcMemWithWork key.swap (binaryEncodeArcs code path)
    let shift := shiftBinaryFlowIfUsedWithWork row.flow forward.1 backward.1
    let front := { row with flow := shift.1 }
    let tail := augmentBinaryFlowRowsWithWork (binaryEncodeArcs code path) (binaryEncodeCapacityFlowRows code rows)
    obtain ⟨rowValue,rowWidth⟩ := decoded row List.mem_cons_self
    obtain ⟨forwardValue,forwardCost⟩ := binaryArcMemWithWork_spec code injective w bounded row.arc path
    obtain ⟨backwardValue,backwardCost⟩ := binaryArcMemWithWork_spec code injective w bounded row.arc.swap path
    obtain ⟨updated,sameTail,sameKeys,exactTail,tailCost⟩ := ih (fun r mem => decoded r (List.mem_cons_of_mem _ mem))
    obtain ⟨shiftValue,shiftWidth,shiftCost⟩ := shiftBinaryFlowIfUsedWithWork_spec row.flow forward.1 backward.1
    change tail.1 = _ at sameTail
    change forward.1 = _ at forwardValue
    change backward.1 = _ at backwardValue
    change forward.2 ≤ 2+path.length*(10*w+14) at forwardCost
    change backward.2 ≤ 2+path.length*(10*w+14) at backwardCost
    change shift.1.value = _ at shiftValue
    change shift.1.magnitude.length ≤ row.flow.magnitude.length+1 at shiftWidth
    change shift.2 ≤ 20*row.flow.magnitude.length+16 at shiftCost
    refine ⟨front::updated,?_,?_,?_,?_⟩
    · change (⟨key,row.capacity,shift.1⟩::tail.1) =
        ⟨key,row.capacity,shift.1⟩::binaryEncodeCapacityFlowRows code updated
      exact congrArg _ sameTail
    · exact congrArg ((row.arc,row.capacity)::·) sameKeys
    · intro item member
      rcases List.mem_cons.mp member with rfl | present
      · refine ⟨?_,by change shift.1.magnitude.length ≤ width+1; omega⟩
        change shift.1.value = flow row.arc + (if row.arc ∈ path.toFinset then 1 else 0) -
          (if row.arc.swap ∈ path.toFinset then 1 else 0)
        rw [shiftValue,forwardValue,backwardValue,rowValue]
        simp
      · exact exactTail item present
    · let cost := 2*(2+path.length*(10*w+14))+20*width+24
      change tail.2 ≤ 2+rows.length*cost at tailCost
      change forward.2+backward.2+shift.2+tail.2+8 ≤ 2+(rows.length+1)*cost
      rw [Nat.succ_mul rows.length]
      dsimp [cost] at tailCost ⊢
      omega

end OnlineReachabilityPreservers
