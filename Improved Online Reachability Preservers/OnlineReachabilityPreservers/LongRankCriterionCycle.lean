import OnlineReachabilityPreservers.RiverDetourComponents

/-! Two long portions of a cycle in one parent row at the original width. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

private def longCycleCenterVertex (m : ℕ) (a : Fin 16) : Fin (2*m+16) :=
  ⟨if a.val < 8 then a.val else m+a.val, by split <;> omega⟩

private theorem longCycleCenterVertex_injective (m : ℕ) : Function.Injective (longCycleCenterVertex m) := by
  intro a b equal
  have eq := congrArg Fin.val equal
  change (if a.val < 8 then a.val else m+a.val) = (if b.val < 8 then b.val else m+b.val) at eq
  apply Fin.ext
  split at eq <;> split at eq <;> omega

private def longCycleCenter (m : ℕ) : List (Fin (2*m+16)) := List.ofFn (longCycleCenterVertex m)

private theorem longCycleCenter_simple (m : ℕ) : (longCycleCenter m).Nodup :=
  List.nodup_ofFn.mpr (longCycleCenterVertex_injective m)

private theorem longCycleCenter_contains {m : ℕ} {x : Fin (2*m+16)} :
    x ∈ longCycleCenter m ↔ x.val < 8 ∨ m+8 ≤ x.val ∧ x.val < m+16 := by
  constructor
  · intro on
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp on
    change (if i.val<8 then i.val else m+i.val) < 8 ∨
      m+8 ≤ (if i.val<8 then i.val else m+i.val) ∧ (if i.val<8 then i.val else m+i.val) < m+16
    split <;> omega
  · intro on
    apply List.mem_ofFn.mpr
    rcases on with first | ⟨low,high⟩
    · let a : Fin 16 := ⟨x.val,by omega⟩
      refine ⟨a,Fin.ext ?_⟩
      change (if x.val < 8 then x.val else m+x.val) = x.val
      exact ite_eq_left first
    · let a : Fin 16 := ⟨x.val-m,by omega⟩
      refine ⟨a,Fin.ext ?_⟩
      change (if x.val-m < 8 then x.val-m else m+(x.val-m)) = x.val
      rw [ite_eq_right (by omega : ¬ x.val-m < 8)]
      omega

private theorem longCycleCenter_position_at (m : ℕ) (a : Fin 16) :
    (longCycleCenter m).idxOf (longCycleCenterVertex m a) = a.val := by
  have valid : a.val < (longCycleCenter m).length := by simp [longCycleCenter]
  have atIndex : (longCycleCenter m)[a.val]'valid = longCycleCenterVertex m a := List.getElem_ofFn valid
  rw [← atIndex,(longCycleCenter_simple m).idxOf_getElem]

private theorem longCycleCenter_position {m : ℕ} {x : Fin (2*m+16)} (on : x ∈ longCycleCenter m) :
    (longCycleCenter m).idxOf x = if x.val < 8 then x.val else x.val-m := by
  obtain ⟨a,rfl⟩ := List.mem_ofFn.mp on
  rw [longCycleCenter_position_at]
  change a.val = if (if a.val<8 then a.val else m+a.val)<8 then
    (if a.val<8 then a.val else m+a.val) else (if a.val<8 then a.val else m+a.val)-m
  by_cases small : a.val < 8
  · simp [small]
  · simp only [small,ite_false]
    rw [ite_eq_right (by omega : ¬ m+a.val < 8)]
    omega

private def longCycleSuccessor {m : ℕ} (x : Fin (2*m+16)) : Fin (2*m+16) :=
  ⟨if x.val+1 < 2*m+16 then x.val+1 else 0, by split <;> omega⟩

private theorem longCycleSuccessor_ne {m : ℕ} (x : Fin (2*m+16)) : x ≠ longCycleSuccessor x := by
  intro equal
  have value := congrArg Fin.val equal
  change x.val = if x.val+1<2*m+16 then x.val+1 else 0 at value
  split at value <;> omega

private theorem longCycleSuccessor_injective (m : ℕ) : Function.Injective (@longCycleSuccessor m) := by
  intro a b equal
  have eq := congrArg Fin.val equal
  change (if a.val+1<2*m+16 then a.val+1 else 0) = (if b.val+1<2*m+16 then b.val+1 else 0) at eq
  apply Fin.ext
  split at eq <;> split at eq <;> omega

private def longCycleExternalTail (m : ℕ) (i : Fin (2*m+3)) : Fin (2*m+16) :=
  ⟨if i.val ≤ m+1 then 6+i.val else i.val+13,by split <;> omega⟩

private theorem longCycleExternalTail_injective (m : ℕ) : Function.Injective (longCycleExternalTail m) := by
  intro a b equal
  have eq := congrArg Fin.val equal
  change (if a.val≤m+1 then 6+a.val else a.val+13) = (if b.val≤m+1 then 6+b.val else b.val+13) at eq
  apply Fin.ext
  split at eq <;> split at eq <;> omega

private theorem longCycleExternalTail_interval {m : ℕ} {i : Fin (2*m+3)} (nonzero : i.val ≠ 0) :
    let v := (longCycleExternalTail m i).val
    (7 ≤ v ∧ v ≤ m+7) ∨ (m+15 ≤ v ∧ v ≤ 2*m+15) := by
  change let v := if i.val≤m+1 then 6+i.val else i.val+13
    (7 ≤ v ∧ v ≤ m+7) ∨ (m+15 ≤ v ∧ v ≤ 2*m+15)
  dsimp only
  split <;> omega

/-- One row on the two eight-vertex portions and one row per step in
the two connecting chains. -/
def longRankCycleRows {m : ℕ} (i : Fin (2*m+3)) : List (Fin (2*m+16)) :=
  if i.val = 0 then longCycleCenter m else
    let x := longCycleExternalTail m i
    [x,longCycleSuccessor x]

theorem longRankCycleRows_simple {m : ℕ} (i : Fin (2*m+3)) : (longRankCycleRows i).Nodup := by
  unfold longRankCycleRows
  split
  · exact longCycleCenter_simple m
  · simp [longCycleSuccessor_ne]

private theorem longRankCycleRows_external_step {m : ℕ} {i : Fin (2*m+3)} {x y : Fin (2*m+16)}
    (nonzero : i.val ≠ 0) (step : Before (@longRankCycleRows m) i x y) :
    x = longCycleExternalTail m i ∧ y = longCycleSuccessor x := by
  unfold SourceAudit.BeforeIn at step
  simp only [longRankCycleRows,nonzero,ite_false,List.mem_cons,List.not_mem_nil,or_false] at step
  obtain ⟨xOn,yOn,ordered⟩ := step
  rcases xOn with hx | hx <;> rcases yOn with hy | hy
  · rw [hx,hy] at ordered
    exact (Nat.lt_irrefl _ ordered).elim
  · exact ⟨hx,hy.trans (congrArg longCycleSuccessor hx).symm⟩
  · rw [hx,hy] at ordered
    simp [longCycleSuccessor_ne] at ordered
  · rw [hx,hy] at ordered
    exact (Nat.lt_irrefl _ ordered).elim

private def longCycleProgress {m : ℕ} (x : Fin (2*m+16)) : ℕ :=
  if x.val = 0 then m+1 else if m+15 ≤ x.val then x.val-(m+15) else x.val-7

private theorem longCycleProgress_external_step {m : ℕ} {i : Fin (2*m+3)} {x y : Fin (2*m+16)}
    (nonzero : i.val ≠ 0) (step : Before (@longRankCycleRows m) i x y) :
    longCycleProgress y = longCycleProgress x+1 := by
  obtain ⟨hx,rfl⟩ := longRankCycleRows_external_step nonzero step
  have between := longCycleExternalTail_interval nonzero
  rw [← hx] at between
  unfold longCycleProgress
  change (if (if x.val+1<2*m+16 then x.val+1 else 0)=0 then m+1 else
    if m+15 ≤ (if x.val+1<2*m+16 then x.val+1 else 0) then
      (if x.val+1<2*m+16 then x.val+1 else 0)-(m+15) else
      (if x.val+1<2*m+16 then x.val+1 else 0)-7) =
    (if x.val=0 then m+1 else if m+15≤x.val then x.val-(m+15) else x.val-7)+1
  rcases between with ⟨first,upper⟩ | ⟨second,upper⟩
  · rw [ite_eq_left (by omega : x.val+1 < 2*m+16),ite_eq_right (by omega : x.val+1 ≠ 0),
        ite_eq_right (by omega : ¬ m+15 ≤ x.val+1),ite_eq_right (by omega : x.val ≠ 0),
        ite_eq_right (by omega : ¬ m+15 ≤ x.val)]
    omega
  · rw [ite_eq_right (by omega : x.val ≠ 0),ite_eq_left second]
    by_cases wraps : x.val+1 < 2*m+16
    · rw [ite_eq_left wraps,ite_eq_right (by omega : x.val+1 ≠ 0),ite_eq_left (by omega : m+15 ≤ x.val+1)]
      omega
    · rw [ite_eq_right wraps,ite_eq_left rfl]
      omega


private theorem longCycle_external_tail_in_center {m : ℕ} {i : Fin (2*m+3)} {x y : Fin (2*m+16)}
    (nonzero : i.val ≠ 0) (step : Before (@longRankCycleRows m) i x y) (on : x ∈ longCycleCenter m) :
    x.val = 7 ∨ x.val = m+15 := by
  have range := longCycleExternalTail_interval nonzero
  rw [← (longRankCycleRows_external_step nonzero step).1] at range
  rcases range with first | second <;>
    rcases longCycleCenter_contains.mp on with early | late <;> omega

private theorem longCycle_external_head_in_center {m : ℕ} {i : Fin (2*m+3)} {x y : Fin (2*m+16)}
    (nonzero : i.val ≠ 0) (step : Before (@longRankCycleRows m) i x y) (on : y ∈ longCycleCenter m) :
    y.val = 0 ∨ y.val = m+8 := by
  obtain ⟨hx,rfl⟩ := longRankCycleRows_external_step nonzero step
  have range := longCycleExternalTail_interval nonzero
  rw [← hx] at range
  replace on := longCycleCenter_contains.mp on
  change (if x.val+1<2*m+16 then x.val+1 else 0) < 8 ∨
    m+8 ≤ (if x.val+1<2*m+16 then x.val+1 else 0) ∧
      (if x.val+1<2*m+16 then x.val+1 else 0) < m+16 at on
  change (if x.val+1<2*m+16 then x.val+1 else 0)=0 ∨
    (if x.val+1<2*m+16 then x.val+1 else 0)=m+8
  by_cases a : x.val+1 < 2*m+16
  · simp only [a,ite_true] at on ⊢
    rcases range with first | second <;> rcases on with firstHead | secondHead <;> omega
  · simp [a]

private theorem longCycle_external_start_progress {m : ℕ} {i : Fin (2*m+3)} {x y : Fin (2*m+16)}
    (nonzero : i.val ≠ 0) (step : Before (@longRankCycleRows m) i x y) (on : x ∈ longCycleCenter m) :
    longCycleProgress x = 0 := by
  unfold longCycleProgress
  rcases longCycle_external_tail_in_center nonzero step on with early | late
  · simp [early,show ¬ m+15 ≤ 7 by omega]
  · simp [late]

private theorem longCycle_external_end_progress {m : ℕ} {i : Fin (2*m+3)} {x y : Fin (2*m+16)}
    (nonzero : i.val ≠ 0) (step : Before (@longRankCycleRows m) i x y) (on : y ∈ longCycleCenter m) :
    longCycleProgress y = m+1 := by
  unfold longCycleProgress
  rcases longCycle_external_head_in_center nonzero step on with early | late
  · simp [early]
  · simp only [late,show m+8 ≠ 0 by omega,show ¬ m+15 ≤ m+8 by omega,ite_false]
    omega

private theorem longCycle_centerStep_indices {m : ℕ} {i : Fin (2*m+3)} {x y : Fin (2*m+16)}
    (zero : i.val = 0) (step : Before (@longRankCycleRows m) i x y) :
    x ∈ longCycleCenter m ∧ y ∈ longCycleCenter m ∧
      (longCycleCenter m).idxOf x < (longCycleCenter m).idxOf y := by
  simpa only [SourceAudit.BeforeIn,longRankCycleRows,zero,ite_true] using step

private theorem longCycle_center_no_step_at_last {m : ℕ} {i : Fin (2*m+3)} {x y : Fin (2*m+16)}
    (zero : i.val = 0) (last : x.val = m+15) (step : Before (@longRankCycleRows m) i x y) : False := by
  obtain ⟨xOn,yOn,ordered⟩ := longCycle_centerStep_indices zero step
  have xIndex : (longCycleCenter m).idxOf x = 15 := by
    rw [longCycleCenter_position xOn,last,ite_eq_right (by omega : ¬ m+15 < 8)]
    omega
  have yIndex := List.idxOf_lt_length_of_mem yOn
  have length : (longCycleCenter m).length = 16 := by simp [longCycleCenter]
  omega

/-- The original system excludes full bridges through the length of one
connecting chain. -/
theorem longRankCycleRows_full_free {m k : ℕ} (positive : 0 < m) (cutoff : k ≤ m+1) :
    BridgeFree (Before (@longRankCycleRows m)) k := by
  intro d small
  refine ⟨fun b => ?_⟩
  by_cases center : b.river.val = 0
  · have external (i : Fin (d+1)) : (b.arc i).val ≠ 0 :=
      fun zero => b.river_ne_arc i (Fin.ext (center.trans zero.symm))
    obtain ⟨begins,ends,_⟩ := longCycle_centerStep_indices center b.riverStep
    have firstProgress : longCycleProgress (b.vertex 0) = 0 :=
      longCycle_external_start_progress (external 0) (b.arcStep 0) begins
    have lastProgress : longCycleProgress (b.vertex (Fin.last (d+1))) = m+1 :=
      longCycle_external_end_progress (external (Fin.last d)) (b.arcStep (Fin.last d)) ends
    have along (i : Fin (d+2)) : longCycleProgress (b.vertex i) = i.val := by
      refine Fin.induction firstProgress ?_ i
      intro j ih
      rw [longCycleProgress_external_step (external j) (b.arcStep j),ih]
      rfl
    have tooLong := along (Fin.last (d+1))
    rw [lastProgress] at tooLong
    change m+1 = d+1 at tooLong
    omega
  · obtain ⟨source,target⟩ := longRankCycleRows_external_step center b.riverStep
    by_cases first : (b.vertex 0).val = 7
    · let last := Fin.last d
      have actualLast : Before (@longRankCycleRows m) (b.arc last)
          (b.vertex last.castSucc) (b.vertex (Fin.last (d+1))) := b.arcStep last
      have value : (b.vertex (Fin.last (d+1))).val = 8 := by
        rw [target]
        change (if (b.vertex 0).val+1<2*m+16 then (b.vertex 0).val+1 else 0) = 8
        rw [first,ite_eq_left (by omega : 7+1 < 2*m+16)]
      have lastExternal : (b.arc last).val ≠ 0 := by
        intro zero
        rcases longCycleCenter_contains.mp (longCycle_centerStep_indices zero actualLast).2.1 with left | right <;> omega
      obtain ⟨lastSource,lastTarget⟩ := longRankCycleRows_external_step lastExternal actualLast
      have same := longCycleSuccessor_injective m (target.symm.trans lastTarget)
      exact b.river_ne_arc last (longCycleExternalTail_injective m (source.symm.trans (same.trans lastSource)))
    · have firstExternal : (b.arc 0).val ≠ 0 := by
        intro zero
        have on := (longCycle_centerStep_indices zero (b.arcStep 0)).1
        have last := (longCycle_external_tail_in_center center b.riverStep on).resolve_left first
        exact longCycle_center_no_step_at_last zero last (b.arcStep 0)
      have same := (longRankCycleRows_external_step firstExternal (b.arcStep 0)).1
      exact b.river_ne_arc 0 (longCycleExternalTail_injective m (source.symm.trans same))

/-- The two blocks have 16 incidences. Each connecting row contributes
exactly two incidences. -/
theorem longRankCycleRows_mass (m : ℕ) :
    (∑ i : Fin (2*m+3), (longRankCycleRows i).length) = 4*m+20 := by
  let root : Fin (2*m+3) := ⟨0,by omega⟩
  let others := (univ : Finset (Fin (2*m+3))).erase root
  have rest (i : Fin (2*m+3)) (on : i ∈ others) : (longRankCycleRows i).length = 2 := by
    have nonzero : i.val ≠ 0 := fun eq => (mem_erase.mp on).1 (Fin.ext eq)
    simp [longRankCycleRows,nonzero]
  have total : others.card = 2*m+2 := by simp [others]
  have center : (longRankCycleRows root).length = 16 := by simp [root,longRankCycleRows,longCycleCenter]
  calc
    _ = (∑ i ∈ others, (longRankCycleRows i).length) + (longRankCycleRows root).length :=
      (sum_erase_add _ _ (mem_univ root)).symm
    _ = (2*m+2)*2+16 := by rw [sum_congr rfl rest,sum_const,smul_eq_mul,total,center]
    _ = _ := by omega

/-- The prescribed original factor-four path width is eight. -/
theorem longRankCycleRows_frozen_width {m : ℕ} (large : 27 ≤ m) :
    4*(∑ i : Fin (2*m+3), (longRankCycleRows i).length)/(2*m+3) = 8 := by
  rw [longRankCycleRows_mass]
  have positive : 0 < 2*m+3 := by omega
  have above : 8 ≤ 4*(4*m+20)/(2*m+3) := (Nat.le_div_iff_mul_le positive).mpr (by omega)
  have below : 4*(4*m+20)/(2*m+3) < 9 := (Nat.div_lt_iff_lt_mul positive).mpr (by omega)
  omega


abbrev LongRankCyclePiece (m : ℕ) := ListBlockIndex (@longRankCycleRows m) 8

/-- The standard width-eight path blocks. -/
def longRankCyclePieces (m : ℕ) := splitListPaths (@longRankCycleRows m) 8

private theorem longRankCyclePiece_step {m : ℕ} {i : LongRankCyclePiece m} {x y : Fin (2*m+16)}
    (before : Before (longRankCyclePieces m) i x y) : Before (@longRankCycleRows m) i.fst x y :=
  listBefore_of_sublist (paths := fun j : LongRankCyclePiece m => longRankCycleRows j.fst)
    (longRankCycleRows_simple i.fst) List.filter_sublist before

private theorem longRankCyclePiece_center_cannot_start_external {m : ℕ} {i j : LongRankCyclePiece m}
    {x y z : Fin (2*m+16)} (center : i.fst.val = 0) (external : j.fst.val ≠ 0)
    (left : Before (longRankCyclePieces m) i x y) (right : Before (longRankCyclePieces m) j x z) : False := by
  obtain ⟨xOn,yOn,ordered⟩ := longCycle_centerStep_indices center (longRankCyclePiece_step left)
  have xSlot : (longCycleCenter m).idxOf x/8 = i.snd.val := by
    simpa only [longRankCycleRows,center,ite_true] using (mem_localPathBlock.mp left.1).2
  have ySlot : (longCycleCenter m).idxOf y/8 = i.snd.val := by
    simpa only [longRankCycleRows,center,ite_true] using (mem_localPathBlock.mp left.2.1).2
  have yEnd : (longCycleCenter m).idxOf y < 16 := by
    have bound := List.idxOf_lt_length_of_mem yOn
    simpa only [longCycleCenter,List.length_ofFn] using bound
  rcases longCycle_external_tail_in_center external (longRankCyclePiece_step right) xOn with low | high
  · rw [longCycleCenter_position xOn,low] at ordered xSlot
    simp only [Nat.reduceLT,ite_true,Nat.reduceDiv] at ordered xSlot
    omega
  · rw [longCycleCenter_position xOn,high,ite_eq_right (by omega : ¬ m+15<8)] at ordered xSlot
    have last : m+15-m = 15 := by omega
    rw [last] at ordered xSlot
    omega

private theorem longRankCyclePiece_unique_source {m : ℕ} {i j : LongRankCyclePiece m} {x y z : Fin (2*m+16)}
    (left : Before (longRankCyclePieces m) i x y) (right : Before (longRankCyclePieces m) j x z) : i = j := by
  by_contra distinct
  apply splitListPaths_disjoint distinct ?_ left.1 right.1
  by_cases center : i.fst.val = 0 <;> by_cases other : j.fst.val = 0
  · exact Fin.ext (center.trans other.symm)
  · exact (longRankCyclePiece_center_cannot_start_external center other left right).elim
  · exact (longRankCyclePiece_center_cannot_start_external other center right left).elim
  · apply longCycleExternalTail_injective m
    exact (longRankCycleRows_external_step center (longRankCyclePiece_step left)).1.symm.trans
      (longRankCycleRows_external_step other (longRankCyclePiece_step right)).1

/-- Each vertex has one outgoing piece. The actual pieces exclude every
full bridge regardless of the cutoff. -/
theorem longRankCyclePieces_full_free (m k : ℕ) : BridgeFree (Before (longRankCyclePieces m)) k := by
  intro d _
  exact ⟨fun b => b.river_ne_arc 0 (longRankCyclePiece_unique_source b.riverStep (b.arcStep 0))⟩

private theorem longRankCyclePiece_step_of_same_slot {m : ℕ} {i : Fin (2*m+3)} {x y : Fin (2*m+16)}
    (before : Before (@longRankCycleRows m) i x y)
    (slot : (longRankCycleRows i).idxOf x/8 = (longRankCycleRows i).idxOf y/8) :
    ∃ j : LongRankCyclePiece m, j.fst = i ∧ Before (longRankCyclePieces m) j x y := by
  let row := longRankCycleRows i
  let block := row.idxOf x/8
  have bound : block < blockCount row.toFinset 8 := by
    rw [blockCount,List.toFinset_card_of_nodup (longRankCycleRows_simple i)]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (List.idxOf_lt_length_of_mem before.1).le)
  let j : LongRankCyclePiece m := ⟨i,⟨block,bound⟩⟩
  have xOn : x ∈ longRankCyclePieces m j := mem_localPathBlock.mpr ⟨before.1,rfl⟩
  have yOn : y ∈ longRankCyclePieces m j := mem_localPathBlock.mpr ⟨before.2.1,slot.symm⟩
  rcases listBefore_total xOn yOn (listBefore_ne before) with forward | reverse
  · exact ⟨j,rfl,forward⟩
  · exact ((Nat.lt_asymm before.2.2) (longRankCyclePiece_step reverse).2.2).elim

private theorem longRankCycleRows_external_forward {m : ℕ} (i : Fin (2*m+3)) (nonzero : i.val ≠ 0) :
    Before (@longRankCycleRows m) i (longCycleExternalTail m i) (longCycleSuccessor (longCycleExternalTail m i)) := by
  simp [SourceAudit.BeforeIn,longRankCycleRows,nonzero,longCycleSuccessor_ne,
    (longCycleSuccessor_ne (longCycleExternalTail m i)).symm]

private theorem longRankCyclePiece_successor_step {m : ℕ} (x : Fin (2*m+16)) :
    ∃ j : LongRankCyclePiece m, Before (longRankCyclePieces m) j x (longCycleSuccessor x) := by
  have external (i : Fin (2*m+3)) (nonzero : i.val ≠ 0) (same : longCycleExternalTail m i = x) :
      ∃ j : LongRankCyclePiece m, Before (longRankCyclePieces m) j x (longCycleSuccessor x) := by
    have step := longRankCycleRows_external_forward i nonzero
    rw [same] at step
    have short : (longRankCycleRows i).length = 2 := by simp [longRankCycleRows,nonzero]
    have covered {v} (on : v ∈ longRankCycleRows i) : (longRankCycleRows i).idxOf v/8 = 0 := by
      apply Nat.div_eq_of_lt
      have position := List.idxOf_lt_length_of_mem on
      rw [short] at position
      omega
    obtain ⟨j,_,forward⟩ := longRankCyclePiece_step_of_same_slot step
      ((covered step.1).trans (covered step.2.1).symm)
    exact ⟨j,forward⟩
  by_cases left : 7 ≤ x.val ∧ x.val ≤ m+7
  · let i : Fin (2*m+3) := ⟨x.val-6,by omega⟩
    apply external i (by change x.val-6 ≠ 0; omega)
    apply Fin.ext
    change (if x.val-6≤m+1 then 6+(x.val-6) else x.val-6+13) = x.val
    rw [ite_eq_left (by omega : x.val-6≤m+1)]
    omega
  · by_cases right : m+15 ≤ x.val
    · let i : Fin (2*m+3) := ⟨x.val-13,by omega⟩
      apply external i (by change x.val-13 ≠ 0; omega)
      apply Fin.ext
      change (if x.val-13≤m+1 then 6+(x.val-13) else x.val-13+13) = x.val
      rw [ite_eq_right (by omega : ¬ x.val-13≤m+1)]
      omega
    · have region : x.val < 7 ∨ m+8 ≤ x.val ∧ x.val < m+15 := by omega
      let y := longCycleSuccessor x
      have successor : y.val = x.val+1 := by
        change (if x.val+1<2*m+16 then x.val+1 else 0) = x.val+1
        exact ite_eq_left (by omega)
      have xOn : x ∈ longCycleCenter m := by
        apply longCycleCenter_contains.mpr
        omega
      have yOn : y ∈ longCycleCenter m := by
        apply longCycleCenter_contains.mpr
        omega
      have xPos := longCycleCenter_position xOn
      have yPos := longCycleCenter_position yOn
      have step : (longCycleCenter m).idxOf x < (longCycleCenter m).idxOf y ∧
          (longCycleCenter m).idxOf x/8 = (longCycleCenter m).idxOf y/8 := by
        rw [xPos,yPos,successor]
        rcases region with early | ⟨middle,late⟩
        · rw [ite_eq_left (by omega : x.val<8),ite_eq_left (by omega : x.val+1<8)]
          omega
        · rw [ite_eq_right (by omega : ¬ x.val<8),ite_eq_right (by omega : ¬ x.val+1<8)]
          omega
      let center : Fin (2*m+3) := ⟨0,by omega⟩
      have rows : longRankCycleRows center = longCycleCenter m := by simp [longRankCycleRows,center]
      have before : Before (@longRankCycleRows m) center x y := by
        unfold SourceAudit.BeforeIn
        rw [rows]
        exact ⟨xOn,yOn,step.1⟩
      obtain ⟨j,_,forward⟩ := longRankCyclePiece_step_of_same_slot before (by rw [rows]; exact step.2)
      exact ⟨j,forward⟩


private theorem longRankCycleConstraintGraph_step {m k : ℕ} (x : Fin (2*m+16)) :
    Edge (riverDetourConstraintGraph (longRankCyclePieces m) k) x (longCycleSuccessor x) :=
  riverDetourConstraintGraph_edge.mpr (Or.inl (longRankCyclePiece_successor_step x))

private theorem longRankCycleConstraintGraph_ascending {m k : ℕ} {x y : Fin (2*m+16)} (ordered : x ≤ y) :
    Reach (riverDetourConstraintGraph (longRankCyclePieces m) k) x y := by
  let G := riverDetourConstraintGraph (longRankCyclePieces m) k
  have along (j : ℕ) (lower : x.val ≤ j) : ∀ upper : j < 2*m+16, Reach G x ⟨j,upper⟩ := by
    induction j, lower using Nat.le_induction with
    | base =>
      intro upper
      exact .refl
    | succ t lower ih =>
      intro bound
      have tBound : t < 2*m+16 := by omega
      have step := longRankCycleConstraintGraph_step (k := k) (⟨t,tBound⟩ : Fin (2*m+16))
      have next : longCycleSuccessor (⟨t,tBound⟩ : Fin (2*m+16)) = ⟨t+1,bound⟩ := by
        apply Fin.ext
        change (if t+1<2*m+16 then t+1 else 0) = t+1
        exact ite_eq_left bound
      rw [next] at step
      exact (ih tBound).tail step
  exact along y.val ordered y.isLt

/-- The two blocks of the central row meet the same strongly connected
component, at every cutoff. -/
theorem longRankCyclePieces_component_test_fails (m k : ℕ) :
    ¬ (∀ ⦃i j : LongRankCyclePiece m⦄ ⦃x y : Fin (2*m+16)⦄, i ≠ j → i.fst = j.fst →
      x ∈ longRankCyclePieces m i → y ∈ longRankCyclePieces m j →
      ¬ SameComponent (riverDetourConstraintGraph (longRankCyclePieces m) k) x y) := by
  let x : Fin (2*m+16) := ⟨0,by omega⟩
  let y : Fin (2*m+16) := ⟨m+8,by omega⟩
  let last : Fin (2*m+16) := ⟨2*m+15,by omega⟩
  let G := riverDetourConstraintGraph (longRankCyclePieces m) k
  have wraps : longCycleSuccessor last = x := by
    apply Fin.ext
    change (if 2*m+15+1<2*m+16 then 2*m+15+1 else 0) = 0
    exact ite_eq_right (by omega)
  have around : Edge G last x := wraps ▸ longRankCycleConstraintGraph_step last
  have forward : Reach G x y := longRankCycleConstraintGraph_ascending (by change 0 ≤ m+8; omega)
  have backward : Reach G y x :=
    (longRankCycleConstraintGraph_ascending (by change m+8 ≤ 2*m+15; omega)).tail around
  let center : Fin (2*m+3) := ⟨0,by omega⟩
  have row : longRankCycleRows center = longCycleCenter m := by simp [longRankCycleRows,center]
  have count : (longRankCycleRows center).toFinset.card = 16 := by
    rw [List.toFinset_card_of_nodup (longRankCycleRows_simple center),row]
    simp [longCycleCenter]
  let left : LongRankCyclePiece m := ⟨center,⟨0,Nat.succ_pos _⟩⟩
  let right : LongRankCyclePiece m := ⟨center,⟨1,by simp [blockCount,count]⟩⟩
  have xOn : x ∈ longCycleCenter m := longCycleCenter_contains.mpr (Or.inl (by change (0 : ℕ) < 8; decide))
  have yOn : y ∈ longCycleCenter m := longCycleCenter_contains.mpr (Or.inr ⟨le_rfl,by change m+8<m+16; omega⟩)
  have onLeft : x ∈ longRankCyclePieces m left := by
    apply mem_localPathBlock.mpr
    refine ⟨row.symm ▸ xOn,?_⟩
    change (longRankCycleRows center).idxOf x/8 = 0
    rw [row,longCycleCenter_position xOn]
    simp [x]
  have onRight : y ∈ longRankCyclePieces m right := by
    apply mem_localPathBlock.mpr
    refine ⟨row.symm ▸ yOn,?_⟩
    change (longRankCycleRows center).idxOf y/8 = 1
    rw [row,longCycleCenter_position yOn]
    change (if m+8<8 then m+8 else m+8-m)/8 = 1
    rw [ite_eq_right (by omega : ¬ m+8<8)]
    omega
  have different : left ≠ right := by
    intro same
    have equal := congrArg (fun i : LongRankCyclePiece m => i.snd.val) same
    change (0:ℕ) = 1 at equal
    omega
  intro apart
  exact apart different rfl onLeft onRight ⟨forward,backward⟩

/-- At every finite cutoff a sufficiently long member of the family has
admissible original-width path pieces with a failed component test. -/
theorem longRankCycle_original_path_width_limit {m k : ℕ} (large : 27 ≤ m) (cutoff : k ≤ m+1) :
    let width := 4*(∑ i : Fin (2*m+3), (longRankCycleRows i).length)/(2*m+3)
    let pieces := splitListPaths (@longRankCycleRows m) width
    BridgeFree (Before (@longRankCycleRows m)) k ∧ (∀ j, BridgeFree (Before pieces) j) ∧
      ¬ (∀ ⦃i j x y⦄, i ≠ j → i.fst = j.fst → x ∈ pieces i → y ∈ pieces j →
        ¬ SameComponent (riverDetourConstraintGraph pieces k) x y) := by
  dsimp only
  rw [longRankCycleRows_frozen_width large]
  exact ⟨longRankCycleRows_full_free (by omega) cutoff,longRankCyclePieces_full_free m,
    longRankCyclePieces_component_test_fails m k⟩

end OnlineReachabilityPreservers
