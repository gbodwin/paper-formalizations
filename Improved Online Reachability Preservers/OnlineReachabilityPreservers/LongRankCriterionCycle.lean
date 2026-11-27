import OnlineReachabilityPreservers.RiverDetourVertices

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

private theorem longCycle_reach_ascending {m : ℕ} {W : Type*} {G : Arcs W}
    (embed : Fin (2*m+16) → W) (step : ∀ v, Edge G (embed v) (embed (longCycleSuccessor v)))
    {x y : Fin (2*m+16)} (ordered : x ≤ y) : Reach G (embed x) (embed y) := by
  have along (j : ℕ) (lower : x.val ≤ j) :
      ∀ upper : j < 2*m+16, Reach G (embed x) (embed ⟨j,upper⟩) := by
    induction j, lower using Nat.le_induction with
    | base =>
      intro upper
      exact .refl
    | succ t lower ih =>
      intro bound
      have tBound : t < 2*m+16 := by omega
      have edge := step ⟨t,tBound⟩
      have next : longCycleSuccessor (⟨t,tBound⟩ : Fin (2*m+16)) = ⟨t+1,bound⟩ := by
        apply Fin.ext
        change (if t+1<2*m+16 then t+1 else 0) = t+1
        exact ite_eq_left bound
      rw [next] at edge
      exact (ih tBound).tail edge
  exact along y.val ordered y.isLt

private theorem longRankCycleConstraintGraph_ascending {m k : ℕ} {x y : Fin (2*m+16)} (ordered : x ≤ y) :
    Reach (riverDetourConstraintGraph (longRankCyclePieces m) k) x y :=
  longCycle_reach_ascending id (longRankCycleConstraintGraph_step (k := k)) ordered

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


/-- A vertex can occur in the center row, in at most one external row
going out of it, and in at most one external row coming into it. -/
theorem longRankCycleRows_degree_le_three {m : ℕ} (x : Fin (2*m+16)) :
    (occurrences (fun i => (longRankCycleRows i).toFinset) x).card ≤ 3 := by
  let root : Fin (2*m+3) := ⟨0,by omega⟩
  let outward := (univ : Finset (Fin (2*m+3))).filter fun i => longCycleExternalTail m i = x
  let inward := (univ : Finset (Fin (2*m+3))).filter fun i => longCycleSuccessor (longCycleExternalTail m i) = x
  have outCount : outward.card ≤ 1 := card_le_one_iff.mpr fun ha hb =>
    longCycleExternalTail_injective m ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
  have inCount : inward.card ≤ 1 := card_le_one_iff.mpr fun ha hb =>
    longCycleExternalTail_injective m (longCycleSuccessor_injective m
      ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm))
  have inside : occurrences (fun i => (longRankCycleRows i).toFinset) x ⊆ ({root} ∪ outward) ∪ inward := by
    intro i on
    by_cases zero : i.val = 0
    · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (mem_singleton.mpr (Fin.ext zero)))))
    · have member := List.mem_toFinset.mp ((mem_occurrences (marks := fun i => (longRankCycleRows i).toFinset)).mp on)
      simp only [longRankCycleRows,zero,ite_false,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with tail | head
      · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr (mem_filter.mpr ⟨mem_univ _,tail.symm⟩))))
      · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨mem_univ _,head.symm⟩))
  calc
    _ ≤ (({root} ∪ outward) ∪ inward).card := card_le_card inside
    _ ≤ ({root} ∪ outward).card+inward.card := card_union_le _ _
    _ ≤ ({root} : Finset (Fin (2*m+3))).card+outward.card+inward.card :=
      Nat.add_le_add_right (card_union_le _ _) _
    _ ≤ _ := by rw [card_singleton]; omega

private def longCycleZeroCopy {m width : ℕ} (v : Fin (2*m+16)) :
    ListVertexBlockIndex (@longRankCycleRows m) width := ⟨v,⟨0,Nat.succ_pos _⟩⟩

private theorem longCycle_zero_copies {m width : ℕ} (wide : 3 < width) (i : Fin (2*m+3)) :
    splitListVertices longRankCycleRows width i = (longRankCycleRows i).map longCycleZeroCopy := by
  let rows := @longRankCycleRows m
  let marks (j : Fin (2*m+3)) := (rows j).toFinset
  let lift (u : {u // u ∈ rows i}) := vertexCopy marks width i ⟨u.val,List.mem_toFinset.mpr u.property⟩
  let copy := @longCycleZeroCopy m width
  change (rows i).attach.map lift = (rows i).map copy
  calc
    _ = (rows i).attach.map (fun u => copy u.val) := by
      apply List.map_congr_left
      intro u _
      refine vertexBlock_eq_of_same_label (u := lift u) (v := copy u.val) rfl ?_
      change (predecessors (occurrences marks u.val) i).card/width = 0
      exact Nat.div_eq_of_lt ((card_filter_le _ _).trans_lt ((longRankCycleRows_degree_le_three u.val).trans_lt wide))
    _ = ((rows i).attach.map Subtype.val).map copy := by simp only [List.map_map,Function.comp_def]
    _ = _ := by rw [List.attach_map_subtype_val]

private theorem longCycle_copy_projection_injective {m width : ℕ} (wide : 3 < width) :
    Function.Injective (fun x : ListVertexBlockIndex (@longRankCycleRows m) width => x.fst) := by
  have blockZero (x : ListVertexBlockIndex (@longRankCycleRows m) width) : x.snd.val = 0 := by
    have bound := x.snd.isLt
    change x.snd.val < (occurrences (fun i => (longRankCycleRows i).toFinset) x.fst).card/width+1 at bound
    have zero := Nat.div_eq_of_lt ((longRankCycleRows_degree_le_three x.fst).trans_lt wide)
    omega
  intro a b same
  exact vertexBlock_eq_of_same_label same ((blockZero a).trans (blockZero b).symm)

/-- The original factor-four degree width is seven for the long cycle
family once the path width is eight. -/
theorem longRankCycleRows_frozen_degree_width {m : ℕ} (large : 27 ≤ m) :
    4*(∑ i : Fin (2*m+3), (longRankCycleRows i).length)/(2*m+16) = 7 := by
  rw [longRankCycleRows_mass]
  have positive : 0 < 2*m+16 := by omega
  have above : 7 ≤ 4*(4*m+20)/(2*m+16) := (Nat.le_div_iff_mul_le positive).mpr (by omega)
  have below : 4*(4*m+20)/(2*m+16) < 8 := (Nat.div_lt_iff_lt_mul positive).mpr (by omega)
  omega

private theorem width_block_map {V W : Type*} [LinearOrder V] [LinearOrder W]
    (row : List V) (simple : row.Nodup) (f : V → W) (injective : Function.Injective f) (width block : ℕ) :
    localPathBlock (row.map f) width block = (localPathBlock row width block).map f := by
  unfold localPathBlock
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro x on
  have pos := List.idxOf_lt_length_of_mem on
  have inside : row.idxOf x < (row.map f).length := by simpa only [List.length_map] using pos
  have same := (simple.map injective).idxOf_getElem (i := row.idxOf x) inside
  rw [List.getElem_map,List.getElem_idxOf pos] at same
  change decide ((row.map f).idxOf (f x)/width=block) = decide (row.idxOf x/width=block)
  rw [same]


private theorem longRankCycleCopies_properties {m width k : ℕ} (wide : 3 < width) :
    let copies := splitListVertices (@longRankCycleRows m) width
    let pieces := splitListPaths copies 8
    (∀ j, BridgeFree (Before pieces) j) ∧
      (¬ ∀ ⦃i j x y⦄, i ≠ j → i.fst = j.fst → x ∈ pieces i → y ∈ pieces j →
        ¬ SameComponent (riverDetourConstraintGraph pieces k) x y) ∧
      riverDetourVertexGraph pieces k = ∅ := by
  let rows := @longRankCycleRows m
  let copies := splitListVertices rows width
  let pieces := splitListPaths copies 8
  let W := ListVertexBlockIndex rows width
  let J := ListBlockIndex copies 8
  let embed := @longCycleZeroCopy m width
  let project (x : W) := x.fst
  have embedInjective : Function.Injective embed := fun _ _ same => congrArg Sigma.fst same
  have projects : Function.Injective project := longCycle_copy_projection_injective wide
  have count (i : Fin (2*m+3)) : blockCount (copies i).toFinset 8 = blockCount (rows i).toFinset 8 := by
    rw [blockCount,blockCount,List.toFinset_card_of_nodup (splitListVertices_simple rows width i (longRankCycleRows_simple i)),
      List.toFinset_card_of_nodup (longRankCycleRows_simple i),splitListVertices_length]
  let pieceIndex : LongRankCyclePiece m ≃ J := {
    toFun := fun i => ⟨i.fst,i.snd.cast (count i.fst).symm⟩
    invFun := fun i => ⟨i.fst,i.snd.cast (count i.fst)⟩
    left_inv := by intro i; cases i; rfl
    right_inv := by intro i; cases i; rfl }
  have shape (i : LongRankCyclePiece m) : pieces (pieceIndex i) = (longRankCyclePieces m i).map embed := by
    change localPathBlock (copies i.fst) 8 i.snd.val = (localPathBlock (rows i.fst) 8 i.snd.val).map embed
    have labels : copies i.fst = (rows i.fst).map embed := longCycle_zero_copies wide i.fst
    calc
      _ = localPathBlock ((rows i.fst).map embed) 8 i.snd.val :=
        congrArg (fun row => localPathBlock row 8 i.snd.val) labels
      _ = _ := width_block_map _ (longRankCycleRows_simple i.fst) embed embedInjective _ _
  have pieceProject (i : J) : (pieces i).map project = longRankCyclePieces m (pieceIndex.symm i) := by
    conv_lhs => rw [← pieceIndex.apply_symm_apply i,shape,List.map_map]
    change (longRankCyclePieces m (pieceIndex.symm i)).map id = _
    rw [List.map_id]
  have forget {i : J} {a b : W} (edge : Before pieces i a b) :
      Before (longRankCyclePieces m) (pieceIndex.symm i) (project a) (project b) := by
    have simple : ((pieces i).map project).Nodup :=
      (pieceProject i).symm ▸ List.filter_sublist.nodup (longRankCycleRows_simple (pieceIndex.symm i).fst)
    simpa only [SourceAudit.BeforeIn,pieceProject] using listBefore_map project simple edge
  have built : ∀ j, BridgeFree (Before pieces) j := by
    intro j d small
    refine ⟨fun b => ?_⟩
    let old : Bridge (Before (longRankCyclePieces m)) d := {
      vertex := project ∘ b.vertex
      arc := pieceIndex.symm ∘ b.arc
      river := pieceIndex.symm b.river
      distinctVertices := projects.comp b.distinctVertices
      distinctArcs := pieceIndex.symm.injective.comp b.distinctArcs
      river_ne_arc := fun l equal => b.river_ne_arc l (pieceIndex.symm.injective equal)
      riverStep := forget b.riverStep
      arcStep := fun l => forget (b.arcStep l) }
    exact (longRankCyclePieces_full_free m j small).false old
  have empty : riverDetourVertexGraph pieces k = ∅ :=
    riverDetourVertexGraph_eq_empty_of_unique_source_piece
      (fun {_ _ _ _ _} left right => pieceIndex.symm.injective
        (longRankCyclePiece_unique_source (forget left) (forget right))) k
  refine ⟨built,?_,empty⟩
  let G := riverDetourConstraintGraph pieces k
  have step (x : Fin (2*m+16)) : Edge G (embed x) (embed (longCycleSuccessor x)) := by
    obtain ⟨i,edge⟩ := longRankCyclePiece_successor_step x
    have simple : ((longRankCyclePieces m i).map embed).Nodup :=
      (List.filter_sublist.nodup (longRankCycleRows_simple i.fst)).map embedInjective
    apply riverDetourConstraintGraph_edge.mpr
    exact Or.inl ⟨pieceIndex i,by
      simpa only [SourceAudit.BeforeIn,shape] using listBefore_map embed simple edge⟩
  let x : Fin (2*m+16) := ⟨0,by omega⟩
  let y : Fin (2*m+16) := ⟨m+8,by omega⟩
  let last : Fin (2*m+16) := ⟨2*m+15,by omega⟩
  have wraps : longCycleSuccessor last = x := by
    apply Fin.ext
    change (if 2*m+15+1<2*m+16 then 2*m+15+1 else 0) = 0
    exact ite_eq_right (by omega)
  have forward : Reach G (embed x) (embed y) :=
    longCycle_reach_ascending embed step (by change 0 ≤ m+8; omega)
  have backward : Reach G (embed y) (embed x) :=
    (longCycle_reach_ascending embed step (by change m+8 ≤ 2*m+15; omega)).tail (wraps ▸ step last)
  let center : Fin (2*m+3) := ⟨0,by omega⟩
  have row : rows center = longCycleCenter m := by simp [rows,longRankCycleRows,center]
  have centerLength : (rows center).length = 16 := by rw [row]; simp [longCycleCenter]
  have centerCount : (rows center).toFinset.card = 16 :=
    (List.toFinset_card_of_nodup (longRankCycleRows_simple center)).trans centerLength
  let left : LongRankCyclePiece m := ⟨center,⟨0,Nat.succ_pos _⟩⟩
  have rightBound : 1 < blockCount (rows center).toFinset 8 := by simp [blockCount,centerCount]
  let right : LongRankCyclePiece m := ⟨center,⟨1,rightBound⟩⟩
  have xOn : x ∈ longCycleCenter m := longCycleCenter_contains.mpr (Or.inl (by change (0 : ℕ) < 8; decide))
  have yOn : y ∈ longCycleCenter m := longCycleCenter_contains.mpr (Or.inr ⟨le_rfl,by change m+8<m+16; omega⟩)
  have onLeft : x ∈ longRankCyclePieces m left := by
    change x ∈ localPathBlock (rows center) 8 0
    apply mem_localPathBlock.mpr
    refine ⟨row.symm ▸ xOn,?_⟩
    change (rows center).idxOf x/8 = 0
    rw [row,longCycleCenter_position xOn]
    simp [x]
  have onRight : y ∈ longRankCyclePieces m right := by
    change y ∈ localPathBlock (rows center) 8 1
    apply mem_localPathBlock.mpr
    refine ⟨row.symm ▸ yOn,?_⟩
    change (rows center).idxOf y/8 = 1
    rw [row,longCycleCenter_position yOn]
    change (if m+8<8 then m+8 else m+8-m)/8 = 1
    rw [ite_eq_right (by omega : ¬ m+8<8)]
    omega
  have different : pieceIndex left ≠ pieceIndex right := by
    intro same
    have slots := congrArg (fun i : J => i.snd.val) same
    change (0:ℕ) = 1 at slots
    omega
  have first : embed x ∈ pieces (pieceIndex left) := by rw [shape]; exact List.mem_map.mpr ⟨x,onLeft,rfl⟩
  have second : embed y ∈ pieces (pieceIndex right) := by rw [shape]; exact List.mem_map.mpr ⟨y,onRight,rfl⟩
  intro apart
  exact apart different rfl first second ⟨forward,backward⟩

/-- Both widths prescribed by the original averages give admissible
blocks of the long cycle family, and their component test fails. -/
theorem longRankCycle_original_widths_limit {m k : ℕ} (large : 27 ≤ m) (cutoff : k ≤ m+1) :
    let M := ∑ i : Fin (2*m+3), (longRankCycleRows i).length
    let copies := splitListVertices (@longRankCycleRows m) (4*M/(2*m+16))
    let pieces := splitListPaths copies (4*M/(2*m+3))
    BridgeFree (Before (@longRankCycleRows m)) k ∧ BridgeFree (Before copies) k ∧
      (∀ j, BridgeFree (Before pieces) j) ∧
      ¬ (∀ ⦃i j x y⦄, i ≠ j → i.fst = j.fst → x ∈ pieces i → y ∈ pieces j →
        ¬ SameComponent (riverDetourConstraintGraph pieces k) x y) := by
  dsimp only
  rw [longRankCycleRows_frozen_degree_width large,longRankCycleRows_frozen_width large]
  have inputFree := longRankCycleRows_full_free (by omega : 0 < m) cutoff
  have properties := longRankCycleCopies_properties (m := m) (k := k) (by decide : 3 < 7)
  refine ⟨inputFree,?_,properties.1,properties.2.1⟩
  intro d small
  refine ⟨fun b => ?_⟩
  let copies := splitListVertices (@longRankCycleRows m) 7
  let project (x : ListVertexBlockIndex (@longRankCycleRows m) 7) := x.fst
  have same (i) : (copies i).map project = longRankCycleRows i := splitListVertices_project _ _ _
  have step (i x y) (before : Before copies i x y) : Before (@longRankCycleRows m) i (project x) (project y) := by
    have simple : ((copies i).map project).Nodup := (same i).symm ▸ longRankCycleRows_simple i
    simpa only [SourceAudit.BeforeIn,same] using listBefore_map project simple before
  exact (inputFree small).false (b.mapVertices project (longCycle_copy_projection_injective (by decide : 3 < 7)) step)

/-- The original-width construction gives a frozen witness for this
family using the already admissible width blocks. -/
theorem longRankCycle_frozen_at_original_widths {m k : ℕ} (large : 27 ≤ m) :
    let M := ∑ i : Fin (2*m+3), (longRankCycleRows i).length
    ∃ n' ≤ 2*m+16, ∃ p' ≤ 2*m+3, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps (2*m+16) (2*m+3) M clean := by
  let M := ∑ i : Fin (2*m+3), (longRankCycleRows i).length
  have mass : M = 4*m+20 := longRankCycleRows_mass m
  have allowed : localOrderAdmissible false k
      (listRegularizedPaths (@longRankCycleRows m) (4*M/(2*m+16)) (4*M/(2*m+3))) :=
    (longRankCycle_original_widths_limit (k := 0) large (by omega)).2.2.1 k
  exact regularization_list_frozen_after_width_blocks_of_mass (half := false) (retention := 16)
    (@longRankCycleRows m) longRankCycleRows_simple allowed
    (by omega) (by omega) (by omega) (by omega) le_rfl (by norm_num)

/-- At the original widths the long cycle has no bounded detour outside
its own river piece. The finer graph has no edges at any cutoff. -/
theorem longRankCycle_original_widths_detour_vertex_graph_empty {m k : ℕ} (large : 27 ≤ m) :
    let M := ∑ i : Fin (2*m+3), (longRankCycleRows i).length
    let pieces := listRegularizedPaths (@longRankCycleRows m) (4*M/(2*m+16)) (4*M/(2*m+3))
    riverDetourVertexGraph pieces k = ∅ := by
  dsimp only
  rw [longRankCycleRows_frozen_degree_width large,longRankCycleRows_frozen_width large]
  exact (longRankCycleCopies_properties (m := m) (k := k) (by decide : 3 < 7)).2.2

/-- Distinct pieces of the same parent in the long cycle meet disjoint
components of the finer graph, despite failing the earlier rank test. -/
theorem longRankCycle_original_widths_detour_vertex_separated {m k : ℕ} (large : 27 ≤ m) :
    let M := ∑ i : Fin (2*m+3), (longRankCycleRows i).length
    let pieces := listRegularizedPaths (@longRankCycleRows m) (4*M/(2*m+16)) (4*M/(2*m+3))
    ∀ ⦃i j x y⦄, i ≠ j → i.fst = j.fst → x ∈ pieces i → y ∈ pieces j →
      ¬ SameComponent (riverDetourVertexGraph pieces k) x y := by
  let M := ∑ i : Fin (2*m+3), (longRankCycleRows i).length
  let V := ListVertexBlockIndex (@longRankCycleRows m) (4*M/(2*m+16))
  have same_of_empty {x y : V} (route : Reach (∅ : Arcs V) x y) : x = y := by
    induction route with
    | refl => rfl
    | tail _ edge _ => exact (Finset.notMem_empty _ edge).elim
  dsimp only
  intro i j x y different parents first second components
  have empty := longRankCycle_original_widths_detour_vertex_graph_empty (k := k) large
  have route := components.1
  rw [empty] at route
  have equal := same_of_empty route
  exact splitListPaths_disjoint different parents first (equal.symm ▸ second)

end OnlineReachabilityPreservers
