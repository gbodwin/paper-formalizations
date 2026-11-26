import OnlineReachabilityPreservers.SteinerBinaryFlowAugmentWork
import OnlineReachabilityPreservers.SteinerBinaryPathWork

/-! Run bounded unit augmentations directly over a complete encoded flow table. -/

namespace OnlineReachabilityPreservers

open Finset

private abbrev EncodedFlowRow := BinaryCapacityFlowRow (List Bool × List Bool)

/-- Scan the residual table, find a shortest encoded path, and update the
signed entries, stopping when no path exists or the supply is exhausted. -/
def binaryUnitAugmentationsWithWork (source target : List Bool) (depth : ℕ) :
    ℕ → List EncodedFlowRow → (List EncodedFlowRow × ℕ) × ℕ
  | 0, rows => ((rows,0),2)
  | fuel+1, rows =>
    let residual := binaryResidualRowsWithWork rows
    let route := binaryShortestPathWithWork residual.1 source target depth
    match route.1 with
    | none => ((rows,0),residual.2+route.2+5)
    | some path =>
      let updated := augmentBinaryFlowRowsWithWork path rows
      let tail := binaryUnitAugmentationsWithWork source target depth fuel updated.1
      ((tail.1.1,tail.1.2+1),residual.2+route.2+updated.2+tail.2+9)

/-- Per-step bounds use the entire table size as an upper bound on the
residual arc count and the vertex count as an upper bound on path length. -/
def binaryUnitAugmentationsWorkBudget (n rows labels capacityWidth flowWidth fuel : ℕ) : ℕ :=
  2+fuel*(binaryResidualRowsWorkBudget rows capacityWidth flowWidth+
    binaryShortestPathWorkBudget n rows labels n+augmentBinaryFlowRowsWorkBudget rows n labels flowWidth+9)

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- A list of rows describes the reference table when every word decodes
to the indicated reference entry and fits its declared width. -/
def BinaryFlowRowsDescribe (capacity flow : ArcFlow V) (capacityWidth flowWidth : ℕ)
    (rows : List (BinaryCapacityFlowRow (V × V))) : Prop :=
  ∀ row ∈ rows, (binaryWordValue row.capacity : ℤ) = capacity row.arc ∧ row.flow.value = flow row.arc ∧
    row.capacity.length ≤ capacityWidth ∧ row.flow.magnitude.length ≤ flowWidth

omit [LinearOrder V] [Fintype V] in
private theorem BinaryFlowRowsDescribe.increase_flow_width {capacity flow : ArcFlow V} {c f g : ℕ}
    {rows : List (BinaryCapacityFlowRow (V × V))} (described : BinaryFlowRowsDescribe capacity flow c f rows)
    (room : f ≤ g) : BinaryFlowRowsDescribe capacity flow c g rows := by
  intro row member
  obtain ⟨capValue,flowValue,capFits,flowFits⟩ := described row member
  exact ⟨capValue,flowValue,capFits,flowFits.trans room⟩

private def rowCapacities {A : Type*} (rows : List (BinaryCapacityFlowRow A)) : List (A × List Bool) :=
  rows.map fun row => (row.arc,row.capacity)

private theorem complete_of_rowCapacities_eq {A : Type*} {before after : List (BinaryCapacityFlowRow A)}
    (unchanged : rowCapacities after = rowCapacities before) (complete : ∀ a, a ∈ before.map BinaryCapacityFlowRow.arc) :
    ∀ a, a ∈ after.map BinaryCapacityFlowRow.arc := by
  have h := congrArg (List.map Prod.fst) unchanged
  have sameKeys : after.map BinaryCapacityFlowRow.arc = before.map BinaryCapacityFlowRow.arc := by
    simpa only [rowCapacities,List.map_map,Function.comp_def] using h
  rw [sameKeys]
  exact complete

omit [LinearOrder V] [Fintype V] in
private theorem updated_rows_describe {capacity flow next : ArcFlow V} {capWidth width : ℕ}
    {rows updated : List (BinaryCapacityFlowRow (V × V))}
    (encoded : BinaryFlowRowsDescribe capacity flow capWidth width rows)
    (unchanged : rowCapacities updated = rowCapacities rows)
    (decoded : ∀ row ∈ updated, row.flow.value = next row.arc ∧ row.flow.magnitude.length ≤ width+1) :
    BinaryFlowRowsDescribe capacity next capWidth (width+1) updated := by
  intro row member
  have fromOld : (row.arc,row.capacity) ∈ rowCapacities rows := by
    rw [← unchanged]
    exact List.mem_map_of_mem member
  obtain ⟨old,inside,same⟩ := List.mem_map.mp fromOld
  obtain ⟨capValue,_,capFits,_⟩ := encoded old inside
  obtain ⟨flowValue,flowFits⟩ := decoded row member
  have keys := congrArg Prod.fst same
  have words := congrArg Prod.snd same
  change old.arc = row.arc at keys
  change old.capacity = row.capacity at words
  rw [keys,words] at capValue
  rw [words] at capFits
  exact ⟨capValue,flowValue,capFits,flowFits⟩

/-- Starting from a valid represented flow, the bounded run returns a
valid flow with the exact number of additional units sent. If the supply
is unspent, the returned flow has no residual source-to-target route. -/
theorem binaryUnitAugmentationsWithWork_refines {capacity flow : ArcFlow V} {source target : V} {sent : ℕ}
    (code : V → List Bool) (injective : Function.Injective code) (w : ℕ) (bounded : ∀ v, (code v).length ≤ w)
    (fuel capWidth flowWidth maxWidth : ℕ) (fits : flowWidth+fuel ≤ maxWidth)
    (rows : List (BinaryCapacityFlowRow (V × V))) (complete : ∀ e, e ∈ rows.map BinaryCapacityFlowRow.arc)
    (encoded : BinaryFlowRowsDescribe capacity flow capWidth flowWidth rows)
    (valid : ValidArcFlow capacity source target sent flow) :
    let out := binaryUnitAugmentationsWithWork (code source) (code target) (Fintype.card V) fuel
      (binaryEncodeCapacityFlowRows code rows)
    ∃ terminal : ArcFlow V, ∃ updated : List (BinaryCapacityFlowRow (V × V)),
      out.1.1 = binaryEncodeCapacityFlowRows code updated ∧
      updated.map (fun row => (row.arc,row.capacity)) = rows.map (fun row => (row.arc,row.capacity)) ∧
      BinaryFlowRowsDescribe capacity terminal capWidth maxWidth updated ∧
      ValidArcFlow capacity source target (sent+out.1.2) terminal ∧ out.1.2 ≤ fuel ∧
      (out.1.2 < fuel → ¬ Reach (residualArcs capacity terminal) source target) ∧
      out.2 ≤ binaryUnitAugmentationsWorkBudget (Fintype.card V) rows.length w capWidth maxWidth fuel := by
  let n := Fintype.card V
  induction fuel generalizing flow sent rows flowWidth with
  | zero =>
    refine ⟨flow,rows,rfl,rfl,encoded.increase_flow_width (by omega),?_,le_rfl,?_ ,?_⟩
    · simpa [binaryUnitAugmentationsWithWork] using valid
    · change 0 < 0 → _
      omega
    · simp [binaryUnitAugmentationsWithWork,binaryUnitAugmentationsWorkBudget]
  | succ fuel ih =>
    let residual := (rows.map BinaryCapacityFlowRow.arc).filter fun e => decide (flow e < capacity e)
    let bits := binaryEncodeCapacityFlowRows code rows
    let residualRows := binaryResidualRowsWithWork bits
    let route := binaryShortestPathWithWork residualRows.1 (code source) (code target) n
    have sameSet : residual.toFinset = residualArcs capacity flow := by
      ext e
      simp [residual,residualArcs,complete e]
    have residualSize : residual.length ≤ rows.length := by
      simpa [residual] using List.length_filter_le (fun e : V × V => decide (flow e < capacity e))
        (rows.map BinaryCapacityFlowRow.arc)
    obtain ⟨residualValue,residualCost⟩ := binaryResidualRowsWithWork_spec code capacity flow rows capWidth flowWidth encoded
    change residualRows.1 = binaryEncodeArcs code residual at residualValue
    change residualRows.2 ≤ _ at residualCost
    have resCost : residualRows.2 ≤ binaryResidualRowsWorkBudget rows.length capWidth maxWidth := by
      apply residualCost.trans
      have narrow : flowWidth ≤ maxWidth := by omega
      unfold binaryResidualRowsWorkBudget
      gcongr
    obtain ⟨routeValue,routeCost⟩ := binaryShortestPathWithWork_spec code injective w bounded residual source target n
    rw [← residualValue] at routeValue routeCost
    have pathCost := routeCost.trans (binaryShortestPathWorkBudget_mono_arcs n w n residualSize)
    let unit := binaryResidualRowsWorkBudget rows.length capWidth maxWidth+
      binaryShortestPathWorkBudget n rows.length w n+augmentBinaryFlowRowsWorkBudget rows.length n w maxWidth+9
    change (route.1 = none ∧ source ∉ reachIn residual.toFinset target n ∨
      ∃ path, route.1 = some (binaryEncodeArcs code path) ∧ SimpleWalk residual.toFinset source target path ∧
        path.length ≤ n ∧ ∀ earlier < path.length, source ∉ reachIn residual.toFinset target earlier) at routeValue
    change route.2 ≤ binaryShortestPathWorkBudget n rows.length w n at pathCost
    rcases routeValue with ⟨missing,absent⟩ | ⟨path,chosen,walk,pathSize,_⟩
    · have stalled : ¬ Reach (residualArcs capacity flow) source target := by
        rw [← sameSet]
        exact fun reach => absent (mem_reaches.mpr reach)
      have output : binaryUnitAugmentationsWithWork (code source) (code target) n (fuel+1) bits =
          ((bits,0),residualRows.2+route.2+5) := by
        rw [binaryUnitAugmentationsWithWork]
        change (match route.1 with
          | none => ((bits,0),residualRows.2+route.2+5)
          | some path =>
            let updated := augmentBinaryFlowRowsWithWork path bits
            let tail := binaryUnitAugmentationsWithWork (code source) (code target) n fuel updated.1
            ((tail.1.1,tail.1.2+1),residualRows.2+route.2+updated.2+tail.2+9)) = _
        rw [missing]
      change ∃ terminal updated, _
      simp only [show Fintype.card V = n from rfl,show binaryEncodeCapacityFlowRows code rows = bits from rfl,output]
      refine ⟨flow,rows,rfl,rfl,encoded.increase_flow_width (by omega),by simpa using valid,by omega,fun _ => stalled,?_⟩
      change residualRows.2+route.2+5 ≤ 2+(fuel+1)*unit
      rw [Nat.succ_mul fuel]
      unfold unit
      omega
    · let next := augmentArcFlow flow path.toFinset
      let changed := augmentBinaryFlowRowsWithWork (binaryEncodeArcs code path) bits
      obtain ⟨updated,updatedBits,keptKeys,updatedFlow,changedCost⟩ :=
        augmentBinaryFlowRowsWithWork_refines code injective w bounded flow rows path flowWidth
          (fun row member => ⟨(encoded row member).2.1,(encoded row member).2.2.2⟩)
      change changed.1 = binaryEncodeCapacityFlowRows code updated at updatedBits
      have changedBound : changed.2 ≤ augmentBinaryFlowRowsWorkBudget rows.length n w maxWidth := by
        apply changedCost.trans
        have room : flowWidth ≤ maxWidth := by omega
        unfold augmentBinaryFlowRowsWorkBudget
        gcongr
      have nextEncoded : BinaryFlowRowsDescribe capacity next capWidth (flowWidth+1) updated :=
        updated_rows_describe encoded keptKeys updatedFlow
      have nextValid : ValidArcFlow capacity source target (sent+1) next :=
        valid.augment (sameSet ▸ walk)
      have nextComplete := complete_of_rowCapacities_eq keptKeys complete
      have length : updated.length = rows.length := by simpa only [List.length_map] using congrArg List.length keptKeys
      obtain ⟨terminal,after,afterBits,afterKeys,afterDescribe,afterValid,within,stalled,tailCost⟩ :=
        ih (flow := next) (sent := sent+1) (flowWidth := flowWidth+1) (by omega) updated nextComplete nextEncoded nextValid
      let tail := binaryUnitAugmentationsWithWork (code source) (code target) n fuel changed.1
      rw [← updatedBits] at afterBits afterValid within stalled tailCost
      change tail.1.1 = _ at afterBits
      change ValidArcFlow capacity source target (sent+1+tail.1.2) terminal at afterValid
      change tail.1.2 ≤ fuel at within
      change tail.1.2 < fuel → ¬ Reach _ _ _ at stalled
      change tail.2 ≤ binaryUnitAugmentationsWorkBudget n updated.length w capWidth maxWidth fuel at tailCost
      rw [length] at tailCost
      have output : binaryUnitAugmentationsWithWork (code source) (code target) n (fuel+1) bits =
          ((tail.1.1,tail.1.2+1),residualRows.2+route.2+changed.2+tail.2+9) := by
        rw [binaryUnitAugmentationsWithWork]
        change (match route.1 with
          | none => ((bits,0),residualRows.2+route.2+5)
          | some path =>
            let updated := augmentBinaryFlowRowsWithWork path bits
            let tail := binaryUnitAugmentationsWithWork (code source) (code target) n fuel updated.1
            ((tail.1.1,tail.1.2+1),residualRows.2+route.2+updated.2+tail.2+9)) = _
        rw [chosen]
      simp only [show Fintype.card V = n from rfl,show binaryEncodeCapacityFlowRows code rows = bits from rfl,output]
      refine ⟨terminal,after,afterBits,afterKeys.trans keptKeys,afterDescribe,?_,by omega,fun short => stalled (by omega),?_⟩
      · rw [show sent+(tail.1.2+1) = sent+1+tail.1.2 by omega]
        exact afterValid
      · change tail.2 ≤ 2+fuel*unit at tailCost
        change residualRows.2+route.2+changed.2+tail.2+9 ≤ 2+(fuel+1)*unit
        rw [Nat.succ_mul fuel]
        omega

/-- Build the initial signed table by giving every supplied capacity a
zero flow. The row keys and capacity words are reused. -/
def zeroBinaryFlowRowsWithWork {A : Type*} :
    List (A × List Bool) → List (BinaryCapacityFlowRow A) × ℕ
  | [] => ([],2)
  | row::rest =>
    let tail := zeroBinaryFlowRowsWithWork rest
    (⟨row.1,row.2,⟨false,[]⟩⟩::tail.1,tail.2+6)

private def zeroFlowRow {A : Type*} (row : A × List Bool) : BinaryCapacityFlowRow A :=
  ⟨row.1,row.2,⟨false,[]⟩⟩

private theorem zeroBinaryFlowRowsWithWork_spec {A : Type*} (rows : List (A × List Bool)) :
    zeroBinaryFlowRowsWithWork rows = (rows.map zeroFlowRow,2+6*rows.length) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [zeroBinaryFlowRowsWithWork,ih,zeroFlowRow,List.map_cons,List.length_cons,Nat.mul_succ,Nat.add_assoc]

def binaryEncodeCapacityRows (code : V → List Bool) (rows : List ((V × V) × List Bool)) :
    List ((List Bool × List Bool) × List Bool) :=
  rows.map fun row => ((code row.1.1,code row.1.2),row.2)

/-- Start from zero, run the bounded augmentations, and return the original
arcs leaving the residual source side when the flow falls short. -/
def binaryFindLowCapacityOutgoingCutWithWork (arcs : List (List Bool × List Bool))
    (rows : List ((List Bool × List Bool) × List Bool)) (source target : List Bool) (depth supply : ℕ) :
    Option (List (List Bool × List Bool)) × ℕ :=
  let start := zeroBinaryFlowRowsWithWork rows
  let solved := binaryUnitAugmentationsWithWork source target depth supply start.1
  if solved.1.2 = supply then (none,start.2+solved.2+5)
  else
    let cut := binaryFlowCutWithWork arcs solved.1.1 source depth
    (some cut.1,start.2+solved.2+cut.2+7)

/-- Bound the finite augmentation supply and the maximum magnitude width
by the same numeric supply, since every entry starts at zero. -/
def binaryLowCapacityOutgoingCutWorkBudget (n arcs rows labels capacityWidth supply : ℕ) : ℕ :=
  2+6*rows+binaryUnitAugmentationsWorkBudget n rows labels capacityWidth supply supply+
    binaryFlowCutWorkBudget n arcs rows labels capacityWidth supply n+7

/-- From a supplied complete unsigned capacity table, the encoded
separator agrees with the reference separator on failure and returns the
ordered original arcs of its exact cut on success. -/
theorem binaryFindLowCapacityOutgoingCutWithWork_refines {capacity : ArcFlow V}
    (code : V → List Bool) (injective : Function.Injective code) (w : ℕ) (bounded : ∀ v, (code v).length ≤ w)
    (arcs : List (V × V)) (rows : List ((V × V) × List Bool)) (source target : V) (capWidth supply : ℕ)
    (complete : ∀ e, e ∈ rows.map Prod.fst)
    (decoded : ∀ row ∈ rows, (binaryWordValue row.2 : ℤ) = capacity row.1 ∧ row.2.length ≤ capWidth) :
    let out := binaryFindLowCapacityOutgoingCutWithWork (binaryEncodeArcs code arcs) (binaryEncodeCapacityRows code rows)
      (code source) (code target) (Fintype.card V) supply
    (match findLowCapacityCut capacity source target supply with
      | none => out.1 = none
      | some side =>
        ∃ cut : List (V × V), out.1 = some (binaryEncodeArcs code cut) ∧
          cut.toFinset = outgoingCut arcs.toFinset side ∧ (arcs.Nodup → cut.Nodup)) ∧
      out.2 ≤ binaryLowCapacityOutgoingCutWorkBudget (Fintype.card V) arcs.length rows.length w capWidth supply := by
  let n := Fintype.card V
  let referenceRows := rows.map zeroFlowRow
  let bits := binaryEncodeCapacityRows code rows
  let start := zeroBinaryFlowRowsWithWork bits
  let solved := binaryUnitAugmentationsWithWork (code source) (code target) n supply start.1
  have initialRows : start.1 = binaryEncodeCapacityFlowRows code referenceRows := by
    change (zeroBinaryFlowRowsWithWork bits).1 = _
    rw [zeroBinaryFlowRowsWithWork_spec]
    simp [bits,binaryEncodeCapacityRows,binaryEncodeCapacityFlowRows,referenceRows,zeroFlowRow,List.map_map,Function.comp_def]
  have initCost : start.2 = 2+6*rows.length := by
    change (zeroBinaryFlowRowsWithWork bits).2 = _
    rw [zeroBinaryFlowRowsWithWork_spec]
    simp [bits,binaryEncodeCapacityRows]
  have completeInitial : ∀ e, e ∈ referenceRows.map BinaryCapacityFlowRow.arc := by
    simpa only [referenceRows,List.map_map,Function.comp_def,zeroFlowRow] using complete
  have nonnegative (e : V × V) : 0 ≤ capacity e := by
    obtain ⟨row,present,rfl⟩ := List.mem_map.mp (complete e)
    rw [← (decoded row present).1]
    exact Int.natCast_nonneg _
  have initial : BinaryFlowRowsDescribe capacity (fun _ => 0) capWidth 0 referenceRows := by
    intro row present
    obtain ⟨old,member,rfl⟩ := List.mem_map.mp present
    obtain ⟨value,width⟩ := decoded old member
    exact ⟨value,rfl,width,le_rfl⟩
  have valid : ValidArcFlow capacity source target 0 (fun _ => 0) :=
    ⟨by simp,nonnegative,by simp [divergence]⟩
  obtain ⟨terminal,updated,encodedEnd,sameKeys,describeEnd,validEnd,within,stalled,solveCost⟩ :=
    binaryUnitAugmentationsWithWork_refines code injective w bounded supply capWidth 0 supply (by omega)
      referenceRows completeInitial initial valid
  rw [← initialRows] at encodedEnd validEnd within stalled solveCost
  change solved.1.1 = _ at encodedEnd
  change ValidArcFlow capacity source target (0+solved.1.2) terminal at validEnd
  change solved.1.2 ≤ supply at within
  change solved.1.2 < supply → ¬ Reach (residualArcs capacity terminal) source target at stalled
  change solved.2 ≤ binaryUnitAugmentationsWorkBudget n referenceRows.length w capWidth supply supply at solveCost
  rw [show referenceRows.length = rows.length from List.length_map ..] at solveCost
  rw [Nat.zero_add] at validEnd
  have agrees := findLowCapacityCut_eq_terminal nonnegative validEnd within stalled
  have updatedComplete := complete_of_rowCapacities_eq sameKeys completeInitial
  have size : updated.length = rows.length := by
    simpa only [referenceRows,List.length_map] using congrArg List.length sameKeys
  let cut := binaryFlowCutWithWork (binaryEncodeArcs code arcs) solved.1.1 (code source) n
  let out := if solved.1.2 = supply then ((none : Option (List (List Bool × List Bool))),start.2+solved.2+5)
    else (some cut.1,start.2+solved.2+cut.2+7)
  change (match findLowCapacityCut capacity source target supply with
      | none => out.1 = none
      | some side =>
        ∃ cut : List (V × V), out.1 = some (binaryEncodeArcs code cut) ∧
          cut.toFinset = outgoingCut arcs.toFinset side ∧ (arcs.Nodup → cut.Nodup)) ∧
    out.2 ≤ binaryLowCapacityOutgoingCutWorkBudget n arcs.length rows.length w capWidth supply
  unfold out
  rw [agrees]
  by_cases enough : solved.1.2 = supply
  · simp only [enough,ite_true]
    refine ⟨True.intro,?_⟩
    rw [initCost]
    unfold binaryLowCapacityOutgoingCutWorkBudget
    omega
  · simp only [enough,ite_false]
    obtain ⟨outgoing,cutValue,cutSet,simple,cutCost⟩ :=
      binaryFlowCutWithWork_refines code injective w bounded arcs updated source capWidth supply updatedComplete describeEnd
    rw [← encodedEnd] at cutValue cutCost
    change cut.1 = _ at cutValue
    change cut.2 ≤ binaryFlowCutWorkBudget n arcs.length updated.length w capWidth supply n at cutCost
    rw [size] at cutCost
    refine ⟨⟨outgoing,congrArg some cutValue,cutSet,simple⟩,?_⟩
    rw [initCost]
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left solveCost _) cutCost) _

/-- Enlarge the graph, residual table, widths, and augmentation allowance. -/
theorem binaryLowCapacityOutgoingCutWorkBudget_le {n n' arcs arcs' rows rows' labels labels' cap cap' supply supply' : ℕ}
    (vertices : n ≤ n') (edges : arcs ≤ arcs') (table : rows ≤ rows') (width : labels ≤ labels')
    (capacity : cap ≤ cap') (augmentations : supply ≤ supply') :
    binaryLowCapacityOutgoingCutWorkBudget n arcs rows labels cap supply ≤
      binaryLowCapacityOutgoingCutWorkBudget n' arcs' rows' labels' cap' supply' := by
  have route := binaryShortestPathWorkBudget_le vertices table width vertices
  unfold binaryLowCapacityOutgoingCutWorkBudget binaryUnitAugmentationsWorkBudget binaryFlowCutWorkBudget
    binaryResidualRowsWorkBudget binaryResidualCutWorkBudget augmentBinaryFlowRowsWorkBudget
  dsimp only
  gcongr

end OnlineReachabilityPreservers
