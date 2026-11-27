import OnlineReachabilityPreservers.CyclicIntersections
import OnlineReachabilityPreservers.ExtremalCopyBounds
import OnlineReachabilityPreservers.RainbowListSearch

/-! A finite comparison of full and half bridge extrema.

Each indexed row contributes at most one incidence in addition to its
nonnegative excess `length - 1`. To rule out mass twelve with five rows,
search among the simple rows of length at least two for excess seven.
The search excludes repeated directed comparisons and full 3-bridges.
-/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset

private abbrev Vertex := Fin 4
private abbrev Row := List Vertex

private def vertexLabels : List Vertex := List.finRange 4

private def rowWords : ℕ → List Row
  | 0 => [[]]
  | k+1 => vertexLabels.flatMap fun x => (rowWords k).map (x :: ·)

private def candidateRows : List Row :=
  (rowWords 4 ++ rowWords 3 ++ rowWords 2).filter fun row => decide row.Nodup

private def rowBefore (row : Row) (x y : Vertex) : Bool :=
  decide (x ∈ row ∧ y ∈ row ∧ row.idxOf x < row.idxOf y)

private def avoidsParallel (chosen : List Row) (row : Row) : Bool :=
  vertexLabels.all fun x => vertexLabels.all fun y =>
    !rowBefore row x y || chosen.all fun prior => !rowBefore prior x y

private def firstOwner (rows : List Row) (x y : Vertex) : Option (Fin rows.length) :=
  (List.finRange rows.length).find? fun i => rowBefore rows[i] x y

private def avoidsThree (rows : List Row) : Bool :=
  vertexLabels.all fun x => vertexLabels.all fun y => vertexLabels.all fun z =>
    match firstOwner rows x y, firstOwner rows y z, firstOwner rows x z with
    | some a, some b, some r => decide (a = b ∨ r = a ∨ r = b)
    | _, _, _ => true

private def score (rows : List Row) : ℕ := (rows.map fun row => row.length-1).sum

private def searchForLargeFullThree : List Row → List Row → Bool
  | [], chosen => decide (7 ≤ score chosen) && avoidsThree chosen
  | row :: rest, chosen =>
    if 7 ≤ score chosen then avoidsThree chosen
    else searchForLargeFullThree rest chosen ||
      (decide (chosen.length < 5) && avoidsParallel chosen row &&
        searchForLargeFullThree rest (chosen ++ [row]))

private def listFamily (rows : List Row) (i : Fin rows.length) : Row := rows[i]

private theorem rowWords_complete (row : Row) : row ∈ rowWords row.length := by
  induction row with
  | nil => simp [rowWords]
  | cons x tail ih =>
    change x::tail ∈ rowWords (tail.length+1)
    rw [rowWords, List.mem_flatMap]
    exact ⟨x,List.mem_finRange _,List.mem_map_of_mem ih⟩

private theorem candidateRows_complete {row : Row} (simple : row.Nodup) (long : 2 ≤ row.length) :
    row ∈ candidateRows := by
  have upper : row.length ≤ 4 := by
    rw [← List.toFinset_card_of_nodup simple]
    simpa only [Fintype.card_fin] using card_le_univ row.toFinset
  have size : row.length = 4 ∨ row.length = 3 ∨ row.length = 2 := by omega
  refine List.mem_filter.mpr ⟨?_,decide_eq_true simple⟩
  simp only [List.mem_append]
  have present := rowWords_complete row
  rcases size with four | three | two
  · exact Or.inl (Or.inl (four ▸ present))
  · exact Or.inl (Or.inr (three ▸ present))
  · exact Or.inr (two ▸ present)

set_option maxRecDepth 8192 in
private theorem candidateRows_unique : candidateRows.Nodup := by
  decide +kernel

private theorem listFamily_append_left_free (front tail : List Row) {cutoff : ℕ}
    (free : BridgeFree (BeforeIn (listFamily (front ++ tail))) cutoff) :
    BridgeFree (BeforeIn (listFamily front)) cutoff := by
  let room : front.length ≤ (front ++ tail).length := by simp
  let embed := Fin.castLE room
  have identifies (i : Fin front.length) : listFamily (front ++ tail) (embed i) = listFamily front i :=
    List.getElem_append_left i.isLt
  intro k bound
  refine ⟨fun b => (free bound).false (b.mapPaths embed (Fin.castLE_injective room) ?_)⟩
  intro i x y step
  unfold BeforeIn at step ⊢
  rw [identifies]
  exact step

private theorem avoidsThree_of_fullFree (rows : List Row)
    (free : BridgeFree (BeforeIn (listFamily rows)) 3) : avoidsThree rows = true := by
  unfold avoidsThree
  apply List.all_eq_true.mpr
  intro x _
  apply List.all_eq_true.mpr
  intro y _
  apply List.all_eq_true.mpr
  intro z _
  have comparison {i : Fin rows.length} {x y} (owns : firstOwner rows x y = some i) :
      BeforeIn (listFamily rows) i x y := by
    unfold firstOwner at owns
    have accepted : rowBefore rows[i] x y = true :=
      List.find?_some (p := fun j : Fin rows.length => rowBefore rows[j] x y) (a := i) owns
    unfold rowBefore at accepted
    unfold BeforeIn listFamily
    exact of_decide_eq_true accepted
  cases first : firstOwner rows x y <;> cases last : firstOwner rows y z <;>
    cases river : firstOwner rows x z <;> simp only
  rename_i a b r
  apply decide_eq_true
  by_contra! distinct
  exact (free (by decide : 3 ≤ 3)).false
    (threeListBridge distinct.1 distinct.2.1 distinct.2.2
      (comparison first) (comparison last) (comparison river))

private theorem avoidsParallel_of_fullFree (chosen : List Row) (row : Row)
    (free : BridgeFree (BeforeIn (listFamily (chosen ++ [row]))) 3) : avoidsParallel chosen row = true := by
  unfold avoidsParallel
  apply List.all_eq_true.mpr
  intro x _
  apply List.all_eq_true.mpr
  intro y _
  by_cases onLast : rowBefore row x y = true
  · simp only [onLast, Bool.not_true, Bool.false_or]
    apply List.all_eq_true.mpr
    intro prior on
    by_contra! parallel
    have onEarlier : rowBefore prior x y = true := by simpa using parallel
    obtain ⟨index,bound,value⟩ := List.mem_iff_getElem.mp on
    let a : Fin (chosen ++ [row]).length := ⟨index,by simp; omega⟩
    let b : Fin (chosen ++ [row]).length := ⟨chosen.length,by simp⟩
    have other : a ≠ b := fun equal => by
      have rank := congrArg Fin.val equal
      change index = chosen.length at rank
      omega
    have rowA : listFamily (chosen ++ [row]) a = prior := by
      exact (List.getElem_append_left bound).trans value
    have rowB : listFamily (chosen ++ [row]) b = row := by
      change (chosen ++ [row])[chosen.length] = row
      simp [List.getElem_append_right le_rfl]
    have stepA : BeforeIn (listFamily (chosen ++ [row])) a x y := by
      unfold BeforeIn
      rw [rowA]
      exact of_decide_eq_true onEarlier
    have stepB : BeforeIn (listFamily (chosen ++ [row])) b x y := by
      unfold BeforeIn
      rw [rowB]
      exact of_decide_eq_true onLast
    exact no_parallel_list_steps free.halfFree (by decide) other stepA stepB
  · have no : rowBefore row x y = false := by simpa using onLast
    simp [no]

private theorem searchForLargeFullThree_complete {pool selected : List Row} (sub : selected.Sublist pool)
    (chosen : List Row) (free : BridgeFree (BeforeIn (listFamily (chosen ++ selected))) 3)
    (room : (chosen ++ selected).length ≤ 5) (large : 7 ≤ score (chosen ++ selected)) :
    searchForLargeFullThree pool chosen = true := by
  induction sub generalizing chosen with
  | slnil =>
    have full := listFamily_append_left_free chosen [] free
    simp only [List.append_nil] at large
    simp [searchForLargeFullThree, large, avoidsThree_of_fullFree _ full]
  | cons row sub previous =>
    by_cases enough : 7 ≤ score chosen
    · exact (ite_eq_left enough).trans (avoidsThree_of_fullFree _ (listFamily_append_left_free _ _ free))
    · rw [searchForLargeFullThree, ite_eq_right enough, previous chosen free room large]
      rfl
  | @cons_cons selectedTail poolTail row sub previous =>
    by_cases enough : 7 ≤ score chosen
    · exact (ite_eq_left enough).trans (avoidsThree_of_fullFree _ (listFamily_append_left_free _ _ free))
    · have count : chosen.length < 5 := by
        simp only [List.length_append, List.length_cons] at room
        omega
      have shift : chosen ++ (row :: selectedTail) = (chosen ++ [row]) ++ selectedTail := by simp
      rw [shift] at free room large
      have usable := avoidsParallel_of_fullFree chosen row (listFamily_append_left_free _ _ free)
      have find := previous (chosen ++ [row]) free room large
      simp [searchForLargeFullThree, enough, count, usable, find]

private theorem searchEmpty_of_first_branches (pool : List Row)
    (branches : ∀ i : Fin pool.length, searchForLargeFullThree (pool.drop (i.val+1)) [pool[i]] = false) :
    searchForLargeFullThree pool [] = false := by
  induction pool with
  | nil => rfl
  | cons head tail previous =>
    have useHead : searchForLargeFullThree tail [head] = false := by
      simpa using branches 0
    have without : searchForLargeFullThree tail [] = false := by
      apply previous
      intro i
      simpa [Fin.val_succ] using branches i.succ
    simp [searchForLargeFullThree, score, without, useHead]

private theorem candidateRows_count : candidateRows.length = 60 := by decide +kernel

-- Check each possible first selection independently in the kernel.
set_option maxRecDepth 32768 in
set_option maxHeartbeats 30000000 in
private theorem rejectEachFirstRow (i : Fin 60) :
    searchForLargeFullThree (candidateRows.drop (i.val+1))
      [candidateRows[i.val]'(by rw [candidateRows_count]; exact i.isLt)] = false := by
  fin_cases i <;> decide +kernel

private theorem searchForLargeFullThree_checked : searchForLargeFullThree candidateRows [] = false :=
  searchEmpty_of_first_branches _ (fun i => rejectEachFirstRow (Fin.cast candidateRows_count i))

private theorem full_mass_le_eleven_of_checked_library (pool : List Row)
    (libraryComplete : ∀ row, row.Nodup → 2 ≤ row.length → row ∈ pool)
    (librarySimple : pool.Nodup) (certificate : searchForLargeFullThree pool [] = false)
    (rows : Fin 5 → List (Fin 4)) (simple : ∀ i, (rows i).Nodup)
    (free : BridgeFree (BeforeIn rows) 3) : (∑ i, (rows i).length) ≤ 11 := by
  classical
  by_contra! tooLarge
  let long : Finset (Fin 5) := univ.filter fun i => 2 ≤ (rows i).length
  let selected := long.image rows
  let chosen := pool.filter fun row => decide (row ∈ selected)
  have onLibrary : ∀ row ∈ selected, row ∈ pool := by
    intro row present
    obtain ⟨i,on,rfl⟩ := mem_image.mp present
    exact libraryComplete _ (simple i) (mem_filter.mp on).2
  have chosenSet : chosen.toFinset = selected := by
    ext row
    simp only [chosen, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun inside => ⟨onLibrary row inside, inside⟩⟩
  have selectedSimple : chosen.Nodup := librarySimple.filter _
  have oneLabel : Set.InjOn rows (long : Set (Fin 5)) := by
    intro i on j _ equal
    by_contra different
    have enough : 2 ≤ (rows i).length := (mem_filter.mp on).2
    have first : 0 < (rows i).length := by omega
    have last : 1 < (rows i).length := by omega
    let x := (rows i)[0]'first
    let y := (rows i)[1]'last
    have step : BeforeIn rows i x y := by
      refine ⟨List.getElem_mem first,List.getElem_mem last,?_⟩
      rw [(simple i).idxOf_getElem, (simple i).idxOf_getElem]
      decide
    have parallel : BeforeIn rows j x y := by
      unfold BeforeIn at step ⊢
      rwa [← equal]
    exact no_parallel_list_steps free.halfFree (by decide) different step parallel
  have each (i : Fin chosen.length) : ∃ j ∈ long, rows j = listFamily chosen i := by
    apply mem_image.mp
    change listFamily chosen i ∈ selected
    rw [← chosenSet]
    exact List.mem_toFinset.mpr (List.getElem_mem i.isLt)
  choose original present identifies using each
  have embedded : Function.Injective original := by
    intro i j same
    have left : listFamily chosen i = listFamily chosen j :=
      (identifies i).symm.trans (same.symm ▸ identifies j)
    exact Fin.ext (selectedSimple.getElem_inj.mp left)
  have inherited : BridgeFree (BeforeIn (listFamily chosen)) 3 := by
    intro k bound
    refine ⟨fun b => (free bound).false (b.mapPaths original embedded ?_)⟩
    intro i x y step
    unfold BeforeIn
    rwa [identifies]
  have count : chosen.length ≤ 5 := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective original embedded
  have exactScore : score chosen = ∑ i ∈ long, ((rows i).length - 1) := by
    rw [score, ← List.sum_toFinset _ selectedSimple, chosenSet]
    exact Finset.sum_image oneLabel
  have onlyLong : (∑ i, ((rows i).length - 1)) = ∑ i ∈ long, ((rows i).length - 1) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro i _
    by_cases longEnough : 2 ≤ (rows i).length
    · simp only [ite_eq_left longEnough]
    · simp only [ite_eq_right longEnough]
      omega
  have upper : (∑ i, (rows i).length) ≤ ∑ i, ((rows i).length - 1 + 1) :=
    sum_le_sum fun i _ => by omega
  rw [sum_add_distrib, onlyLong, ← exactScore] at upper
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at upper
  have found := searchForLargeFullThree_complete (selected := chosen) List.filter_sublist [] inherited
    count (show 7 ≤ score chosen by omega)
  rw [certificate] at found
  contradiction

/-- With at most four vertices and five paths, full exclusion through
three gives at most eleven incidences. -/
theorem four_vertices_five_paths_full_mass_le_eleven {n p cutoff : ℕ}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : BridgeFree (BeforeIn rows) cutoff) (enough : 3 ≤ cutoff)
    (vertices : n ≤ 4) (paths : p ≤ 5) : (∑ i, (rows i).length) ≤ 11 := by
  obtain ⟨padded, paddedSimple, paddedFree, sameMass⟩ :=
    exists_disjoint_copies_with_budgets (half := false) (t := 1) rows simple free
      (by simpa using vertices) (by simpa using paths)
  have bound := full_mass_le_eleven_of_checked_library candidateRows (fun _ => candidateRows_complete)
    candidateRows_unique searchForLargeFullThree_checked padded paddedSimple
    (fun _ size => paddedFree (size.trans enough))
  simpa [sameMass] using bound

local instance fourVertexDecidableBefore {I : Type*} (rows : I → List (Fin 4))
    (i : I) (x y : Fin 4) : Decidable (BeforeIn rows i x y) := by
  unfold BeforeIn
  infer_instance

/-- An attaining family for the full extremum, with distinct nonempty rows. -/
def fourFiveFullWitness : Fin 5 → List (Fin 4) := ![[0,1],[0,2],[1,0],[2,3],[3,2,0]]

set_option maxRecDepth 4096 in
private theorem fourFiveFullWitness_search :
    ∀ (fuel river : Fin 5) (x y : Fin 4), BeforeIn fourFiveFullWitness river x y →
      rainbowSearch fourFiveFullWitness fuel.val ((List.finRange 5).filter (fun i => decide (i ≠ river))) x y = false := by
  decide +kernel

/-- This attaining family also excludes full bridges at every size. -/
theorem fourFiveFullWitness_spec :
    (∀ i, (fourFiveFullWitness i).Nodup) ∧ Function.Injective fourFiveFullWitness ∧
      (∀ i, fourFiveFullWitness i ≠ []) ∧ (∀ k, BridgeFree (BeforeIn fourFiveFullWitness) k) ∧
      (∑ i, (fourFiveFullWitness i).length) = 11 := by
  have distinct : ∀ i j, fourFiveFullWitness i = fourFiveFullWitness j → i = j := by decide
  exact ⟨by decide, fun {_ _} => distinct _ _, by decide,
    fun _ d _ => isEmpty_bridge_of_rainbowSearch fourFiveFullWitness fourFiveFullWitness_search d, by decide⟩

/-- A simple half-bridge-free family in the displayed arrival order. -/
def fourFiveHalfWitness : Fin 5 → List (Fin 4) := ![[0,1],[0,2],[0,3],[1,2,3],[3,2,1]]

private theorem fourFiveHalfWitness_steps : ∀ i x y, BeforeIn fourFiveHalfWitness i x y →
    y ≠ 0 ∧ (i.val < 3 ↔ x = 0) := by decide +kernel

private theorem fourFiveHalfWitness_parallel : ∀ i j x y, BeforeIn fourFiveHalfWitness i x y →
    BeforeIn fourFiveHalfWitness j x y → i = j := by decide +kernel

/-- In this arrival order the half exclusion holds at every cutoff. -/
theorem fourFiveHalfWitness_halfFree (cutoff : ℕ) : HalfBridgeFree (BeforeIn fourFiveHalfWitness) cutoff := by
  intro d _ bridge earlier
  by_cases single : d = 0
  · subst d
    exact bridge.river_ne_arc 0 (fourFiveHalfWitness_parallel _ _ _ _ bridge.riverStep (bridge.arcStep 0))
  by_cases shortRiver : bridge.river.val < 3
  · let last := Fin.last d
    let prior : Fin (d+1) := ⟨d-1, by omega⟩
    have shortLast : (bridge.arc last).val < 3 := lt_trans earlier shortRiver
    have startsZero : bridge.vertex last.castSucc = 0 :=
      (fourFiveHalfWitness_steps _ _ _ (bridge.arcStep last)).2.mp shortLast
    have joins : prior.succ = last.castSucc := Fin.ext (by
      simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last, last, prior]
      omega)
    exact (fourFiveHalfWitness_steps _ _ _ (bridge.arcStep prior)).1 (joins.symm ▸ startsZero)
  · let first : Fin (d+1) := 0
    let second : Fin (d+1) := ⟨1,by omega⟩
    have notZero : bridge.vertex 0 ≠ 0 :=
      fun zero => shortRiver ((fourFiveHalfWitness_steps _ _ _ bridge.riverStep).2.mpr zero)
    have longFirst : 3 ≤ (bridge.arc first).val := le_of_not_gt
      (fun short => notZero ((fourFiveHalfWitness_steps _ _ _ (bridge.arcStep first)).2.mp short))
    have same : second.castSucc = first.succ := Fin.ext rfl
    have longSecond : 3 ≤ (bridge.arc second).val := le_of_not_gt (fun short =>
      (fourFiveHalfWitness_steps _ _ _ (bridge.arcStep first)).1
        (same ▸ (fourFiveHalfWitness_steps _ _ _ (bridge.arcStep second)).2.mp short))
    have differentA : bridge.river.val ≠ (bridge.arc first).val := fun equal => bridge.river_ne_arc first (Fin.ext equal)
    have differentB : bridge.river.val ≠ (bridge.arc second).val := fun equal => bridge.river_ne_arc second (Fin.ext equal)
    have differentC : (bridge.arc first).val ≠ (bridge.arc second).val := by
      intro equal
      have equalPos := congrArg Fin.val (bridge.distinctArcs (Fin.ext equal))
      change 0 = 1 at equalPos
      omega
    have upperRiver := bridge.river.isLt
    have upperFirst := (bridge.arc first).isLt
    have upperSecond := (bridge.arc second).isLt
    omega

/-- The half-bridge-free family has twelve incidences and five distinct nonempty rows. -/
theorem fourFiveHalfWitness_spec :
    (∀ i, (fourFiveHalfWitness i).Nodup) ∧ Function.Injective fourFiveHalfWitness ∧
      (∀ i, fourFiveHalfWitness i ≠ []) ∧ (∀ k, HalfBridgeFree (BeforeIn fourFiveHalfWitness) k) ∧
      (∑ i, (fourFiveHalfWitness i).length) = 12 := by
  have distinct : ∀ i j, fourFiveHalfWitness i = fourFiveHalfWitness j → i = j := by decide
  exact ⟨by decide, fun {_ _} => distinct _ _, by decide, fourFiveHalfWitness_halfFree, by decide⟩

end OnlineReachabilityPreservers.SourceAudit
