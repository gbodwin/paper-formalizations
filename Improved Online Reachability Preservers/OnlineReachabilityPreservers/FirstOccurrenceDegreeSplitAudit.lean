import OnlineReachabilityPreservers.FirstOccurrenceHalfFive
import OnlineReachabilityPreservers.VertexSplitAudit

/-! The first-occurrence sublist condition alone permits a half-five degree collision. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset

/-- The initial singleton rows place vertex three in its own first-occurrence
group and shift its two active incidences together by one degree block. -/
def firstOccurrenceSplitRows (i : Fin 43) : List (Fin 12) :=
  if i.val = 16 then [3,2]
  else if i.val = 17 then [0,2]
  else if i.val = 32 then [1,2]
  else if i.val = 33 then [2,3]
  else if i.val = 34 then [0,1]
  else if i.val < 16 then [3]
  else if i.val < 32 then [2]
  else [⟨i.val-31,by have := i.isLt; omega⟩]

/-- The first row of each vertex is distinct in this example. -/
def firstOccurrenceSplitFirst : Fin 12 → Fin 43 :=
  ![17,32,16,0,35,36,37,38,39,40,41,42]

private def activeRows : Fin 5 → Fin 43 := ![16,17,32,33,34]

private def projectVertex (v : Fin 12) : Fin 4 := ⟨v.val % 4, Nat.mod_lt _ (by decide)⟩

local instance decidableListComparison {I V : Type*} [DecidableEq V]
    (rows : I → List V) (i : I) (x y : V) : Decidable (BeforeIn rows i x y) :=
  inferInstanceAs (Decidable (x ∈ rows i ∧ y ∈ rows i ∧ (rows i).idxOf x < (rows i).idxOf y))

private theorem onlyActive {i : Fin 43} {x y : Fin 12}
    (step : BeforeIn firstOccurrenceSplitRows i x y) : ∃ a, activeRows a = i := by
  have belongs : i.val = 16 ∨ i.val = 17 ∨ i.val = 32 ∨ i.val = 33 ∨ i.val = 34 := by
    by_contra! outside
    obtain ⟨a,b,c,d,e⟩ := outside
    have lengthOne : (firstOccurrenceSplitRows i).length = 1 := by
      simp only [firstOccurrenceSplitRows, ite_eq_right a, ite_eq_right b, ite_eq_right c,
        ite_eq_right d, ite_eq_right e]
      split <;> (try split) <;> rfl
    have after := List.idxOf_lt_length_of_mem step.2.1
    have ordered := step.2.2
    omega
  rcases belongs with eq16 | eq17 | eq32 | eq33 | eq34
  · exact ⟨0,Fin.ext eq16.symm⟩
  · exact ⟨1,Fin.ext eq17.symm⟩
  · exact ⟨2,Fin.ext eq32.symm⟩
  · exact ⟨3,Fin.ext eq33.symm⟩
  · exact ⟨4,Fin.ext eq34.symm⟩

set_option maxRecDepth 8192 in
private theorem projectActive : ∀ a x y, BeforeIn firstOccurrenceSplitRows (activeRows a) x y →
    x.val < 4 ∧ y.val < 4 ∧ BeforeIn vertexSplitFiveExample a (projectVertex x) (projectVertex y) := by
  decide +kernel

private theorem respectsOrder : ∀ a r, activeRows a < activeRows r → a < r := by decide

/-- The active comparisons are an order-preserving relabelling of the
original five-row example. The added singleton rows contribute no steps. -/
theorem firstOccurrenceSplitRows_halfFree (cutoff : ℕ) : HalfBridgeFree (BeforeIn firstOccurrenceSplitRows) cutoff := by
  intro d bound bridge earlier
  choose arc arcLabel using (fun j : Fin (d+1) => onlyActive (bridge.arcStep j))
  obtain ⟨r,riverLabel⟩ := onlyActive bridge.riverStep
  have arcData (j : Fin (d+1)) := projectActive (arc j) _ _ (by rw [arcLabel j]; exact bridge.arcStep j)
  have riverData := projectActive r _ _ (by rw [riverLabel]; exact bridge.riverStep)
  have vertexSmall (j : Fin (d+2)) : (bridge.vertex j).val < 4 := by
    refine Fin.lastCases riverData.2.1 (fun i => (arcData i).1) j
  let old : Bridge (BeforeIn vertexSplitFiveExample) d :=
    ⟨projectVertex ∘ bridge.vertex,arc,r,?_,?_,?_,riverData.2.2,fun j => (arcData j).2.2⟩
  · apply vertexSplitFiveExample_half_free cutoff bound old
    apply respectsOrder
    change activeRows (arc (Fin.last d)) < activeRows r
    simpa only [arcLabel,riverLabel] using earlier
  · intro i j same
    have rank := congrArg Fin.val same
    change (bridge.vertex i).val % 4 = (bridge.vertex j).val % 4 at rank
    rw [Nat.mod_eq_of_lt (vertexSmall i), Nat.mod_eq_of_lt (vertexSmall j)] at rank
    exact bridge.distinctVertices (Fin.ext rank)
  · intro i j same
    apply bridge.distinctArcs
    rw [← arcLabel i, ← arcLabel j, same]
  · intro j same
    apply bridge.river_ne_arc j
    rw [← riverLabel, ← arcLabel j, same]

set_option maxRecDepth 8192 in
theorem firstOccurrenceSplitRows_parameters :
    (∀ i, (firstOccurrenceSplitRows i).Nodup ∧ (firstOccurrenceSplitRows i).length ≤ 2) ∧
    (∀ v : Fin 12, v ∈ firstOccurrenceSplitRows (firstOccurrenceSplitFirst v)) ∧
    (∀ i, ∀ v ∈ firstOccurrenceSplitRows i, firstOccurrenceSplitFirst v ≤ i) ∧
    Function.Injective firstOccurrenceSplitFirst ∧
    let M := ∑ i, (firstOccurrenceSplitRows i).length
    M = 48 ∧ 4*M/12 = 16 ∧ 4*M/43 = 4 := by
  have injective : ∀ x y, firstOccurrenceSplitFirst x = firstOccurrenceSplitFirst y → x = y := by decide
  exact ⟨by decide, by decide, by decide, fun {_ _} => injective _ _, by decide⟩

/-- Every row already has at most one vertex in each first-occurrence group. -/
theorem firstOccurrenceSplitRows_normalized (i b : Fin 43) :
    ((firstOccurrenceSplitRows i).toFinset.filter (fun v => firstOccurrenceSplitFirst v = b)).card ≤ 1 := by
  apply card_le_one_iff.mpr
  intro x y onX onY
  exact firstOccurrenceSplitRows_parameters.2.2.2.1
    ((mem_filter.mp onX).2.trans (mem_filter.mp onY).2.symm)

theorem firstOccurrenceSplitRows_has_cross_group_opposites :
    ¬ OppositesWithinFirstOccurrenceGroups firstOccurrenceSplitRows firstOccurrenceSplitFirst := by
  intro grouped
  exact (by decide : firstOccurrenceSplitFirst 3 ≠ firstOccurrenceSplitFirst 2)
    (grouped (i := 16) (j := 33) (x := 3) (y := 2) (by decide) (by decide) (by decide))

set_option synthInstance.maxSize 1500 in
/-- The degree split at the original factor-four width creates a half-five bridge. -/
theorem firstOccurrenceSplitRows_degree_creates_halfFive :
    ¬ HalfBridgeFree (BeforeIn (splitListVertices firstOccurrenceSplitRows 16)) 5 := by
  let vertex : Fin 5 → ListVertexBlockIndex firstOccurrenceSplitRows 16 :=
    ![⟨0,⟨0,by decide⟩⟩,⟨1,⟨0,by decide⟩⟩,⟨2,⟨1,by decide⟩⟩,
      ⟨3,⟨1,by decide⟩⟩,⟨2,⟨0,by decide⟩⟩]
  let arc : Fin 4 → Fin 43 := ![34,32,33,16]
  have distinctVertices : ∀ i j, vertex i = vertex j → i = j := by decide
  have distinctRows : ∀ i j, arc i = arc j → i = j := by decide
  have riverApart : ∀ i, (17 : Fin 43) ≠ arc i := by decide
  have river : BeforeIn (splitListVertices firstOccurrenceSplitRows 16) 17 (vertex 0) (vertex (Fin.last 4)) := by decide
  have steps : ∀ i, BeforeIn (splitListVertices firstOccurrenceSplitRows 16) (arc i) (vertex i.castSucc) (vertex i.succ) := by decide
  intro free
  exact free (k := 3) (by decide)
    ⟨vertex,arc,17,fun {_ _} => distinctVertices _ _,fun {_ _} => distinctRows _ _,riverApart,river,steps⟩
    (by change (16 : Fin 43) < 17; decide)

end OnlineReachabilityPreservers.SourceAudit
