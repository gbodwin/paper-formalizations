import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Data.List.ChainOfFn
import OnlineReachabilityPreservers.FrozenDistinctCleaning
import OnlineReachabilityPreservers.OutputAverageDistinctCleaning

/-! Short bridge projections in incidence graphs with large girth. -/

namespace OnlineReachabilityPreservers

open SimpleGraph Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

private theorem short_circuit_getVert_injective {A : Type*} {G : SimpleGraph A}
    {v : A} {w : G.Walk v v} (trail : w.IsTrail) {k : ℕ}
    (girth : (k:ℕ∞) < G.egirth) (short : w.length ≤ 2*k) :
    Set.InjOn w.getVert {i | i < w.length} := by
  have cannot {i j : ℕ} (earlier : i < j) (inside : j < w.length)
      (same : w.getVert i = w.getVert j) : False := by
    have atEnd : (w.drop i).getVert (j-i) = w.getVert i := by
      rw [Walk.drop_getVert, Nat.add_sub_of_le earlier.le]
      exact same.symm
    let a := ((w.drop i).take (j-i)).copy rfl atEnd
    let b := ((w.drop j).append (w.take i)).copy same.symm rfl
    have aLength : a.length = j-i := by
      simp only [a,Walk.length_copy,Walk.take_length,Walk.drop_length]
      exact min_eq_left (Nat.sub_le_sub_right inside.le i)
    have bLength : b.length = w.length-j+i := by
      simp only [b,Walk.length_copy,Walk.length_append,Walk.drop_length,Walk.take_length]
      rw [min_eq_left (earlier.le.trans inside.le)]
    have aTrail : a.IsTrail := by
      rw [Walk.isTrail_def]
      simp only [a,Walk.edges_copy,Walk.edges_take,Walk.edges_drop]
      exact (List.take_sublist _ _).nodup ((List.drop_sublist _ _).nodup trail.edges_nodup)
    have bTrail : b.IsTrail := by
      rw [Walk.isTrail_def]
      simp only [b,Walk.edges_copy,Walk.edges_append,Walk.edges_take,Walk.edges_drop]
      refine List.nodup_append.mpr ⟨(List.drop_sublist _ _).nodup trail.edges_nodup,
        (List.take_sublist _ _).nodup trail.edges_nodup,?_⟩
      intro x hx y hy eq
      exact List.disjoint_take_drop trail.edges_nodup earlier.le hy (eq ▸ hx)
    have aNonempty : a ≠ .nil := by
      intro nil
      simp only [nil,Walk.length_nil] at aLength
      omega
    have bNonempty : b ≠ .nil := by
      intro nil
      simp only [nil,Walk.length_nil] at bLength
      omega
    have aCycle : a.IsCircuit := ⟨aTrail,aNonempty⟩
    have bCycle : b.IsCircuit := ⟨bTrail,bNonempty⟩
    have aLong := ENat.natCast_lt_natCast.mp (girth.trans_le aCycle.egirth_le_length)
    have bLong := ENat.natCast_lt_natCast.mp (girth.trans_le bCycle.egirth_le_length)
    omega
  intro i hi j hj same
  change i < w.length at hi
  change j < w.length at hj
  rcases lt_trichotomy i j with ij | eq | ji
  · exact (cannot ij hj same).elim
  · exact eq
  · exact (cannot ji hi same.symm).elim

/-- The bipartite graph on row labels and vertex labels, with an edge for
each incidence. The directed order inside a row plays no role here. -/
def pathIncidenceGraph {I V : Type*} (paths : I → List V) : SimpleGraph (I ⊕ V) where
  Adj
    | .inl i, .inr v => v ∈ paths i
    | .inr v, .inl i => v ∈ paths i
    | _, _ => False
  symm := ⟨by intro a b h; cases a <;> cases b <;> exact h⟩
  loopless := ⟨by intro a; cases a <;> exact id⟩

section Projection

variable {I J V W : Type*} [DecidableEq V] [DecidableEq W]

private def incidenceSlots {pieces : J → List W} {d : ℕ} (b : Bridge (Before pieces) d) :
    Fin (d+2) → J := Fin.snoc b.arc b.river

private theorem incidenceSlots_injective {pieces : J → List W} {d : ℕ}
    (b : Bridge (Before pieces) d) : Function.Injective (incidenceSlots b) :=
  Fin.snoc_injective_of_injective b.distinctArcs (fun ⟨i,hi⟩ => b.river_ne_arc i hi.symm)

private theorem incidence_next_arc {d : ℕ} (a : Fin (d+1)) :
    (a.castSucc : Fin (d+2))+1 = a.succ := by
  apply Fin.ext
  simp only [Fin.val_add,Fin.val_castSucc,Fin.val_one,Fin.val_succ]
  exact Nat.mod_eq_of_lt (Nat.succ_lt_succ a.isLt)

private theorem incidence_next_river (d : ℕ) : (Fin.last (d+1):Fin (d+2))+1 = 0 := by
  apply Fin.ext
  simp

private theorem incidence_next_ne {d : ℕ} (i : Fin (d+2)) : i ≠ i+1 := by
  refine Fin.lastCases (motive := fun i : Fin (d+2) => i ≠ i+1) ?_ ?_ i
  · rw [incidence_next_river]
    intro eq
    have same := congrArg Fin.val eq
    simp at same
  · intro a
    rw [incidence_next_arc]
    intro eq
    have same := congrArg Fin.val eq
    simp at same

private theorem incidence_slot_corners {pieces : J → List W} {d : ℕ}
    (b : Bridge (Before pieces) d) (i : Fin (d+2)) :
    b.vertex i ∈ pieces (incidenceSlots b i) ∧ b.vertex (i+1) ∈ pieces (incidenceSlots b i) := by
  refine Fin.lastCases (motive := fun i => b.vertex i ∈ pieces (incidenceSlots b i) ∧
    b.vertex (i+1) ∈ pieces (incidenceSlots b i)) ?_ ?_ i
  · rw [incidenceSlots,Fin.snoc_last,incidence_next_river]
    exact ⟨b.riverStep.2.1,b.riverStep.1⟩
  · intro a
    rw [incidenceSlots,Fin.snoc_castSucc,incidence_next_arc]
    exact ⟨(b.arcStep a).1,(b.arcStep a).2.1⟩

private def incidenceCycleVertex {d : ℕ} (corners : Fin (d+2) → V) (slots : Fin (d+2) → I)
    (i : ℕ) : I ⊕ V :=
  let j : Fin (d+2) := ⟨(i/2)%(d+2),Nat.mod_lt _ (by omega)⟩
  if i%2 = 0 then .inr (corners j) else .inl (slots j)

omit [DecidableEq V] in
private theorem incidence_cycle_even {d : ℕ} (corners : Fin (d+2) → V) (slots : Fin (d+2) → I)
    (i : Fin (d+2)) : incidenceCycleVertex corners slots (2*i.val) = .inr (corners i) := by
  simp [incidenceCycleVertex,show 2*i.val/2 = i.val by omega,
    show (2*i.val)%2 = 0 by omega,Nat.mod_eq_of_lt i.isLt]

omit [DecidableEq V] in
private theorem incidence_cycle_odd {d : ℕ} (corners : Fin (d+2) → V) (slots : Fin (d+2) → I)
    (i : Fin (d+2)) : incidenceCycleVertex corners slots (2*i.val+1) = .inl (slots i) := by
  simp [incidenceCycleVertex,show (2*i.val+1)/2 = i.val by omega,
    show (2*i.val+1)%2 = 1 by omega,Nat.mod_eq_of_lt i.isLt]

omit [DecidableEq V] in
private theorem incidence_cycle_next {d : ℕ} (corners : Fin (d+2) → V) (slots : Fin (d+2) → I)
    (i : Fin (d+2)) : incidenceCycleVertex corners slots (2*i.val+2) = .inr (corners (i+1)) := by
  have index : (⟨(i.val+1)%(d+2),Nat.mod_lt _ (by omega)⟩ : Fin (d+2)) = i+1 := by
    apply Fin.ext
    simp [Fin.val_add]
  simp only [incidenceCycleVertex,show (2*i.val+2)/2 = i.val+1 by omega,
    show (2*i.val+2)%2 = 0 by omega,ite_true,index]

omit [DecidableEq V] in
private theorem incidence_cycle_closes {d : ℕ} (corners : Fin (d+2) → V) (slots : Fin (d+2) → I) :
    incidenceCycleVertex corners slots (2*(d+2)) = incidenceCycleVertex corners slots 0 := by
  simp [incidenceCycleVertex,show 2*(d+2)/2 = d+2 by omega,show (2*(d+2))%2 = 0 by omega]

omit [DecidableEq V] in
private theorem projected_bridge_incidence_injective {paths : I → List V} {pieces : J → List W} {d : ℕ}
    (b : Bridge (Before pieces) d) (parent : J → I) (project : W → V)
    (members : ∀ {i x}, x ∈ pieces i → project x ∈ paths (parent i))
    (incidences : ∀ {i j x y}, x ∈ pieces i → y ∈ pieces j → parent i = parent j →
      project x = project y → i = j ∧ x = y)
    (girth : ((d+2:ℕ):ℕ∞) < (pathIncidenceGraph paths).egirth) :
    Function.Injective (project ∘ b.vertex) ∧ Function.Injective (parent ∘ incidenceSlots b) := by
  let slots := parent ∘ incidenceSlots b
  let corners := project ∘ b.vertex
  let node := incidenceCycleVertex corners slots
  have even (i : Fin (d+2)) : node (2*i.val) = Sum.inr (corners i) := incidence_cycle_even corners slots i
  have odd (i : Fin (d+2)) : node (2*i.val+1) = Sum.inl (slots i) := incidence_cycle_odd corners slots i
  have next (i : Fin (d+2)) : node (2*i.val+2) = Sum.inr (corners (i+1)) := incidence_cycle_next corners slots i
  let support := List.ofFn (fun i : Fin (2*(d+2)+1) => node i.val)
  have nonempty : support ≠ [] := by simp [support]
  have chain : support.IsChain (pathIncidenceGraph paths).Adj := by
    refine List.isChain_ofFn.mpr ?_
    intro t ht
    change (pathIncidenceGraph paths).Adj (node t) (node (t+1))
    let i : Fin (d+2) := ⟨t/2,by omega⟩
    by_cases parity : t%2 = 0
    · have h : t = 2*i.val := by dsimp only [i]; omega
      rw [h,even,odd]
      exact members (incidence_slot_corners b i).1
    · have h : t = 2*i.val+1 := by dsimp only [i]; omega
      rw [h,odd,show 2*i.val+1+1 = 2*i.val+2 by omega,next]
      exact members (incidence_slot_corners b i).2
  have first : support.head nonempty = node 0 := List.head_ofFn nonempty
  have last : support.getLast nonempty = node 0 := by
    rw [List.getLast_ofFn]
    change node (2*(d+2)+1-1) = node 0
    rw [Nat.add_sub_cancel]
    exact incidence_cycle_closes corners slots
  let walk := (Walk.ofSupport support nonempty chain).copy first last
  have length : walk.length = 2*(d+2) := by
    simp only [walk,Walk.length_copy,Walk.length_ofSupport,support,List.length_ofFn]
    omega
  have atIndex {t : ℕ} (fit : t ≤ walk.length) : walk.getVert t = node t := by
    rw [walk.getVert_eq_support_getElem fit]
    simp only [walk,Walk.support_copy,Walk.support_ofSupport,support,List.getElem_ofFn]
  let edgeRow (t : Fin (2*(d+2))) : Fin (d+2) := ⟨t.val/2,by omega⟩
  let edgeCorner (t : Fin (2*(d+2))) : Fin (d+2) :=
    if t.val%2 = 0 then edgeRow t else edgeRow t+1
  have cornerEven (t : Fin (2*(d+2))) (parity : t.val%2 = 0) : edgeCorner t = edgeRow t := ite_eq_left parity
  have cornerOdd (t : Fin (2*(d+2))) (parity : t.val%2 ≠ 0) : edgeCorner t = edgeRow t+1 := ite_eq_right parity
  have cornerMem (t : Fin (2*(d+2))) : b.vertex (edgeCorner t) ∈ pieces (incidenceSlots b (edgeRow t)) := by
    by_cases parity : t.val%2 = 0
    · simpa only [cornerEven t parity] using (incidence_slot_corners b (edgeRow t)).1
    · simpa only [cornerOdd t parity] using (incidence_slot_corners b (edgeRow t)).2
  have edgeAt (t : Fin (2*(d+2))) : walk.edges[t.val]'(by rw [walk.length_edges,length]; exact t.isLt) =
      s(Sum.inl (slots (edgeRow t)),Sum.inr (corners (edgeCorner t))) := by
    rw [Walk.getElem_edges,atIndex (by omega),atIndex (by omega)]
    by_cases parity : t.val%2 = 0
    · have h : t.val = 2*(edgeRow t).val := by dsimp only [edgeRow]; omega
      rw [h,even,odd,cornerEven t parity,Sym2.eq_swap]
    · have h : t.val = 2*(edgeRow t).val+1 := by dsimp only [edgeRow]; omega
      rw [h,odd,show 2*(edgeRow t).val+1+1 = 2*(edgeRow t).val+2 by omega,next,cornerOdd t parity]
  have trail : walk.IsTrail := by
    rw [Walk.isTrail_def,List.nodup_iff_injective_get]
    intro s t same
    have sFit : s.val < 2*(d+2) := by rw [← length,← walk.length_edges]; exact s.isLt
    have tFit : t.val < 2*(d+2) := by rw [← length,← walk.length_edges]; exact t.isLt
    let s' : Fin (2*(d+2)) := ⟨s.val,sFit⟩
    let t' : Fin (2*(d+2)) := ⟨t.val,tFit⟩
    have equal : s(Sum.inl (slots (edgeRow s')),Sum.inr (corners (edgeCorner s'))) =
        s(Sum.inl (slots (edgeRow t')),Sum.inr (corners (edgeCorner t'))) := by
      rw [← edgeAt s',← edgeAt t']
      exact same
    rcases Sym2.eq_iff.mp equal with ⟨row,vertex⟩ | ⟨bad,_⟩
    · obtain ⟨row,vertex⟩ := incidences (cornerMem s') (cornerMem t')
        (Sum.inl.inj row) (Sum.inr.inj vertex)
      have rows := incidenceSlots_injective b row
      have cornersEq := b.distinctVertices vertex
      have divEq : s.val/2 = t.val/2 := congrArg Fin.val rows
      apply Fin.ext
      by_cases sEven : s'.val%2 = 0 <;> by_cases tEven : t'.val%2 = 0
      · change s.val%2 = 0 at sEven
        change t.val%2 = 0 at tEven
        omega
      · rw [cornerEven s' sEven,cornerOdd t' tEven,← rows] at cornersEq
        exact (incidence_next_ne _ cornersEq).elim
      · rw [cornerOdd s' sEven,cornerEven t' tEven,← rows] at cornersEq
        exact (incidence_next_ne _ cornersEq.symm).elim
      · change s.val%2 ≠ 0 at sEven
        change t.val%2 ≠ 0 at tEven
        omega
    · cases bad
  have injective := short_circuit_getVert_injective trail girth length.le
  constructor
  · intro i j same
    have iFit : 2*i.val < walk.length := by rw [length]; omega
    have jFit : 2*j.val < walk.length := by rw [length]; omega
    have equal := injective iFit jFit (by rw [atIndex iFit.le,atIndex jFit.le,even,even]; exact congrArg Sum.inr same)
    apply Fin.ext
    omega
  · intro i j same
    have iFit : 2*i.val+1 < walk.length := by rw [length]; omega
    have jFit : 2*j.val+1 < walk.length := by rw [length]; omega
    have equal := injective iFit jFit (by rw [atIndex iFit.le,atIndex jFit.le,odd,odd]; exact congrArg Sum.inl same)
    apply Fin.ext
    omega

/-- When the original incidence girth exceeds the size of the bridge,
a projection injective on incidences keeps its distinct labels. -/
def Bridge.project_of_incidence_girth {paths : I → List V} {pieces : J → List W} {d : ℕ}
    (b : Bridge (Before pieces) d) (parent : J → I) (project : W → V)
    (members : ∀ {i x}, x ∈ pieces i → project x ∈ paths (parent i))
    (incidences : ∀ {i j x y}, x ∈ pieces i → y ∈ pieces j → parent i = parent j →
      project x = project y → i = j ∧ x = y)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) (project x) (project y))
    (girth : ((d+2:ℕ):ℕ∞) < (pathIncidenceGraph paths).egirth) :
    Bridge (Before paths) d := by
  have projected := projected_bridge_incidence_injective b parent project
    (fun {_ _} => members) (fun {_ _ _ _} => incidences) girth
  refine ⟨project ∘ b.vertex,parent ∘ b.arc,parent b.river,projected.1,?_,?_,steps b.riverStep,
    fun i => steps (b.arcStep i)⟩
  · intro i j same
    have eq : (i.castSucc : Fin (d+2)) = j.castSucc := projected.2 (by
      simpa only [Function.comp_apply,incidenceSlots,Fin.snoc_castSucc] using same)
    exact Fin.castSucc_injective _ eq
  · intro i same
    have eq : (Fin.last (d+1):Fin (d+2)) = i.castSucc := projected.2 (by
      simpa only [Function.comp_apply,incidenceSlots,Fin.snoc_last,Fin.snoc_castSucc] using same)
    have positions := congrArg Fin.val eq
    simp only [Fin.val_last,Fin.val_castSucc] at positions
    have small := i.isLt
    omega

/-- Every projection that preserves comparisons and identifies no distinct
incidences preserves the bridge cutoff below the incidence girth. In half
mode the parent map respects arrival order. -/
theorem localOrderAdmissible_of_incidence_girth_projection [LinearOrder I] [LinearOrder J]
    {paths : I → List V} {pieces : J → List W} {k : ℕ} {half : Bool}
    (allowed : localOrderAdmissible half k paths) (girth : (k:ℕ∞) < (pathIncidenceGraph paths).egirth)
    (parent : J → I) (project : W → V) (ordered : Monotone parent)
    (members : ∀ {i x}, x ∈ pieces i → project x ∈ paths (parent i))
    (incidences : ∀ {i j x y}, x ∈ pieces i → y ∈ pieces j → parent i = parent j →
      project x = project y → i = j ∧ x = y)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) (project x) (project y)) :
    localOrderAdmissible half k pieces := by
  let lift {d : ℕ} (size : d+2 ≤ k) (b : Bridge (Before pieces) d) : Bridge (Before paths) d :=
    b.project_of_incidence_girth parent project (fun {_ _} => members) (fun {_ _ _ _} => incidences)
      (fun {_ _ _} => steps) ((ENat.natCast_le_natCast.mpr size).trans_lt girth)
  cases half
  · intro d fit
    exact ⟨fun b => (allowed fit).false (lift fit b)⟩
  · intro d fit b earlier
    let original := lift fit b
    have strict : original.arc (Fin.last d) < original.river :=
      lt_of_le_of_ne (ordered earlier.le) (original.river_ne_arc _).symm
    exact allowed fit original strict

end Projection

/-- Both ordinary width splits project injectively on the incidences. Thus
they preserve either bridge cutoff strictly below the incidence girth. -/
theorem listRegularizedPaths_admissible_of_incidence_girth {I V : Type*}
    [LinearOrder I] [Fintype I] [LinearOrder V] [Fintype V] {paths : I → List V} {k : ℕ} {half : Bool}
    (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (girth : (k:ℕ∞) < (pathIncidenceGraph paths).egirth) (D L : ℕ) :
    localOrderAdmissible half k (listRegularizedPaths paths D L) := by
  let copies := splitListVertices paths D
  let pieces := splitListPaths copies L
  let parent : ListBlockIndex copies L → I := Sigma.fst
  let project : ListVertexBlockIndex paths D → V := Sigma.fst
  have sub (i : ListBlockIndex copies L) : (pieces i).Sublist (copies (parent i)) :=
    List.filter_sublist
  have copiedSimple (i : I) : (copies i).Nodup := splitListVertices_simple paths D i (simple i)
  have members {i x} (on : x ∈ pieces i) : project x ∈ paths (parent i) := by
    rw [← splitListVertices_project paths D (parent i)]
    exact List.mem_map_of_mem ((sub i).subset on)
  have incidences {i j x y} (xi : x ∈ pieces i) (yj : y ∈ pieces j)
      (row : parent i = parent j) (vertex : project x = project y) : i = j ∧ x = y := by
    have yi : y ∈ copies (parent i) := row.symm ▸ (sub j).subset yj
    have distinct : ((copies (parent i)).map project).Nodup :=
      (splitListVertices_project paths D (parent i)).symm ▸ simple (parent i)
    have same := List.inj_on_of_nodup_map distinct ((sub i).subset xi) yi vertex
    refine ⟨?_,same⟩
    by_contra apart
    exact splitListPaths_disjoint apart row xi (same.symm ▸ yj)
  have steps {i x y} (step : Before pieces i x y) : Before paths (parent i) (project x) (project y) := by
    have lifted : Before (fun j : ListBlockIndex copies L => copies (parent j)) i x y :=
      listBefore_of_sublist (copiedSimple (parent i)) (sub i) step
    exact splitListVertices_step (simple (parent i)) lifted
  exact localOrderAdmissible_of_incidence_girth_projection allowed girth parent project
    (block_parent_mono (fun i => (copies i).toFinset) L) (fun {_ _} => members)
    (fun {_ _ _ _} => incidences) (fun {_ _ _} => steps)

/-- Restricting row labels and vertex labels does not decrease incidence
girth when each retained incidence is present in the input. -/
theorem pathIncidenceGraph_egirth_le_of_embedding {I J V W : Type*}
    {paths : I → List V} {pieces : J → List W} (parent : J → I) (project : W → V)
    (rowInjective : Function.Injective parent) (vertexInjective : Function.Injective project)
    (members : ∀ {i x}, x ∈ pieces i → project x ∈ paths (parent i)) :
    (pathIncidenceGraph paths).egirth ≤ (pathIncidenceGraph pieces).egirth := by
  let f : pathIncidenceGraph pieces →g pathIncidenceGraph paths :=
    ⟨Sum.map parent project,by
      intro a b h
      cases a <;> cases b
      · exact h.elim
      · exact members h
      · exact members h
      · exact h.elim⟩
  have injective : Function.Injective f := Sum.map_injective.mpr ⟨rowInjective,vertexInjective⟩
  refine SimpleGraph.le_egirth.mpr (fun a w cycle => ?_)
  simpa only [Walk.length_map] using (cycle.map injective).egirth_le_length

/-- At a cutoff smaller than the incidence girth, both original budgets,
all four starting-average caps, and at least one sixteenth of the input
mass survive regularization in either bridge mode. -/
theorem regularization_list_frozen_of_incidence_girth {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (girth : (k:ℕ∞) < (pathIncidenceGraph paths).egirth)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ localOrderAdmissible half k rows ∧
      M ≤ 16*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  let M := ∑ i, (paths i).length
  exact regularization_list_frozen_after_width_blocks_of_mass paths simple
    (listRegularizedPaths_admissible_of_incidence_girth simple allowed girth (4*M/n) (4*M/p))
    hn hp dense long le_rfl (by ring_nf; omega)

/-- The same incidence-girth criterion gives exact starting caps in the
literal convention for cutoffs at least two. -/
theorem regularization_literal_frozen_of_incidence_girth {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (girth : (k:ℕ∞) < (pathIncidenceGraph paths).egirth)
    (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ localOrderAdmissible half k rows ∧
      M ≤ 16*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  obtain ⟨v,vFit,q,qFit,rows,oneToOne,nonempty,simple,legal,keep,upper,caps⟩ :=
    regularization_list_frozen_distinct_of_indexed paths distinct (fun i => (valid i).1) (fun i => (valid i).2)
      allowed two hn hp dense (by decide)
      (regularization_list_frozen_of_incidence_girth paths (fun i => (valid i).2) allowed girth hn hp dense)
  exact ⟨v,vFit,q,qFit,rows,oneToOne,fun i => ⟨nonempty i,simple i⟩,legal,keep,upper,caps⟩

/-- Below the incidence girth, the indexed witness can instead use the
four caps relative to its own averages, keeping both original budgets. -/
theorem regularization_list_output_average_of_incidence_girth {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (girth : (k:ℕ∞) < (pathIncidenceGraph paths).egirth)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ localOrderAdmissible half k rows ∧
      M ≤ 392*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ listOutputAverageCaps rows := by
  refine regularization_list_output_average_of_rectangle_splits (k := k) paths simple half ?_
    hn hp dense long (by omega) le_rfl
  intro A B D L
  let rectangle := restrictListPaths paths A B
  have rectangleSimple (i : B) : (rectangle i).Nodup := restrictListPath_nodup (simple i.val) A
  have restricted : localOrderAdmissible half k rectangle := by
    cases half
    · exact restrictListPaths_fullFree simple allowed A B
    · exact restrictListPaths_halfFree simple allowed A B
  have grew : (pathIncidenceGraph paths).egirth ≤ (pathIncidenceGraph rectangle).egirth :=
    pathIncidenceGraph_egirth_le_of_embedding Subtype.val Subtype.val Subtype.val_injective
      Subtype.val_injective (fun {_ _} on => mem_restrictListPath.mp on)
  exact listRegularizedPaths_admissible_of_incidence_girth rectangleSimple restricted (girth.trans_le grew) D L

/-- The output-average criterion also applies to distinct nonempty rows. -/
theorem regularization_literal_output_average_of_incidence_girth {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (girth : (k:ℕ∞) < (pathIncidenceGraph paths).egirth)
    (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ localOrderAdmissible half k rows ∧
      M ≤ 7056*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ listOutputAverageCaps rows := by
  obtain ⟨v,vFit,q,qFit,rows,oneToOne,nonempty,simple,legal,keep,upper,caps⟩ :=
    regularization_list_output_average_distinct_of_indexed paths distinct (fun i => (valid i).1) (fun i => (valid i).2)
      allowed two hn hp dense
      (regularization_list_output_average_of_incidence_girth paths (fun i => (valid i).2) allowed girth hn hp dense)
  exact ⟨v,vFit,q,qFit,rows,oneToOne,fun i => ⟨nonempty i,simple i⟩,legal,keep,upper,caps⟩

end OnlineReachabilityPreservers
