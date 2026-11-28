import OnlineReachabilityPreservers.ShortIncidenceRowPacking

/-! Compute the incidence connections used in the width tests. -/

namespace OnlineReachabilityPreservers

open Finset SimpleGraph

section IncidenceArcs

variable {I V : Type*} [DecidableEq I] [Fintype I] [DecidableEq V]

/-- Both directions of each incidence, enumerated from the input lists. -/
def pathIncidenceArcs (rows : I → List V) : Arcs (I ⊕ V) :=
  univ.biUnion fun i =>
    ((rows i).toFinset.image fun x => (Sum.inl i,Sum.inr x)) ∪
      ((rows i).toFinset.image fun x => (Sum.inr x,Sum.inl i))

theorem pathIncidenceArcs_edge {rows : I → List V} {u v : I ⊕ V} :
    Edge (pathIncidenceArcs rows) u v ↔ (pathIncidenceGraph rows).Adj u v := by
  cases u <;> cases v <;>
    simp [Edge,pathIncidenceArcs,pathIncidenceGraph,mem_biUnion,mem_image,Prod.mk.injEq]

/-- Remove the arcs touching a deleted incidence label. -/
def deletedIncidenceArcs (rows : I → List V) (root : I ⊕ V) : Arcs (I ⊕ V) :=
  (pathIncidenceArcs rows).filter fun e => e.1 ≠ root ∧ e.2 ≠ root

theorem deletedIncidenceArcs_edge {rows : I → List V} {root u v : I ⊕ V} :
    Edge (deletedIncidenceArcs rows root) u v ↔ (pathIncidenceGraph rows).Adj u v ∧ u ≠ root ∧ v ≠ root := by
  change (u,v) ∈ (pathIncidenceArcs rows).filter _ ↔ _
  rw [mem_filter]
  exact and_congr_left fun _ => pathIncidenceArcs_edge

end IncidenceArcs

section BoundedWalks

variable {A : Type*} [DecidableEq A] {G : SimpleGraph A} {arcs : Arcs A} {root : A}

private theorem mem_reachIn_of_avoiding_walk
    (edges : ∀ {u v}, Edge arcs u v ↔ G.Adj u v ∧ u ≠ root ∧ v ≠ root)
    {x y : A} (w : G.Walk x y) (off : root ∉ w.support) {radius : ℕ} (short : w.length ≤ radius) :
    x ∈ reachIn arcs y radius := by
  induction w generalizing radius with
  | nil => exact target_mem_reachIn arcs _ _
  | @cons x u y edge tail previous =>
    cases radius with
    | zero => simp at short
    | succ r =>
      have start : x ≠ root := fun eq => off (eq ▸ (SimpleGraph.Walk.cons edge tail).start_mem_support)
      have remaining : root ∉ tail.support := fun on => off (by
        simp only [Walk.support_cons,List.mem_cons]
        exact Or.inr on)
      have next : u ≠ root := fun eq => remaining (eq ▸ tail.start_mem_support)
      exact reachIn_succ.mpr (Or.inr ⟨u,edges.mpr ⟨edge,start,next⟩,
        previous remaining (Nat.le_of_succ_le_succ short)⟩)

/-- Backward reachability decides whether there is a bounded walk in
the original graph avoiding the removed label. -/
theorem mem_reachIn_iff_avoiding_walk
    (edges : ∀ {u v}, Edge arcs u v ↔ G.Adj u v ∧ u ≠ root ∧ v ≠ root)
    {x y : A} (off : x ≠ root) (radius : ℕ) :
    x ∈ reachIn arcs y radius ↔ ∃ w : G.Walk x y, w.length ≤ radius ∧ root ∉ w.support := by
  refine ⟨?_,fun ⟨w,short,avoids⟩ => mem_reachIn_of_avoiding_walk (fun {_ _} => edges) w avoids short⟩
  induction radius generalizing x with
  | zero =>
    intro found
    have same : x = y := by simpa only [reachIn,mem_singleton] using found
    subst y
    exact ⟨SimpleGraph.Walk.nil,by simp,by simpa only [Walk.support_nil,List.mem_singleton] using off.symm⟩
  | succ k previous =>
    intro found
    rcases reachIn_succ.mp found with earlier | ⟨v,e,tail⟩
    · obtain ⟨w,short,avoids⟩ := previous off earlier
      exact ⟨w,short.trans (Nat.le_succ _),avoids⟩
    · obtain ⟨edge,_,away⟩ := edges.mp e
      obtain ⟨w,short,avoids⟩ := previous away tail
      refine ⟨SimpleGraph.Walk.cons edge w, Nat.succ_le_succ short,?_⟩
      simp only [Walk.support_cons,List.mem_cons,not_or]
      exact ⟨off.symm,avoids⟩

end BoundedWalks

section Groups

variable {I V : Type*} [DecidableEq I] [Fintype I] [LinearOrder V] [Fintype V]

/-- The finite arc computation of the short links among one row's neighbors. -/
def shortIncidenceRowGraphBySearch (rows : I → List V) (radius : ℕ) (i : I) : Arcs V :=
  let links := deletedIncidenceArcs rows (.inl i)
  ((rows i).toFinset ×ˢ (rows i).toFinset).filter fun (x,y) =>
    Sum.inr x ∈ reachIn links (.inr y) radius ∨ Sum.inr y ∈ reachIn links (.inr x) radius

theorem shortIncidenceRowGraphBySearch_eq (rows : I → List V) (radius : ℕ) (i : I) :
    shortIncidenceRowGraphBySearch rows radius i = shortIncidenceRowGraph rows radius i := by
  ext e
  obtain ⟨x,y⟩ := e
  change Edge (shortIncidenceRowGraphBySearch rows radius i) x y ↔
    Edge (shortIncidenceRowGraph rows radius i) x y
  rw [shortIncidenceRowGraph_edge]
  simp only [Edge,shortIncidenceRowGraphBySearch,mem_filter,mem_product,List.mem_toFinset]
  rw [mem_reachIn_iff_avoiding_walk (fun {_ _} => deletedIncidenceArcs_edge) (by simp) radius,
    mem_reachIn_iff_avoiding_walk (fun {_ _} => deletedIncidenceArcs_edge) (by simp) radius]
  unfold shortIncidenceRowLink
  constructor
  · rintro ⟨⟨onX,onY⟩,route | route⟩
    · exact Or.inl ⟨onX,onY,route⟩
    · exact Or.inr ⟨onY,onX,route⟩
  · rintro (⟨onX,onY,route⟩ | ⟨onY,onX,route⟩)
    · exact ⟨⟨onX,onY⟩,Or.inl route⟩
    · exact ⟨⟨onX,onY⟩,Or.inr route⟩

/-- Compute the connected group of short links by finite searches. -/
def shortIncidenceRowGroupBySearch (rows : I → List V) (radius : ℕ) (i : I) (x : V) : Finset V :=
  linkedGroupComponent (rows i).toFinset (shortIncidenceRowGraphBySearch rows radius i) x

theorem shortIncidenceRowGroupBySearch_eq (rows : I → List V) (radius : ℕ) (i : I) (x : V) :
    shortIncidenceRowGroupBySearch rows radius i x = shortIncidenceRowGroup rows radius i x := by
  unfold shortIncidenceRowGroupBySearch shortIncidenceRowGroup
  rw [shortIncidenceRowGraphBySearch_eq]

/-- Compute the entire deleted-row component among that row's neighbors. -/
def incidenceRowDeletionGroupBySearch (rows : I → List V) (i : I) (x : V) : Finset V :=
  (rows i).toFinset.filter fun y =>
    Sum.inr x ∈ reachIn (deletedIncidenceArcs rows (.inl i)) (.inr y) (Fintype.card (I ⊕ V))

/-- A simple path has fewer edges than the number of incidence labels,
so the finite search also recognizes unrestricted deletion components. -/
theorem incidenceRowDeletionGroupBySearch_eq (rows : I → List V) (i : I) (x : V) :
    incidenceRowDeletionGroupBySearch rows i x = incidenceRowDeletionGroup rows i x := by
  ext y
  simp only [incidenceRowDeletionGroupBySearch,mem_filter,List.mem_toFinset,mem_incidenceRowDeletionGroup]
  rw [mem_reachIn_iff_avoiding_walk (fun {_ _} => deletedIncidenceArcs_edge) (by simp)]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨w,_,avoids⟩
    exact ⟨w,avoids⟩
  · rintro ⟨w,avoids⟩
    exact ⟨w.bypass,w.bypass_isPath.length_lt.le,fun h => avoids (w.support_bypass_subset_support h)⟩

end Groups

end OnlineReachabilityPreservers
