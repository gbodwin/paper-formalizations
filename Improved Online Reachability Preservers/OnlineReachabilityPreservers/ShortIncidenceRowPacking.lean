import OnlineReachabilityPreservers.ShortIncidenceProjection
import OnlineReachabilityPreservers.ShortReturnPieceComponents

/-! Pack neighbors in the same component of the bounded-link graph. -/

namespace OnlineReachabilityPreservers

open SimpleGraph Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

section Groups

variable {I V : Type*} [LinearOrder V] [Fintype V]

/-- Two neighbors of a row have a short connection after deleting the row. -/
def shortIncidenceRowLink (rows : I → List V) (radius : ℕ) (i : I) (x y : V) : Prop :=
  x ∈ rows i ∧ y ∈ rows i ∧
    ∃ w : (pathIncidenceGraph rows).Walk (.inr x) (.inr y), w.length ≤ radius ∧ Sum.inl i ∉ w.support

/-- Make a graph on the neighbors of a deleted row using the short links. -/
noncomputable def shortIncidenceRowGraph (rows : I → List V) (radius : ℕ) (i : I) : Arcs V := by
  classical
  exact univ.filter fun e => shortIncidenceRowLink rows radius i e.1 e.2 ∨
    shortIncidenceRowLink rows radius i e.2 e.1

omit [LinearOrder V] in
theorem shortIncidenceRowGraph_edge {rows : I → List V} {radius : ℕ} {i : I} {x y : V} :
    Edge (shortIncidenceRowGraph rows radius i) x y ↔
      shortIncidenceRowLink rows radius i x y ∨ shortIncidenceRowLink rows radius i y x := by
  classical
  simp only [shortIncidenceRowGraph,Edge,mem_filter,mem_univ,true_and]

/-- A neighbor group consists of neighbors linked by a chain of short
connections in the graph with the row deleted. -/
noncomputable def shortIncidenceRowGroup (rows : I → List V) (radius : ℕ) (i : I) (x : V) : Finset V :=
  linkedGroupComponent (rows i).toFinset (shortIncidenceRowGraph rows radius i) x

/-- The short-link groups are the components that must fit within pieces. -/
theorem short_incidence_row_partition (rows : I → List V) (radius : ℕ) (i : I) (width : ℕ)
    (fits : ∀ x ∈ rows i, (shortIncidenceRowGroup rows radius i x).card ≤ width) :
    ∃ groups, CappedPathPartition (rows i).toFinset (shortIncidenceRowLink rows radius i) width groups :=
  (cappedPathPartition_iff_component_room _ _ _ _ (fun {_ _} => shortIncidenceRowGraph_edge)
    (fun {_ _} h => ⟨List.mem_toFinset.mpr h.1,List.mem_toFinset.mpr h.2.1⟩)).mpr
    (fun x on => fits x (List.mem_toFinset.mp on))

/-- Every short-link group is contained in the corresponding component
of the original graph with the row deleted. -/
theorem shortIncidenceRowGroup_subset {rows : I → List V} (radius : ℕ) (i : I) (x : V) :
    shortIncidenceRowGroup rows radius i x ⊆ incidenceRowDeletionGroup rows i x := by
  intro y on
  change y ∈ (rows i).toFinset.filter (fun v =>
    componentLabel (shortIncidenceRowGraph rows radius i) v =
      componentLabel (shortIncidenceRowGraph rows radius i) x) at on
  obtain ⟨present,same⟩ := mem_filter.mp on
  have connected := RowDeletionConnected.equivalence rows i
  have link {a b : V} (edge : Edge (shortIncidenceRowGraph rows radius i) a b) :
      RowDeletionConnected rows i a b := by
    rcases shortIncidenceRowGraph_edge.mp edge with forward | backward
    · obtain ⟨_,_,w,_,off⟩ := forward
      exact ⟨w,off⟩
    · obtain ⟨_,_,w,_,off⟩ := backward
      exact connected.symm ⟨w,off⟩
  have reaches := (componentLabel_eq.mp same).2
  refine mem_incidenceRowDeletionGroup.mpr ⟨List.mem_toFinset.mp present,?_⟩
  clear on present same
  induction reaches with
  | refl => exact connected.refl _
  | tail _ edge previous => exact connected.trans previous (link edge)

/-- Exact row projection through degree copies can only shrink the
short-link groups. Each witness walk projects at its original length. -/
theorem shortIncidenceRowGroup_card_le_project {W : Type*} [LinearOrder W] [Fintype W]
    {rows : I → List V} {copies : I → List W} (project : W → V)
    (simple : ∀ i, (rows i).Nodup) (projects : ∀ i, (copies i).map project = rows i)
    (radius : ℕ) (i : I) (x : W) : (shortIncidenceRowGroup copies radius i x).card ≤
      (shortIncidenceRowGroup rows radius i (project x)).card := by
  have members {j y} (on : y ∈ copies j) : project y ∈ rows j := by
    rw [← projects j]
    exact List.mem_map_of_mem (f := project) on
  let f := pathIncidenceGraph_hom id project (fun {_ _} => members)
  have links {u v : W} (on : shortIncidenceRowLink copies radius i u v) :
      shortIncidenceRowLink rows radius i (project u) (project v) := by
    obtain ⟨first,last,w,near,avoids⟩ := on
    refine ⟨members first,members last,w.map f,?_,?_⟩
    · change (w.map f).length ≤ radius
      simpa only [Walk.length_map] using near
    · change Sum.inl i ∉ (w.map f).support
      simp only [Walk.support_map,List.mem_map]
      rintro ⟨a,inside,same⟩
      have eq : Sum.map (id : I → I) project a = Sum.inl i := same
      cases a with
      | inl j => exact avoids (Sum.inl.inj eq ▸ inside)
      | inr _ => cases eq
  apply linkedGroupComponent_card_le_project project _ _ _ x
  · exact fun on => List.mem_toFinset.mpr (members (List.mem_toFinset.mp on))
  · intro u left v right same
    have nodup : ((copies i).map project).Nodup := projects i ▸ simple i
    exact List.inj_on_of_nodup_map nodup (List.mem_toFinset.mp left) (List.mem_toFinset.mp right) same
  · intro u v edge
    exact shortIncidenceRowGraph_edge.mpr ((shortIncidenceRowGraph_edge.mp edge).imp links links)

end Groups

/-- Pack groups of row neighbors connected by chains of short deletion
links. The pieces preserve all mass, every vertex degree, and the original
cutoff in either bridge mode. There is at most one piece of at most half
the width per original row. -/
theorem split_of_short_incidence_row_group_room {V : Type*} [LinearOrder V] [Fintype V]
    {p width k : ℕ} {half : Bool} {rows : Fin p → List V}
    (simple : ∀ i, (rows i).Nodup) (legal : localOrderAdmissible half k rows)
    (fits : ∀ i, ∀ x ∈ rows i, (shortIncidenceRowGroup rows (k-2) i x).card ≤ width) :
    ∃ (sizes : Fin p → ℕ) (pieces : (Σₗ i : Fin p, Fin (sizes i)) → List V),
      (∀ i, (pieces i).Nodup) ∧ localOrderAdmissible half k pieces ∧
      (∀ i, (pieces i).length ≤ width) ∧
      (∑ i, (pieces i).length) = ∑ i, (rows i).length ∧
      (∀ x, (occurrences (fun i => (pieces i).toFinset) x).card =
        (occurrences (fun i => (rows i).toFinset) x).card) ∧
      ({i ∈ univ | (pieces i).length ≤ width/2} : Finset (Σₗ i : Fin p, Fin (sizes i))).card ≤ p := by
  let linked := shortIncidenceRowLink rows (k-2)
  refine split_of_capped_path_partitions_with_membership (half := half) (cutoff := k)
    simple linked (fun i => short_incidence_row_partition rows (k-2) i width (fits i)) ?_
  intro sizes pieces members steps _ together
  let J := Σₗ i : Fin p, Fin (sizes i)
  let parent : J → Fin p := Sigma.fst
  have ordered : Monotone parent := by
    intro a b order
    rcases Sigma.Lex.le_def.mp order with before | ⟨same,_⟩
    · exact before.le
    · exact same.le
  refine localOrderAdmissible_of_short_incidence_links legal parent id ordered
    (fun {_ _} h => members h) (fun {_ _ _} h => steps h) ?_
  intro a x y u v atX atY edgeX edgeY w near avoids
  cases x with
  | inr x =>
    have equal : Sum.inr x = Sum.map parent (id : V → V) y := atX.trans atY.symm
    cases y with
    | inl y => cases equal
    | inr y => exact congrArg Sum.inr (Sum.inr.inj equal)
  | inl i =>
    have equal : Sum.inl (parent i) = Sum.map parent (id : V → V) y := atX.trans atY.symm
    cases y with
    | inr y => cases equal
    | inl j =>
      have same : parent i = parent j := Sum.inl.inj equal
      cases u with
      | inl u => exact edgeX.elim
      | inr u =>
        cases v with
        | inl v => exact edgeY.elim
        | inr v =>
          have absent : Sum.inl (parent i) ∉ w.support := by
            have root : Sum.inl (parent i) = a := atX
            rw [root]
            exact avoids
          have onV : v ∈ rows i.fst := by
            have member : v ∈ rows j.fst := members edgeY
            change i.fst = j.fst at same
            rwa [same]
          have link : linked i.fst u v := ⟨members edgeX,onV,w,near,absent⟩
          exact congrArg Sum.inl (together same edgeX edgeY link)

/-- After admissible degree copying, the groups of neighbors linked within
radius `k-2` after deleting each row must fit the original length width. This
gives all four original-average caps and one quarter of the original mass. -/
theorem regularization_list_frozen_of_short_incidence_row_group_room {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (copiedLegal : let M := ∑ i, (paths i).length
      localOrderAdmissible half k (splitListVertices paths (4*M/n)))
    (fits : let M := ∑ i, (paths i).length
      let copies := splitListVertices paths (4*M/n)
      ∀ i, ∀ x ∈ copies i, (shortIncidenceRowGroup copies (k-2) i x).card ≤ 4*M/p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_after_packing_standard_degree_copies paths hn hp dense long
    (split_of_short_incidence_row_group_room (fun i => splitListVertices_simple paths _ i (simple i))
      copiedLegal fits)

/-- Full exclusion survives degree copying. Check that each deleted
row's group of short-linked neighbors fit the original path width. -/
theorem regularization_list_frozen_full_of_short_incidence_row_group_room {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (legal : BridgeFree (Before paths) k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (fits : let M := ∑ i, (paths i).length
      let copies := splitListVertices paths (4*M/n)
      ∀ i, ∀ x ∈ copies i, (shortIncidenceRowGroup copies (k-2) i x).card ≤ 4*M/p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_of_short_incidence_row_group_room (half := false) paths simple hn hp dense long
    (legal.split_list_vertices_any (·.fst) (fun {i _ _} => splitListVertices_step (simple i))) fits

/-- The groups of short-linked neighbors may also be checked before degree copying. -/
theorem regularization_list_frozen_full_of_original_short_incidence_row_group_room {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (legal : BridgeFree (Before paths) k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (fits : let M := ∑ i, (paths i).length
      ∀ i, ∀ x ∈ paths i, (shortIncidenceRowGroup paths (k-2) i x).card ≤ 4*M/p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  apply regularization_list_frozen_full_of_short_incidence_row_group_room paths simple legal hn hp dense long
  dsimp only
  intro i x member
  let D := 4*(∑ i, (paths i).length)/n
  have projects := splitListVertices_project paths D
  have on := List.mem_map_of_mem (f := Sigma.fst) member
  change x.fst ∈ ((splitListVertices paths D i).map fun v => v.fst) at on
  rw [projects i] at on
  exact (shortIncidenceRowGroup_card_le_project (W := ListVertexBlockIndex paths D)
    (fun v => v.fst) simple projects (k-2) i x).trans (fits i _ on)

/-- The frozen witness can be chosen to have distinct nonempty paths
at cutoffs of at least two. -/
theorem regularization_literal_frozen_of_short_incidence_row_group_room {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup) (legal : localOrderAdmissible half k paths)
    (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length)
    (copiedLegal : let M := ∑ i, (paths i).length
      localOrderAdmissible half k (splitListVertices paths (4*M/n)))
    (fits : let M := ∑ i, (paths i).length
      let copies := splitListVertices paths (4*M/n)
      ∀ i, ∀ x ∈ copies i, (shortIncidenceRowGroup copies (k-2) i x).card ≤ 4*M/p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ [] ∧ (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨n',vertexBudget,p',rowBudget,clean,injective,nonempty,cleanSimple,cleanLegal,mass,upper,caps⟩ :=
    regularization_list_frozen_distinct_of_indexed (retention := 8) paths distinct (fun i => (valid i).1)
      (fun i => (valid i).2) legal two hn hp dense le_rfl (fun long => by
        obtain ⟨v,vFits,q,qFits,rows,rowsSimple,allowed,keep,within,bounds⟩ :=
          regularization_list_frozen_of_short_incidence_row_group_room paths (fun i => (valid i).2)
            hn hp dense long copiedLegal fits
        exact ⟨v,vFits,q,qFits,rows,rowsSimple,allowed,keep.trans (Nat.mul_le_mul_right _ (by decide)),within,bounds⟩)
  exact ⟨n',vertexBudget,p',rowBudget,clean,injective,fun i => ⟨nonempty i,cleanSimple i⟩,cleanLegal,mass,upper,caps⟩


end OnlineReachabilityPreservers
