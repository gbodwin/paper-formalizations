import OnlineReachabilityPreservers.IncidenceGirthCleaning
import OnlineReachabilityPreservers.ShortReturnPiecePacking
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Incidence splits that separate whole components at a removed label. -/

namespace OnlineReachabilityPreservers

open SimpleGraph Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

/-- At an original label `a`, neighbors that lie in the same component
after deleting `a` must attach to the same copy of `a`. -/
def RespectsDeletionComponentsAt {A B : Type*} {G : SimpleGraph A} {H : SimpleGraph B}
    (f : G →g H) (a : B) : Prop :=
  ∀ {x y u v : A}, f x = a → f y = a → G.Adj x u → G.Adj y v →
    ∀ w : H.Walk (f u) (f v), a ∉ w.support → x = y

/-- At each projected label, neighbors joined by a walk of bounded
length after deleting that label must belong to the same copy. -/
def RespectsShortDeletionLinksAt {A B : Type*} {G : SimpleGraph A} {H : SimpleGraph B}
    (f : G →g H) (a : B) (radius : ℕ) : Prop :=
  ∀ {x y u v : A}, f x = a → f y = a → G.Adj x u → G.Adj y v →
    ∀ w : H.Walk (f u) (f v), w.length ≤ radius → a ∉ w.support → x = y

/-- A short connecting walk between two copies would project to a
forbidden short return to their common label. -/
theorem RespectsShortDeletionLinksAt.eq_of_walk {A B : Type*}
    {G : SimpleGraph A} {H : SimpleGraph B} {f : G →g H} {a : B} {radius : ℕ}
    (coherent : RespectsShortDeletionLinksAt f a radius) {x y : A}
    (left : f x = a) (right : f y = a) (walk : G.Walk x y)
    (short : walk.length ≤ radius+2) : x = y := by
  classical
  by_contra different
  let w := walk.bypass
  have simple := walk.bypass_isPath
  have bound : w.length ≤ radius+2 := walk.length_bypass_le_length.trans short
  have positive : 0 < w.length := by
    by_contra! zero
    exact different (Walk.eq_of_length_eq_zero (Nat.eq_zero_of_le_zero zero))
  let returns (j : ℕ) := 0 < j ∧ j ≤ w.length ∧ f (w.getVert j) = a
  have someReturn : ∃ j, returns j := ⟨w.length,positive,le_rfl,by rwa [Walk.getVert_length]⟩
  let j := Nat.find someReturn
  obtain ⟨jPos,jFits,jAt⟩ := Nat.find_spec someReturn
  change 0 < j at jPos
  change j ≤ w.length at jFits
  change f (w.getVert j) = a at jAt
  have avoids {i : ℕ} (iPos : 0 < i) (before : i < j) : f (w.getVert i) ≠ a := by
    intro atRoot
    exact (Nat.find_min someReturn before) ⟨iPos,before.le.trans jFits,atRoot⟩
  have first : G.Adj x (w.getVert 1) := by
    simpa only [Walk.getVert_zero, Nat.zero_add] using w.adj_getVert_succ (i := 0) positive
  have later : 1 < j := by
    by_contra! early
    have atOne : j = 1 := by omega
    rw [atOne] at jAt
    exact (f.map_adj first).ne (left.trans jAt.symm)
  have last : G.Adj (w.getVert j) (w.getVert (j-1)) := by
    have step := w.adj_getVert_succ (i := j-1) (by omega)
    rwa [show j-1+1 = j by omega,adj_comm] at step
  have endpoint : (w.drop 1).getVert (j-2) = w.getVert (j-1) := by
    rw [Walk.drop_getVert,show 1+(j-2) = j-1 by omega]
  let between := ((w.drop 1).take (j-2)).copy rfl endpoint
  have mappedAvoids : a ∉ (between.map f).support := by
    simp only [Walk.support_map,List.mem_map]
    rintro ⟨u,on,atRoot⟩
    obtain ⟨i,h,fit⟩ := Walk.mem_support_iff_exists_getVert.mp on
    have within : i ≤ j-2 := by
      simp only [between,Walk.length_copy,Walk.take_length,le_min_iff] at fit
      exact fit.1
    have fromWalk : between.getVert i = w.getVert (1+i) := by
      simp only [between,Walk.getVert_copy,Walk.take_getVert,Walk.drop_getVert,inf_eq_right.mpr within]
    rw [fromWalk] at h
    exact avoids (by omega) (by omega) (congrArg f h |>.trans atRoot)
  have betweenShort : (between.map f).length ≤ radius := by
    rw [Walk.length_map,Walk.length_copy,Walk.take_length]
    exact (min_le_left _ _).trans (by omega)
  have same := coherent left jAt first last (between.map f) betweenShort mappedAvoids
  have zero := simple.getVert_injOn (x₁ := 0) (x₂ := j) (by simp) jFits
    (by rwa [Walk.getVert_zero])
  omega

/-- A projection that respects the components at a deleted label has
at most one copy of that label in any connected component. -/
theorem RespectsDeletionComponentsAt.eq_of_reachable {A B : Type*}
    {G : SimpleGraph A} {H : SimpleGraph B} {f : G →g H} {a : B}
    (coherent : RespectsDeletionComponentsAt f a) {x y : A}
    (left : f x = a) (right : f y = a) (joined : G.Reachable x y) : x = y := by
  obtain ⟨w⟩ := joined
  apply RespectsShortDeletionLinksAt.eq_of_walk (radius := w.length) (f := f) (a := a) _ left right w (by omega)
  intro x y u v first last edgeA edgeB route _ avoids
  exact coherent first last edgeA edgeB route avoids

private theorem Bridge.incidence_reaches {J W : Type*} [DecidableEq W]
    {pieces : J → List W} {d : ℕ} (b : Bridge (Before pieces) d) :
    (∀ j, (pathIncidenceGraph pieces).Reachable (.inr (b.vertex 0)) (.inr (b.vertex j))) ∧
    (∀ j, (pathIncidenceGraph pieces).Reachable (.inr (b.vertex 0)) (.inl (b.arc j))) ∧
    (pathIncidenceGraph pieces).Reachable (.inr (b.vertex 0)) (.inl b.river) := by
  let G := pathIncidenceGraph pieces
  have atArc (j : Fin (d+1)) : G.Adj (.inr (b.vertex j.castSucc)) (.inl (b.arc j)) := (b.arcStep j).1
  have pastArc (j : Fin (d+1)) : G.Adj (.inl (b.arc j)) (.inr (b.vertex j.succ)) := (b.arcStep j).2.1
  have atRiver : G.Adj (.inr (b.vertex 0)) (.inl b.river) := b.riverStep.1
  have corners (j : Fin (d+2)) : G.Reachable (.inr (b.vertex 0)) (.inr (b.vertex j)) := by
    induction j using Fin.induction with
    | zero => exact .rfl
    | succ j previous => exact previous.trans ((atArc j).reachable.trans (pastArc j).reachable)
  exact ⟨corners,fun j => (corners j.castSucc).trans (atArc j).reachable,atRiver.reachable⟩

/-- Splitting only between components at each removed incidence label
preserves every bridge cutoff. In half mode, the pieces follow the
arrival order of their original rows. -/
theorem localOrderAdmissible_of_incidence_components {I J V W : Type*}
    [LinearOrder I] [LinearOrder J] [DecidableEq V] [DecidableEq W]
    {paths : I → List V} {pieces : J → List W} {half : Bool} {k : ℕ}
    (allowed : localOrderAdmissible half k paths)
    (parent : J → I) (project : W → V) (ordered : Monotone parent)
    (members : ∀ {i x}, x ∈ pieces i → project x ∈ paths (parent i))
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) (project x) (project y))
    (coherent : ∀ a, RespectsDeletionComponentsAt (pathIncidenceGraph_hom parent project
      (fun {_ _} => members)) a) : localOrderAdmissible half k pieces := by
  let f := pathIncidenceGraph_hom parent project (fun {_ _} => members)
  let lift {d : ℕ} (b : Bridge (Before pieces) d) : Bridge (Before paths) d := by
    have reached := b.incidence_reaches
    have corners := reached.1
    have arcs := reached.2.1
    have river := reached.2.2
    have equal {a c : J ⊕ W}
        (ra : (pathIncidenceGraph pieces).Reachable (.inr (b.vertex 0)) a)
        (rc : (pathIncidenceGraph pieces).Reachable (.inr (b.vertex 0)) c) (same : f a = f c) : a = c :=
      RespectsDeletionComponentsAt.eq_of_reachable (f := f) (coherent (f a))
        rfl same.symm (ra.symm.trans rc)
    refine ⟨project ∘ b.vertex,parent ∘ b.arc,parent b.river,?_,?_,?_,steps b.riverStep,
      fun i => steps (b.arcStep i)⟩
    · intro i j same
      exact b.distinctVertices (Sum.inr.inj (equal (corners i) (corners j) (congrArg Sum.inr same)))
    · intro i j same
      exact b.distinctArcs (Sum.inl.inj (equal (arcs i) (arcs j) (congrArg Sum.inl same)))
    · intro i same
      exact b.river_ne_arc i (Sum.inl.inj (equal river (arcs i) (congrArg Sum.inl same)))
  cases half
  · intro d fit
    exact ⟨fun b => (allowed fit).false (lift b)⟩
  · intro d fit b earlier
    let original := lift b
    have strict : original.arc (Fin.last d) < original.river :=
      lt_of_le_of_ne (ordered earlier.le) (original.river_ne_arc _).symm
    exact allowed fit original strict

section RowPacking

variable {I V : Type*} [DecidableEq V]

/-- Two vertices are connected in the incidence graph with the indicated
row deleted. The connecting walk may use any of the other rows. -/
def RowDeletionConnected (rows : I → List V) (i : I) (x y : V) : Prop :=
  ∃ w : (pathIncidenceGraph rows).Walk (.inr x) (.inr y), Sum.inl i ∉ w.support

omit [DecidableEq V] in
theorem RowDeletionConnected.equivalence (rows : I → List V) (i : I) :
    Equivalence (RowDeletionConnected rows i) := by
  refine ⟨fun x => ⟨SimpleGraph.Walk.nil, by simp⟩,?_,?_⟩
  · rintro x y ⟨w,avoids⟩
    exact ⟨w.reverse, by simpa only [Walk.support_reverse,List.mem_reverse] using avoids⟩
  · rintro x y z ⟨w,first⟩ ⟨t,second⟩
    exact ⟨w.append t, fun on => (Walk.mem_support_append_iff _ _).mp on |>.elim first second⟩

/-- The vertices on a row in the same incidence component as `x` after
removing that row label. -/
noncomputable def incidenceRowDeletionGroup (rows : I → List V) (i : I) (x : V) : Finset V := by
  classical
  exact (rows i).toFinset.filter (RowDeletionConnected rows i x)

theorem mem_incidenceRowDeletionGroup {rows : I → List V} {i : I} {x y : V} :
    y ∈ incidenceRowDeletionGroup rows i x ↔ y ∈ rows i ∧ RowDeletionConnected rows i x y := by
  classical
  change y ∈ (rows i).toFinset.filter _ ↔ _
  simp only [mem_filter,List.mem_toFinset]

/-- Splitting vertex labels cannot increase a deleted-row component's
size when its original row is simple and projection preserves the row. -/
theorem incidenceRowDeletionGroup_card_le_project {W : Type*} [DecidableEq W]
    {rows : I → List V} {copies : I → List W} (project : W → V)
    (simple : ∀ i, (rows i).Nodup) (projects : ∀ i, (copies i).map project = rows i)
    (i : I) (x : W) : (incidenceRowDeletionGroup copies i x).card ≤
      (incidenceRowDeletionGroup rows i (project x)).card := by
  have members {j y} (on : y ∈ copies j) : project y ∈ rows j := by
    rw [← projects j]
    exact List.mem_map_of_mem (f := project) on
  let f := pathIncidenceGraph_hom id project (fun {_ _} => members)
  apply card_le_card_of_injOn project
  · intro y on
    obtain ⟨member,w,avoids⟩ := mem_incidenceRowDeletionGroup.mp on
    refine mem_incidenceRowDeletionGroup.mpr ⟨members member,w.map f,?_⟩
    change Sum.inl i ∉ (w.map f).support
    simp only [Walk.support_map,List.mem_map]
    rintro ⟨a,inside,same⟩
    have eq : Sum.map (id : I → I) project a = Sum.inl i := same
    cases a with
    | inl j => exact avoids (Sum.inl.inj eq ▸ inside)
    | inr y => cases eq
  · intro y onY z onZ same
    have left := (mem_incidenceRowDeletionGroup.mp onY).1
    have right := (mem_incidenceRowDeletionGroup.mp onZ).1
    have nodup : ((copies i).map project).Nodup := projects i ▸ simple i
    exact List.inj_on_of_nodup_map nodup left right same

/-- The deleted-row groups partition its neighbors and keep linked pairs
together whenever each group fits the width. -/
theorem incidence_row_deletion_partition (rows : I → List V) (i : I) (width : ℕ)
    (fits : ∀ x ∈ rows i, (incidenceRowDeletionGroup rows i x).card ≤ width) :
    ∃ groups, CappedPathPartition (rows i).toFinset
      (fun x y => x ∈ rows i ∧ y ∈ rows i ∧ RowDeletionConnected rows i x y) width groups := by
  classical
  let group := incidenceRowDeletionGroup rows i
  let groups := (rows i).toFinset.image group
  have connected := RowDeletionConnected.equivalence rows i
  have own {x : V} (on : x ∈ rows i) : x ∈ group x :=
    mem_incidenceRowDeletionGroup.mpr ⟨on,connected.refl x⟩
  have same {x y : V} (reach : RowDeletionConnected rows i x y) : group x = group y := by
    ext z
    simp only [group,mem_incidenceRowDeletionGroup]
    exact and_congr_right fun _ => ⟨connected.trans (connected.symm reach),connected.trans reach⟩
  refine ⟨groups,⟨?_,?_,?_,?_,?_⟩⟩
  · ext x
    simp only [mem_biUnion,id_eq,List.mem_toFinset]
    exact ⟨fun ⟨g,on,inside⟩ => by
      obtain ⟨y,_,rfl⟩ := mem_image.mp on
      exact (mem_incidenceRowDeletionGroup.mp inside).1,
      fun on => ⟨group x,mem_image_of_mem _ (List.mem_toFinset.mpr on),own on⟩⟩
  · intro g onG h onH different
    obtain ⟨x,_,rfl⟩ := mem_image.mp onG
    obtain ⟨y,_,rfl⟩ := mem_image.mp onH
    exact disjoint_left.mpr fun z left right => different (same
      (connected.trans (mem_incidenceRowDeletionGroup.mp left).2
        (connected.symm (mem_incidenceRowDeletionGroup.mp right).2)))
  · intro g on
    obtain ⟨x,member,rfl⟩ := mem_image.mp on
    exact ⟨x,own (List.mem_toFinset.mp member)⟩
  · intro g on
    obtain ⟨x,member,rfl⟩ := mem_image.mp on
    exact fits x (List.mem_toFinset.mp member)
  · intro x y linked
    exact ⟨group x,mem_image_of_mem _ (List.mem_toFinset.mpr linked.1),own linked.1,
      mem_incidenceRowDeletionGroup.mpr linked.2⟩

end RowPacking

/-- Pack width-bounded groups of whole incidence components within each
row. The pieces preserve all mass, every vertex degree, and the original
cutoff in either bridge mode. There is at most one piece of at most half
the width per original row. -/
theorem split_of_incidence_row_deletion_group_room {V : Type*} [LinearOrder V] [Fintype V]
    {p width k : ℕ} {half : Bool} {rows : Fin p → List V}
    (simple : ∀ i, (rows i).Nodup) (legal : localOrderAdmissible half k rows)
    (fits : ∀ i, ∀ x ∈ rows i, (incidenceRowDeletionGroup rows i x).card ≤ width) :
    ∃ (sizes : Fin p → ℕ) (pieces : (Σₗ i : Fin p, Fin (sizes i)) → List V),
      (∀ i, (pieces i).Nodup) ∧ localOrderAdmissible half k pieces ∧
      (∀ i, (pieces i).length ≤ width) ∧
      (∑ i, (pieces i).length) = ∑ i, (rows i).length ∧
      (∀ x, (occurrences (fun i => (pieces i).toFinset) x).card =
        (occurrences (fun i => (rows i).toFinset) x).card) ∧
      ({i ∈ univ | (pieces i).length ≤ width/2} : Finset (Σₗ i : Fin p, Fin (sizes i))).card ≤ p := by
  let linked (i : Fin p) (x y : V) := x ∈ rows i ∧ y ∈ rows i ∧ RowDeletionConnected rows i x y
  refine split_of_capped_path_partitions_with_membership (half := half) (cutoff := k)
    simple linked (fun i => incidence_row_deletion_partition rows i width (fits i)) ?_
  intro sizes pieces members steps _ together
  let J := Σₗ i : Fin p, Fin (sizes i)
  let parent : J → Fin p := Sigma.fst
  have ordered : Monotone parent := by
    intro a b order
    rcases Sigma.Lex.le_def.mp order with before | ⟨same,_⟩
    · exact before.le
    · exact same.le
  refine localOrderAdmissible_of_incidence_components legal parent id ordered
    (fun {_ _} h => members h) (fun {_ _ _} h => steps h) ?_
  intro a x y u v atX atY edgeX edgeY w avoids
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
          have link : linked i.fst u v := ⟨members edgeX,onV,w,absent⟩
          exact congrArg Sum.inl (together same edgeX edgeY link)

/-- After admissible degree copying, the neighbors of each deleted row
in each remaining component must fit the original length width. This
gives all four original-average caps and one quarter of the original mass. -/
theorem regularization_list_frozen_of_incidence_row_deletion_group_room {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (copiedLegal : let M := ∑ i, (paths i).length
      localOrderAdmissible half k (splitListVertices paths (4*M/n)))
    (fits : let M := ∑ i, (paths i).length
      let copies := splitListVertices paths (4*M/n)
      ∀ i, ∀ x ∈ copies i, (incidenceRowDeletionGroup copies i x).card ≤ 4*M/p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_after_packing_standard_degree_copies paths hn hp dense long
    (split_of_incidence_row_deletion_group_room (fun i => splitListVertices_simple paths _ i (simple i))
      copiedLegal fits)

/-- Full exclusion survives degree copying. Check that each deleted
row's neighbors in any single component fit the original path width. -/
theorem regularization_list_frozen_full_of_incidence_row_deletion_group_room {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (legal : BridgeFree (Before paths) k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (fits : let M := ∑ i, (paths i).length
      let copies := splitListVertices paths (4*M/n)
      ∀ i, ∀ x ∈ copies i, (incidenceRowDeletionGroup copies i x).card ≤ 4*M/p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_of_incidence_row_deletion_group_room (half := false) paths simple hn hp dense long
    (legal.split_list_vertices_any (·.fst) (fun {i _ _} => splitListVertices_step (simple i))) fits

/-- Deleted-row components may also be checked before degree copying. -/
theorem regularization_list_frozen_full_of_original_incidence_row_deletion_group_room {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (legal : BridgeFree (Before paths) k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (fits : let M := ∑ i, (paths i).length
      ∀ i, ∀ x ∈ paths i, (incidenceRowDeletionGroup paths i x).card ≤ 4*M/p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  apply regularization_list_frozen_full_of_incidence_row_deletion_group_room paths simple legal hn hp dense long
  dsimp only
  intro i x member
  let D := 4*(∑ i, (paths i).length)/n
  have projects := splitListVertices_project paths D
  have on := List.mem_map_of_mem (f := Sigma.fst) member
  change x.fst ∈ ((splitListVertices paths D i).map fun v => v.fst) at on
  rw [projects i] at on
  exact (incidenceRowDeletionGroup_card_le_project Sigma.fst simple projects i x).trans (fits i _ on)

/-- The frozen witness can be chosen to have distinct nonempty paths
at cutoffs of at least two. -/
theorem regularization_literal_frozen_of_incidence_row_deletion_group_room {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup) (legal : localOrderAdmissible half k paths)
    (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length)
    (copiedLegal : let M := ∑ i, (paths i).length
      localOrderAdmissible half k (splitListVertices paths (4*M/n)))
    (fits : let M := ∑ i, (paths i).length
      let copies := splitListVertices paths (4*M/n)
      ∀ i, ∀ x ∈ copies i, (incidenceRowDeletionGroup copies i x).card ≤ 4*M/p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ [] ∧ (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨n',vertexBudget,p',rowBudget,clean,injective,nonempty,cleanSimple,cleanLegal,mass,upper,caps⟩ :=
    regularization_list_frozen_distinct_of_indexed (retention := 8) paths distinct (fun i => (valid i).1)
      (fun i => (valid i).2) legal two hn hp dense le_rfl (fun long => by
        obtain ⟨v,vFits,q,qFits,rows,rowsSimple,allowed,keep,within,bounds⟩ :=
          regularization_list_frozen_of_incidence_row_deletion_group_room paths (fun i => (valid i).2)
            hn hp dense long copiedLegal fits
        exact ⟨v,vFits,q,qFits,rows,rowsSimple,allowed,keep.trans (Nat.mul_le_mul_right _ (by decide)),within,bounds⟩)
  exact ⟨n',vertexBudget,p',rowBudget,clean,injective,fun i => ⟨nonempty i,cleanSimple i⟩,cleanLegal,mass,upper,caps⟩

end OnlineReachabilityPreservers
