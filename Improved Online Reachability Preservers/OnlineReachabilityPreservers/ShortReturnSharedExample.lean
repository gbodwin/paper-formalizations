import OnlineReachabilityPreservers.BridgeAtJoint
import OnlineReachabilityPreservers.ShortReturnSharedClipping

/-! A joint example where one deletion can pay both component excesses. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset

private def sharedSpine : List (Fin 57) := List.ofFn fun i : Fin 15 => i.castLE (by decide)

private def sharedLeaf (j : Fin 10) : Fin 57 := ⟨j.val+15, by have := j.isLt; omega⟩
private def sharedOut (j : Fin 10) : Fin 22 := ⟨j.val+2, by have := j.isLt; omega⟩
private def sharedIn (j : Fin 10) : Fin 22 := ⟨j.val+12, by have := j.isLt; omega⟩

/-- Place a pair of reversed length-15 rows and a bidirected 10-leaf
star on a common vertex. The reserve vertices give the original degree width. -/
def sharedClippingExampleRows : Fin 22 → List (Fin 57) :=
  Fin.addCases (m := 2) (n := 20) (fun i => if i = 0 then sharedSpine else sharedSpine.reverse)
    (Fin.addCases (m := 10) (n := 10) (fun j => [0,sharedLeaf j]) (fun j => [sharedLeaf j,0]))

private theorem sharedClippingExample_mass_simple :
    (∑ i, (sharedClippingExampleRows i).length) = 70 ∧
      ∀ i, (sharedClippingExampleRows i).Nodup := by decide +kernel

private theorem shared_row_cases (i : Fin 22) :
    i = 0 ∨ i = 1 ∨ (∃ j, i = sharedOut j) ∨ (∃ j, i = sharedIn j) := by
  by_cases h0 : i = 0
  · exact Or.inl h0
  by_cases h1 : i = 1
  · exact Or.inr (Or.inl h1)
  have above : 2 ≤ i.val := by
    have zero : i.val ≠ 0 := fun h => h0 (Fin.ext h)
    have one : i.val ≠ 1 := fun h => h1 (Fin.ext h)
    omega
  by_cases out : i.val < 12
  · exact Or.inr (Or.inr (Or.inl ⟨⟨i.val-2, by omega⟩, Fin.ext (by simp [sharedOut]; omega)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨⟨i.val-12, by have := i.isLt; omega⟩, Fin.ext (by simp [sharedIn]; omega)⟩))

private theorem shared_out_row (j : Fin 10) : sharedClippingExampleRows (sharedOut j) = [0,sharedLeaf j] := by
  have value : sharedOut j = Fin.natAdd 2 (j.castAdd 10) := Fin.ext (by simp [sharedOut]; omega)
  rw [value, sharedClippingExampleRows, Fin.addCases_right, Fin.addCases_left]

private theorem shared_in_row (j : Fin 10) : sharedClippingExampleRows (sharedIn j) = [sharedLeaf j,0] := by
  have value : sharedIn j = Fin.natAdd 2 (Fin.natAdd 10 j) := Fin.ext (by simp [sharedIn]; omega)
  rw [value, sharedClippingExampleRows, Fin.addCases_right, Fin.addCases_right]

private def sharedSide (i : Fin 22) : Bool := decide (i.val < 2)

private def sharedRowsOn (side : Bool) (i : Fin 22) : List (Fin 57) :=
  if sharedSide i = side then sharedClippingExampleRows i else []

private theorem sharedSide_main : sharedSide 0 = true ∧ sharedSide 1 = true := by decide +kernel

private theorem sharedSide_out (j : Fin 10) : sharedSide (sharedOut j) = false := by
  simp [sharedSide, sharedOut]

private theorem sharedSide_in (j : Fin 10) : sharedSide (sharedIn j) = false := by
  simp [sharedSide, sharedIn]

private theorem shared_overlap {i j : Fin 22} {v : Fin 57}
    (apart : sharedSide i ≠ sharedSide j) (onI : v ∈ sharedClippingExampleRows i)
    (onJ : v ∈ sharedClippingExampleRows j) : v = 0 := by
  have main_vertices (r : Fin 22) (side : sharedSide r = true) (v : Fin 57)
      (on : v ∈ sharedClippingExampleRows r) : v.val < 15 := by
    have direct : ∀ w : Fin 57, w ∈ sharedClippingExampleRows 0 ∨ w ∈ sharedClippingExampleRows 1 →
        w.val < 15 := by decide +kernel
    rcases shared_row_cases r with rfl | rfl | ⟨z,rfl⟩ | ⟨z,rfl⟩
    · exact direct v (Or.inl on)
    · exact direct v (Or.inr on)
    · rw [sharedSide_out] at side
      contradiction
    · rw [sharedSide_in] at side
      contradiction
  have star_vertices (r : Fin 22) (side : sharedSide r = false) (v : Fin 57)
      (on : v ∈ sharedClippingExampleRows r) : v = 0 ∨ 15 ≤ v.val := by
    rcases shared_row_cases r with rfl | rfl | ⟨z,rfl⟩ | ⟨z,rfl⟩
    · rw [sharedSide_main.1] at side
      contradiction
    · rw [sharedSide_main.2] at side
      contradiction
    · rw [shared_out_row] at on
      rcases List.mem_cons.mp on with same | leaf
      · exact Or.inl same
      · obtain rfl := List.mem_singleton.mp leaf
        exact Or.inr (by simp [sharedLeaf])
    · rw [shared_in_row] at on
      rcases List.mem_cons.mp on with rfl | center
      · exact Or.inr (by simp [sharedLeaf])
      · exact Or.inl (List.mem_singleton.mp center)
  cases left : sharedSide i <;> cases right : sharedSide j
  · exact (apart (left.trans right.symm)).elim
  · rcases star_vertices i left v onI with center | leaf
    · exact center
    · exact ((main_vertices j right v onJ).not_ge leaf).elim
  · rcases star_vertices j right v onJ with center | leaf
    · exact center
    · exact ((main_vertices i left v onI).not_ge leaf).elim
  · exact (apart (left.trans right.symm)).elim

private theorem shared_only_main_steps {i : Fin 22} {x y : Fin 57}
    (on : BeforeIn (sharedRowsOn true) i x y) : (i = 0 ∧ x < y) ∨ (i = 1 ∧ y < x) := by
  have steps : (∀ a b, BeforeIn (sharedRowsOn true) 0 a b → a < b) ∧
      (∀ a b, BeforeIn (sharedRowsOn true) 1 a b → b < a) := by
    unfold BeforeIn
    decide +kernel
  rcases shared_row_cases i with rfl | rfl | ⟨z,rfl⟩ | ⟨z,rfl⟩
  · exact Or.inl ⟨rfl, steps.1 x y on⟩
  · exact Or.inr ⟨rfl, steps.2 x y on⟩
  · have impossible := on.1
    simp [sharedRowsOn,sharedSide_out] at impossible
  · have impossible := on.1
    simp [sharedRowsOn,sharedSide_in] at impossible

private theorem shared_main_free (cutoff : ℕ) : BridgeFree (BeforeIn (sharedRowsOn true)) cutoff := by
  intro j _
  refine ⟨fun b => ?_⟩
  rcases shared_only_main_steps b.riverStep with ⟨river, forward⟩ | ⟨river, backward⟩
  · have decreasing (s : Fin (j+2)) : b.vertex s ≤ b.vertex 0 := by
      induction s using Fin.induction with
      | zero => exact le_rfl
      | succ s ih =>
        rcases shared_only_main_steps (b.arcStep s) with ⟨arc, _⟩ | ⟨_, step⟩
        · exact (b.river_ne_arc s (river.trans arc.symm)).elim
        · exact step.le.trans ih
    exact forward.not_ge (decreasing _)
  · have increasing (s : Fin (j+2)) : b.vertex 0 ≤ b.vertex s := by
      induction s using Fin.induction with
      | zero => exact le_rfl
      | succ s ih =>
        rcases shared_only_main_steps (b.arcStep s) with ⟨_, step⟩ | ⟨arc, _⟩
        · exact ih.trans step.le
        · exact (b.river_ne_arc s (river.trans arc.symm)).elim
    exact backward.not_ge (increasing _)

private theorem pair_endpoints {I A : Type*} [DecidableEq A] {rows : I → List A}
    {i : I} {a b x y : A} (row : rows i = [a,b]) (distinct : a ≠ b)
    (on : BeforeIn rows i x y) : x = a ∧ y = b := by
  have hx : x ∈ [a,b] := row ▸ on.1
  have hy : y ∈ [a,b] := row ▸ on.2.1
  rcases List.mem_cons.mp hx with rfl | tail
  · rcases List.mem_cons.mp hy with rfl | last
    · exact (listBefore_ne on rfl).elim
    · exact ⟨rfl, List.mem_singleton.mp last⟩
  · obtain rfl := List.mem_singleton.mp tail
    rcases List.mem_cons.mp hy with rfl | last
    · have wrong := on.2.2
      rw [row] at wrong
      simp [distinct] at wrong
    · obtain rfl := List.mem_singleton.mp last
      exact (listBefore_ne on rfl).elim

private theorem sharedLeaf_ne_zero (j : Fin 10) : sharedLeaf j ≠ 0 := by
  intro same
  have values : j.val+15 = 0 := congrArg Fin.val same
  omega

private theorem shared_only_star_steps {i : Fin 22} {x y : Fin 57}
    (on : BeforeIn (sharedRowsOn false) i x y) :
    (∃ j, i = sharedOut j ∧ x = 0 ∧ y = sharedLeaf j) ∨
      (∃ j, i = sharedIn j ∧ x = sharedLeaf j ∧ y = 0) := by
  rcases shared_row_cases i with rfl | rfl | ⟨z,rfl⟩ | ⟨z,rfl⟩
  · have impossible := on.1
    simp [sharedRowsOn,sharedSide_main.1] at impossible
  · have impossible := on.1
    simp [sharedRowsOn,sharedSide_main.2] at impossible
  · have pair : sharedRowsOn false (sharedOut z) = [0,sharedLeaf z] := by
      simp [sharedRowsOn,sharedSide_out,shared_out_row]
    exact Or.inl ⟨z,rfl,pair_endpoints pair (sharedLeaf_ne_zero z).symm on⟩
  · have pair : sharedRowsOn false (sharedIn z) = [sharedLeaf z,0] := by
      simp [sharedRowsOn,sharedSide_in,shared_in_row]
    exact Or.inr ⟨z,rfl,pair_endpoints pair (sharedLeaf_ne_zero z) on⟩

private theorem shared_star_free (cutoff : ℕ) : BridgeFree (BeforeIn (sharedRowsOn false)) cutoff := by
  intro d _
  refine ⟨fun b => ?_⟩
  have leafInjective : Function.Injective sharedLeaf := by
    intro a c same
    have values := congrArg Fin.val same
    simp [sharedLeaf] at values
    exact Fin.ext values
  rcases shared_only_star_steps b.riverStep with ⟨leaf,river,_,endpoint⟩ | ⟨leaf,river,endpoint,_⟩
  · rcases shared_only_star_steps (b.arcStep (Fin.last d)) with ⟨other,last,_,ends⟩ | ⟨_,_,_,ends⟩
    · have same : leaf = other := leafInjective (endpoint.symm.trans ends)
      exact b.river_ne_arc (Fin.last d) (river.trans (same ▸ last.symm))
    · exact sharedLeaf_ne_zero leaf (endpoint.symm.trans ends)
  · rcases shared_only_star_steps (b.arcStep 0) with ⟨_,_,starts,_⟩ | ⟨other,first,starts,_⟩
    · exact sharedLeaf_ne_zero leaf (endpoint.symm.trans starts)
    · have same : leaf = other := leafInjective (endpoint.symm.trans starts)
      exact b.river_ne_arc 0 (river.trans (same ▸ first.symm))

/-- Each of the two row families excludes every full bridge. Their only
possible common vertex is the center. -/
theorem sharedClippingExample_fullFree (cutoff : ℕ) : BridgeFree (BeforeIn sharedClippingExampleRows) cutoff :=
  localOrderAdmissible_of_single_shared_vertex (half := false) sharedSide 0 (fun {_ _ _} => shared_overlap)
    (fun side => by
      cases side
      · exact shared_star_free cutoff
      · exact shared_main_free cutoff)

/-- The original widths are four for degrees and twelve for paths. -/
theorem sharedClippingExample_widths :
    let M := ∑ i, (sharedClippingExampleRows i).length
    M = 70 ∧ 4*M/57 = 4 ∧ 4*M/22 = 12 := by
  dsimp only
  rw [sharedClippingExample_mass_simple.1]
  decide

private def sharedExampleKeep (i : Fin 22) (v : Fin 57) : Bool :=
  if sharedSide i then decide (0 < v.val ∧ v.val ≤ 12)
  else decide (v ≠ 0 ∨ i = 2 ∨ i = 3 ∨ i = 12 ∨ i = 13)

private def sharedExampleKept (i : Fin 22) : List (Fin 57) :=
  (sharedClippingExampleRows i).filter (sharedExampleKeep i)

private theorem sharedExampleKept_caps :
    (∑ i, (sharedExampleKept i).length) = 48 ∧
    (∀ i, (sharedExampleKept i).length ≤ 12) ∧
    ∀ v, (occurrences (fun i => (sharedExampleKept i).toFinset) v).card ≤ 4 := by
  decide +kernel

private noncomputable def sharedExampleDeleted : Finset (Fin 22 × Fin 57) :=
  (pieceIncidences sharedClippingExampleRows univ).filter fun a => !sharedExampleKeep a.1 a.2

private theorem sharedExampleDeleted_subset :
    sharedExampleDeleted ⊆ pieceIncidences sharedClippingExampleRows univ :=
  filter_subset _ _

private theorem sharedExampleKept_incidence :
    pieceIncidences sharedExampleKept univ =
      pieceIncidences sharedClippingExampleRows univ \ sharedExampleDeleted := by
  ext a
  simp only [mem_pieceIncidences, mem_univ, true_and, mem_sdiff, sharedExampleDeleted, mem_filter,
    sharedExampleKept, List.mem_filter]
  cases flag : sharedExampleKeep a.1 a.2 <;> simp

private theorem sharedExampleDeleted_count : sharedExampleDeleted.card = 22 := by
  have simple (i : Fin 22) : (sharedExampleKept i).Nodup :=
    (sharedClippingExample_mass_simple.2 i).filter _
  have total := card_sdiff_add_card_eq_card sharedExampleDeleted_subset
  rw [← sharedExampleKept_incidence, pieceIncidences_card simple univ,
    pieceIncidences_card sharedClippingExample_mass_simple.2 univ,
    sharedExampleKept_caps.1, sharedClippingExample_mass_simple.1] at total
  omega

private theorem sharedExampleKept_degree_class (k : ℕ) (c : Fin 57 × Fin 22) :
    ((pieceIncidences sharedExampleKept univ).filter
      (fun a => shortReturnDegreeClass sharedClippingExampleRows k a = c)).card ≤ 4 := by
  obtain ⟨v, label⟩ := c
  rw [shortReturnDegreeClass_card]
  exact (card_le_card (filter_subset _ _)).trans (sharedExampleKept_caps.2.2 v)

private theorem sharedExampleKept_path_class (k : ℕ) (c : Fin 22 × Fin 57) :
    ((pieceIncidences sharedExampleKept univ).filter
      (fun a => shortReturnPathClass sharedClippingExampleRows k a = c)).card ≤ 12 := by
  obtain ⟨i, label⟩ := c
  have simple : (sharedExampleKept i).Nodup := (sharedClippingExample_mass_simple.2 i).filter _
  rw [shortReturnPathClass_card]
  exact (card_le_card (filter_subset _ _)).trans
    ((List.toFinset_card_of_nodup simple).trans_le (sharedExampleKept_caps.2.1 i))

/-- The 22 deletions fit both sets of fixed classes at any cutoff. The
exact criterion converts them into a shared set at deletion budget 22. -/
theorem sharedClippingExample_has_shared_deletions (cutoff : ℕ) :
    ∃ shared : Finset (Fin 22 × Fin 57),
      ShortReturnSharedDeletion sharedClippingExampleRows 4 12 cutoff shared ∧
      shortReturnDegreeExcessMass sharedClippingExampleRows 4 cutoff +
        shortReturnPathExcessMass sharedClippingExampleRows 12 cutoff ≤ 22 + shared.card := by
  obtain ⟨shared, within, paid, degree, path⟩ :=
    (FiberClipping.exists_capped_deletion_iff (pieceIncidences sharedClippingExampleRows univ)
      (shortReturnDegreeClass sharedClippingExampleRows cutoff)
      (shortReturnPathClass sharedClippingExampleRows cutoff) 4 12 22).mp
      ⟨sharedExampleDeleted, sharedExampleDeleted_subset, sharedExampleDeleted_count.le,
        fun c => sharedExampleKept_incidence ▸ sharedExampleKept_degree_class cutoff c,
        fun c => sharedExampleKept_incidence ▸ sharedExampleKept_path_class cutoff c⟩
  refine ⟨shared, ⟨within, degree, path⟩, ?_⟩
  rw [shortReturnDegreeClass_totalExcess, shortReturnPathClass_totalExcess] at paid
  exact paid

/-- The shared certificate gives a frozen full witness at any cutoff. -/
theorem sharedClippingExample_full_frozen (cutoff : ℕ) :
    ∃ n' ≤ 57, ∃ p' ≤ 22, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (BeforeIn clean) cutoff ∧
      70 ≤ 18*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ 70 ∧ frozenListCaps 57 22 70 clean := by
  have mass := sharedClippingExample_mass_simple.1
  have dense : 57 ≤ ∑ i, (sharedClippingExampleRows i).length := by rw [mass]; decide
  have long : 22 ≤ ∑ i, (sharedClippingExampleRows i).length := by rw [mass]; decide
  obtain ⟨shared, fits, paid⟩ := sharedClippingExample_has_shared_deletions cutoff
  have result := regularization_list_frozen_of_shared_short_return_deletions (half := false)
    sharedClippingExampleRows sharedClippingExample_mass_simple.2 (sharedClippingExample_fullFree cutoff)
    (by decide) (by decide) dense long shared
    (by dsimp only; rw [mass, show 4*70/57 = 4 by decide, show 4*70/22 = 12 by decide]; exact fits)
    (by
      dsimp only
      rw [mass, show 4*70/57 = 4 by decide, show 4*70/22 = 12 by decide]
      exact paid.trans (Nat.add_le_add_right (by decide : 22 ≤ 70/3) _))
  simpa only [mass, localOrderAdmissible, Bool.false_eq_true, ite_false] using result

private def sharedCenterNeighbor (i : Fin 22) : Fin 57 :=
  if i.val < 2 then 1
  else if i.val < 12 then ⟨i.val+13, by have := i.isLt; omega⟩
  else ⟨i.val+3, by have := i.isLt; omega⟩

private def sharedCenterMate (i : Fin 22) : Fin 22 :=
  if i = 0 then 1
  else if i = 1 then 0
  else if h : i.val < 12 then ⟨i.val+10, by omega⟩
  else ⟨i.val-10, by have := i.isLt; omega⟩

private theorem shared_center_steps (i : Fin 22) :
    let x := sharedCenterNeighbor i
    let mate := sharedCenterMate i
    (i ≠ 1 ∧ BeforeIn sharedClippingExampleRows i 0 x ∧ BeforeIn sharedClippingExampleRows mate x 0) ∨
      (i ≠ 0 ∧ BeforeIn sharedClippingExampleRows i x 0 ∧ BeforeIn sharedClippingExampleRows mate 0 x) := by
  revert i
  unfold BeforeIn
  decide +kernel

private theorem shared_center_spine_steps :
    BeforeIn sharedClippingExampleRows 0 0 1 ∧ BeforeIn sharedClippingExampleRows 1 1 0 := by
  unfold BeforeIn
  decide +kernel

private theorem joint_row_components {I V : Type*} [Fintype I] [Fintype V] [DecidableEq I] [LinearOrder V]
    {rows : I → List V} {i j vIn vOut : I} {v x y : V}
    (apart : i ≠ j) (starts : BeforeIn rows i v x) (ends : BeforeIn rows j y v)
    (back : BeforeIn rows vIn x v) (forward : BeforeIn rows vOut v y) :
    SameComponent (shortReturnCopyRowGraph rows 7 v) i j := by
  let G := listPiecePrecedenceGraph rows
  have enter : Edge G x v := listPiecePrecedenceGraph_edge.mpr ⟨vIn, back⟩
  have leave : Edge G v y := listPiecePrecedenceGraph_edge.mpr ⟨vOut, forward⟩
  have last : v ∈ reachIn G y 2 :=
    (reachIn_succ (G := G) (k := 1)).mpr (Or.inr ⟨y, leave, target_mem_reachIn G y 1⟩)
  have route : x ∈ reachIn G y 3 :=
    (reachIn_succ (G := G) (k := 2)).mpr (Or.inr ⟨v, enter, last⟩)
  have linked : ShortReturnCopyRowPair rows 7 v i j := ⟨apart, x, y, starts, ends, route⟩
  exact ⟨.single (shortReturnCopyRowGraph_edge.mpr (Or.inl linked)),
    .single (shortReturnCopyRowGraph_edge.mpr (Or.inr linked))⟩

private theorem shared_center_connected (i : Fin 22) :
    SameComponent (shortReturnCopyRowGraph sharedClippingExampleRows 7 0) i 0 := by
  have first := shared_center_spine_steps.1
  have last := shared_center_spine_steps.2
  have pair := joint_row_components (by decide : (0 : Fin 22) ≠ 1) first last last first
  rcases shared_center_steps i with ⟨apart, start, back⟩ | ⟨apart, finish, forward⟩
  · exact (joint_row_components apart start last back first).trans pair.symm
  · exact (joint_row_components apart.symm first finish last forward).symm

private def sharedCenterDegreeClass : Fin 57 × Fin 22 :=
  (0, componentLabel (shortReturnCopyRowGraph sharedClippingExampleRows 7 0) 0)

private theorem shared_center_degree_class_card :
    ((pieceIncidences sharedClippingExampleRows univ).filter
      fun a => shortReturnDegreeClass sharedClippingExampleRows 7 a = sharedCenterDegreeClass).card = 22 := by
  rw [sharedCenterDegreeClass, shortReturnDegreeClass_card]
  have all : (occurrences (fun i => (sharedClippingExampleRows i).toFinset) 0).filter
      (fun i => componentLabel (shortReturnCopyRowGraph sharedClippingExampleRows 7 0) i =
        componentLabel (shortReturnCopyRowGraph sharedClippingExampleRows 7 0) 0) = univ := by
    ext i
    simp only [mem_filter, mem_univ, iff_true]
    have occurs : (0 : Fin 57) ∈ sharedClippingExampleRows i := by
      rcases shared_center_steps i with ⟨_, on, _⟩ | ⟨_, on, _⟩
      · exact on.1
      · exact on.2.1
    exact ⟨mem_occurrences.mpr (List.mem_toFinset.mpr occurs),
      componentLabel_eq.mpr (shared_center_connected i)⟩
  rw [all, card_univ, Fintype.card_fin]

private theorem shared_spine_reverse_at_center :
    ∀ v : Fin 57, v ∈ sharedClippingExampleRows 0 → v ≠ 0 →
      BeforeIn sharedClippingExampleRows 0 0 v ∧ BeforeIn sharedClippingExampleRows 1 v 0 := by
  unfold BeforeIn
  decide +kernel

private theorem shared_spine_same_vertices :
    (sharedClippingExampleRows 1).toFinset = (sharedClippingExampleRows 0).toFinset := by
  decide +kernel

private theorem path_component_of_opposite_step {I V : Type*} [Fintype I] [Fintype V] [LinearOrder V]
    {rows : I → List V} {i j : I} {x y : V}
    (forward : BeforeIn rows i x y) (back : BeforeIn rows j y x) :
    SameComponent (shortReturnRowGraph rows 7 i) x y := by
  let G := listPiecePrecedenceGraph rows
  have edge : Edge G y x := listPiecePrecedenceGraph_edge.mpr ⟨j, back⟩
  have path : y ∈ reachIn G x 4 :=
    (reachIn_succ (G := G) (t := x) (u := y) (k := 3)).mpr
      (Or.inr ⟨x, edge, target_mem_reachIn G x 3⟩)
  exact ⟨.single (shortReturnRowGraph_edge.mpr (Or.inl ⟨forward,path⟩)),
    .single (shortReturnRowGraph_edge.mpr (Or.inr ⟨forward,path⟩))⟩

private def sharedSpinePathClass (i : Fin 22) : Fin 22 × Fin 57 :=
  (i, componentLabel (shortReturnRowGraph sharedClippingExampleRows 7 i) 0)

private theorem shared_spine_path_class_card (i : Fin 22) (spine : i = 0 ∨ i = 1) :
    ((pieceIncidences sharedClippingExampleRows univ).filter
      fun a => shortReturnPathClass sharedClippingExampleRows 7 a = sharedSpinePathClass i).card = 15 := by
  rw [sharedSpinePathClass, shortReturnPathClass_card]
  have all : ((sharedClippingExampleRows i).toFinset.filter
      (fun v => componentLabel (shortReturnRowGraph sharedClippingExampleRows 7 i) v =
        componentLabel (shortReturnRowGraph sharedClippingExampleRows 7 i) 0)) =
      (sharedClippingExampleRows i).toFinset := by
    ext x
    refine ⟨fun on => (mem_filter.mp on).1, fun on => ?_⟩
    refine mem_filter.mpr ⟨on, ?_⟩
    by_cases center : x = 0
    · subst x
      rfl
    have onFirst : x ∈ (sharedClippingExampleRows 0).toFinset := by
      rcases spine with rfl | rfl
      · exact on
      · exact shared_spine_same_vertices ▸ on
    obtain ⟨forward,backward⟩ := shared_spine_reverse_at_center x (List.mem_toFinset.mp onFirst) center
    apply componentLabel_eq.mpr
    rcases spine with rfl | rfl
    · exact (path_component_of_opposite_step forward backward).symm
    · exact path_component_of_opposite_step backward forward
  rw [all]
  rcases spine with rfl | rfl <;> decide +kernel

private theorem fiber_excess_le_total {A B : Type*}
    [DecidableEq A] [DecidableEq B] [Fintype B]
    (items : Finset A) (label : A → B) (width : ℕ) (c : B) :
    FiberClipping.excess items label width c ≤ FiberClipping.totalExcess items label width :=
  single_le_sum (f := FiberClipping.excess items label width)
    (fun _ _ => Nat.zero_le _) (mem_univ c)

/-- Charging the two original excesses separately exceeds the one-third
budget at cutoff seven, while the shared certificate pays within it. -/
theorem sharedClippingExample_separate_excess :
    70/3 < shortReturnDegreeExcessMass sharedClippingExampleRows 4 7 +
      shortReturnPathExcessMass sharedClippingExampleRows 12 7 := by
  let items := pieceIncidences sharedClippingExampleRows univ
  let degree := shortReturnDegreeClass sharedClippingExampleRows 7
  let path := shortReturnPathClass sharedClippingExampleRows 7
  have degreePaid : FiberClipping.excess items degree 4 sharedCenterDegreeClass = 18 := by
    unfold FiberClipping.excess
    rw [shared_center_degree_class_card]
  have pathPaid (i : Fin 22) (which : i = 0 ∨ i = 1) :
      FiberClipping.excess items path 12 (sharedSpinePathClass i) = 3 := by
    unfold FiberClipping.excess
    rw [shared_spine_path_class_card i which]
  have degreeBound : 18 ≤ FiberClipping.totalExcess items degree 4 := by
    rw [← degreePaid]
    exact fiber_excess_le_total items degree 4 sharedCenterDegreeClass
  have pathBound : 6 ≤ FiberClipping.totalExcess items path 12 := calc
    _ = FiberClipping.excess items path 12 (sharedSpinePathClass 0) +
        FiberClipping.excess items path 12 (sharedSpinePathClass 1) := by
          rw [pathPaid 0 (.inl rfl), pathPaid 1 (.inr rfl)]
    _ = ∑ c ∈ ({sharedSpinePathClass 0, sharedSpinePathClass 1} : Finset (Fin 22 × Fin 57)),
        FiberClipping.excess items path 12 c := by
          rw [sum_pair (show sharedSpinePathClass 0 ≠ sharedSpinePathClass 1 from
            fun eq => (by decide : (0 : Fin 22) ≠ 1) (congrArg Prod.fst eq))]
    _ ≤ _ := sum_le_sum_of_subset (subset_univ _)
  rw [shortReturnDegreeClass_totalExcess] at degreeBound
  rw [shortReturnPathClass_totalExcess] at pathBound
  exact (by decide : 70/3 < 18+6).trans_le (Nat.add_le_add degreeBound pathBound)

end OnlineReachabilityPreservers.SourceAudit
