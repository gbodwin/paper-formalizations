import OnlineReachabilityPreservers.LiteralFullBridgeBudget

/-! The two exact-count conventions have different feasible budgets. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset

private abbrev Vertex := Fin 4

/-- Four singleton paths followed by seven directed comparisons. -/
def fourVertexElevenHalfRows : Fin 11 → List Vertex :=
  ![[0],[1],[2],[3],[0,1],[0,2],[0,3],[1,2],[1,3],[2,1],[3,1]]

private local instance decidableBefore {V I : Type*} [DecidableEq V]
    (rows : I → List V) (i : I) (x y : V) : Decidable (BeforeIn rows i x y) := by
  unfold BeforeIn
  infer_instance

private def halfDartOwner (x y : Vertex) : Option (Fin 11) :=
  (List.finRange 11).find? fun i => decide (BeforeIn fourVertexElevenHalfRows i x y)

private theorem halfDartOwner_exact :
    ∀ (i : Fin 11) (x y : Vertex), BeforeIn fourVertexElevenHalfRows i x y → halfDartOwner x y = some i := by
  decide +kernel

private theorem halfDartRoles :
    ∀ (i : Fin 11) (x y : Vertex), BeforeIn fourVertexElevenHalfRows i x y →
      y ≠ 0 ∧ (x = 0 → i.val ≤ 6) ∧ (x ≠ 0 → 7 ≤ i.val ∧ (x = 1 ∨ y = 1)) := by
  decide +kernel

/-- The eleven distinct nonempty rows exclude half-bridges of every size.
Vertex zero points into a bidirectional star, and no row enters vertex zero. -/
theorem fourVertexElevenHalfRows_spec :
    Function.Injective fourVertexElevenHalfRows ∧
      (∀ i, fourVertexElevenHalfRows i ≠ [] ∧ (fourVertexElevenHalfRows i).Nodup) ∧
      ∀ cutoff, HalfBridgeFree (BeforeIn fourVertexElevenHalfRows) cutoff := by
  refine ⟨by decide,by decide,?_⟩
  intro cutoff s _ bridge earlier
  cases s with
  | zero =>
    have river := halfDartOwner_exact _ _ _ bridge.riverStep
    have arc := halfDartOwner_exact _ _ _ (bridge.arcStep 0)
    exact bridge.river_ne_arc 0 (Option.some.inj (river.symm.trans arc))
  | succ s =>
    let last : Fin (s+2) := Fin.last (s+1)
    let previous : Fin (s+2) := (Fin.last s).castSucc
    have sameCorner : previous.succ = last.castSucc := Fin.ext rfl
    have lastStartsInStar : bridge.vertex last.castSucc ≠ 0 := by
      rw [← sameCorner]
      exact (halfDartRoles _ _ _ (bridge.arcStep previous)).1
    have lastRoles := (halfDartRoles _ _ _ (bridge.arcStep last)).2.2 lastStartsInStar
    have lastEnd : last.succ = Fin.last (s+2) := Fin.succ_last _
    have riverRoles := halfDartRoles _ _ _ bridge.riverStep
    by_cases startsAtSource : bridge.vertex 0 = 0
    · have riverEarly := riverRoles.2.1 startsAtSource
      change (bridge.arc last).val < bridge.river.val at earlier
      omega
    · rcases (riverRoles.2.2 startsAtSource).2 with startRoot | stopRoot
      · have lastNotRoot : bridge.vertex last.succ ≠ 1 := by
          rw [lastEnd]
          exact fun equal => listBefore_ne bridge.riverStep (startRoot.trans equal.symm)
        have lastRoot := lastRoles.2.resolve_right lastNotRoot
        have same := bridge.distinctVertices (startRoot.trans lastRoot.symm)
        have zero := congrArg Fin.val same
        change 0 = s+1 at zero
        omega
      · have startNotRoot : bridge.vertex 0 ≠ 1 :=
          fun eq => listBefore_ne bridge.riverStep (eq.trans stopRoot.symm)
        have firstRoles := (halfDartRoles _ _ _ (bridge.arcStep 0)).2.2 startsAtSource
        have firstRoot := firstRoles.2.resolve_left startNotRoot
        have same := bridge.distinctVertices (firstRoot.trans stopRoot.symm)
        have zero := congrArg Fin.val same
        change 1 = s+2 at zero
        omega

private def allDarts : Finset (Vertex × Vertex) := (univ : Finset Vertex).offDiag

private def SmallDartDetour (edges : Finset (Vertex × Vertex)) (s : ℕ) : Prop :=
  ∃ v : Fin (s+2) → Vertex, Function.Injective v ∧ (v 0,v (Fin.last (s+1))) ∈ edges ∧
    ∀ i : Fin (s+1), (v i.castSucc,v i.succ) ∈ edges

private theorem three_dart_detour {edges : Finset (Vertex × Vertex)} {x y z : Vertex}
    (xy : x ≠ y) (xz : x ≠ z) (yz : y ≠ z)
    (river : (x,z) ∈ edges) (first : (x,y) ∈ edges) (last : (y,z) ∈ edges) :
    SmallDartDetour edges 1 := by
  let v : Fin 3 → Vertex := ![x,y,z]
  refine ⟨v,?_,river,?_⟩
  · intro i j equal
    fin_cases i <;> fin_cases j <;> simp [v] at equal ⊢ <;> aesop
  · intro i
    fin_cases i
    · exact first
    · exact last

private theorem four_dart_detour {edges : Finset (Vertex × Vertex)} {x y z w : Vertex}
    (xy : x ≠ y) (xz : x ≠ z) (xw : x ≠ w) (yz : y ≠ z) (yw : y ≠ w) (zw : z ≠ w)
    (river : (x,w) ∈ edges) (first : (x,y) ∈ edges) (middle : (y,z) ∈ edges)
    (last : (z,w) ∈ edges) : SmallDartDetour edges 2 := by
  let v : Fin 4 → Vertex := ![x,y,z,w]
  refine ⟨v,?_,river,?_⟩
  · intro i j equal
    fin_cases i <;> fin_cases j <;> simp [v] at equal ⊢ <;> aesop
  · intro i
    fin_cases i
    · exact first
    · exact middle
    · exact last

private def reciprocalSeed : Finset (Vertex × Vertex) := {(0,1),(1,0)}

/-- Contract the reciprocal pair to the first of three vertices. -/
private def collapse : Vertex → Fin 3 := ![0,0,1,2]

private def collapseDart (edge : Vertex × Vertex) : Fin 3 × Fin 3 :=
  (collapse edge.1,collapse edge.2)

private theorem collapse_dart_collision :
    ∀ a b : Vertex × Vertex, a ∈ allDarts \ reciprocalSeed → b ∈ allDarts \ reciprocalSeed →
      a ≠ b → collapseDart a = collapseDart b →
      (a.1,b.1) ∈ reciprocalSeed ∧ a.2 = b.2 ∨ a.1 = b.1 ∧ (a.2,b.2) ∈ reciprocalSeed := by
  decide +kernel

private theorem collapse_nonseed_offdiag :
    ∀ e : Vertex × Vertex, e ∈ allDarts \ reciprocalSeed → (collapseDart e).1 ≠ (collapseDart e).2 := by
  decide +kernel

private theorem collapse_on_two : ∀ v : Vertex, collapse v = 1 ↔ v = 2 := by decide +kernel
private theorem collapse_on_three : ∀ v : Vertex, collapse v = 2 ↔ v = 3 := by decide +kernel

private theorem collapse_on_pair : ∀ v : Vertex, collapse v = 0 → v ≠ 2 ∧ v ≠ 3 := by
  decide +kernel

private theorem collapse_between_pair :
    ∀ x y : Vertex, collapse x = 0 → collapse y = 0 → x ≠ y → (x,y) ∈ reciprocalSeed := by
  decide +kernel

/-- Each of the two opposite linear orders uses a disjoint triple of
arcs. Omitting at most one arc leaves all three arcs of one order. -/
private theorem five_collapsed_darts_triple {edges : Finset (Fin 3 × Fin 3)}
    (allowed : edges ⊆ (univ : Finset (Fin 3)).offDiag) (five : edges.card = 5) :
    ((0,1) ∈ edges ∧ (0,2) ∈ edges ∧ (1,2) ∈ edges) ∨
      ((2,1) ∈ edges ∧ (2,0) ∈ edges ∧ (1,0) ∈ edges) := by
  let all := (univ : Finset (Fin 3)).offDiag
  let forward : Finset (Fin 3 × Fin 3) := {(0,1),(0,2),(1,2)}
  let reverse : Finset (Fin 3 × Fin 3) := {(2,1),(2,0),(1,0)}
  have six : all.card = 6 := by decide +kernel
  have opposed : Disjoint forward reverse := by decide +kernel
  have forwardAllowed : forward ⊆ all := by decide +kernel
  have reverseAllowed : reverse ⊆ all := by decide +kernel
  have missing := card_sdiff_add_card_eq_card allowed
  change (all \ edges).card + edges.card = all.card at missing
  have aTriple : forward ⊆ edges ∨ reverse ⊆ edges := by
    by_contra fail
    obtain ⟨a,af,na⟩ := not_subset.mp (fun h => fail (Or.inl h))
    obtain ⟨b,br,nb⟩ := not_subset.mp (fun h => fail (Or.inr h))
    have different : a ≠ b := fun equal => disjoint_left.mp opposed af (equal.symm ▸ br)
    have absent : ({a,b} : Finset (Fin 3 × Fin 3)) ⊆ all \ edges := by
      simp only [insert_subset_iff,singleton_subset_iff]
      exact ⟨mem_sdiff.mpr ⟨forwardAllowed af,na⟩,mem_sdiff.mpr ⟨reverseAllowed br,nb⟩⟩
    have bound := card_le_card absent
    rw [card_pair different] at bound
    omega
  simpa only [forward,reverse,insert_subset_iff,singleton_subset_iff] using aTriple

/-- With the reciprocal pair present, seven arcs force a directed
shortcut. If contraction merged two other arcs, those arcs and one
reciprocal step already give a three-vertex witness. -/
private theorem seven_darts_with_seed {edges : Finset (Vertex × Vertex)}
    (allowed : edges ⊆ allDarts) (seven : edges.card = 7) (seed : reciprocalSeed ⊆ edges) :
    SmallDartDetour edges 1 ∨ SmallDartDetour edges 2 := by
  by_cases triangle : SmallDartDetour edges 1
  · exact Or.inl triangle
  let outside := edges \ reciprocalSeed
  have outside_allowed : outside ⊆ allDarts \ reciprocalSeed := by
    intro edge found
    obtain ⟨yes,no⟩ := mem_sdiff.mp found
    exact mem_sdiff.mpr ⟨allowed yes,no⟩
  have outside_inj : Set.InjOn collapseDart (outside : Set (Vertex × Vertex)) := by
    rintro ⟨a,b⟩ ha ⟨c,d⟩ hc equal
    by_contra different
    have ab := mem_sdiff.mp ha |>.1
    have cd := mem_sdiff.mp hc |>.1
    have ab_ne := (mem_offDiag.mp (allowed ab)).2.2
    have cd_ne := (mem_offDiag.mp (allowed cd)).2.2
    rcases collapse_dart_collision (a,b) (c,d) (outside_allowed ha) (outside_allowed hc) different equal
      with ⟨ac,same⟩ | ⟨same,bd⟩
    · change b = d at same
      subst d
      have acEdge := seed ac
      exact triangle (three_dart_detour (mem_offDiag.mp (allowed acEdge)).2.2 ab_ne cd_ne ab acEdge cd)
    · change a = c at same
      subst c
      have bdEdge := seed bd
      exact triangle (three_dart_detour ab_ne cd_ne (mem_offDiag.mp (allowed bdEdge)).2.2 cd ab bdEdge)
  let collapsed := outside.image collapseDart
  have count := card_sdiff_add_card_eq_card seed
  change outside.card + reciprocalSeed.card = edges.card at count
  have pair : reciprocalSeed.card = 2 := by decide +kernel
  have five : collapsed.card = 5 := by
    rw [card_image_of_injOn outside_inj]
    omega
  have collapsedAllowed : collapsed ⊆ (univ : Finset (Fin 3)).offDiag := by
    intro e visible
    obtain ⟨edge,found,rfl⟩ := mem_image.mp visible
    exact mem_offDiag.mpr ⟨mem_univ _,mem_univ _,collapse_nonseed_offdiag edge (outside_allowed found)⟩
  have lift {x y : Fin 3} (visible : (x,y) ∈ collapsed) :
      ∃ a b : Vertex, collapse a = x ∧ collapse b = y ∧ (a,b) ∈ edges := by
    obtain ⟨⟨a,b⟩,found,equal⟩ := mem_image.mp visible
    exact ⟨a,b,congrArg Prod.fst equal,congrArg Prod.snd equal,(mem_sdiff.mp found).1⟩
  rcases five_collapsed_darts_triple collapsedAllowed five with ⟨first,river,last⟩ | ⟨first,river,last⟩
  · obtain ⟨a,b,ha,hb,first⟩ := lift first
    obtain ⟨c,d,hc,hd,river⟩ := lift river
    obtain ⟨e,f,he,hf,last⟩ := lift last
    rcases collapse_on_two b |>.mp hb with rfl
    rcases collapse_on_three d |>.mp hd with rfl
    rcases collapse_on_two e |>.mp he with rfl
    rcases collapse_on_three f |>.mp hf with rfl
    have an := collapse_on_pair a ha
    have cn := collapse_on_pair c hc
    by_cases same : c = a
    · subst c
      exact (triangle (three_dart_detour an.1 an.2 (by decide) river first last)).elim
    · exact Or.inr (four_dart_detour same cn.1 cn.2 an.1 an.2 (by decide) river
        (seed (collapse_between_pair c a hc ha same)) first last)
  · obtain ⟨a,b,ha,hb,first⟩ := lift first
    obtain ⟨c,d,hc,hd,river⟩ := lift river
    obtain ⟨e,f,he,hf,last⟩ := lift last
    rcases collapse_on_three a |>.mp ha with rfl
    rcases collapse_on_two b |>.mp hb with rfl
    rcases collapse_on_three c |>.mp hc with rfl
    rcases collapse_on_two e |>.mp he with rfl
    have fn := collapse_on_pair f hf
    have dn := collapse_on_pair d hd
    by_cases same : f = d
    · subst f
      exact (triangle (three_dart_detour (by decide) dn.2.symm dn.1.symm river first last)).elim
    · exact Or.inr (four_dart_detour (by decide) fn.2.symm dn.2.symm fn.1.symm dn.1.symm same
        river first last (seed (collapse_between_pair f d hf hd same)))

private theorem sevenDarts_have_reciprocal {edges : Finset (Vertex × Vertex)}
    (allowed : edges ⊆ allDarts) (seven : edges.card = 7) :
    ∃ x y : Vertex, x ≠ y ∧ (x,y) ∈ edges ∧ (y,x) ∈ edges := by
  by_contra missing
  let ordered := (univ : Finset (Vertex × Vertex)).filter fun edge => edge.1 < edge.2
  let sort (edge : Vertex × Vertex) := (min edge.1 edge.2,max edge.1 edge.2)
  have targetSize : ordered.card = 6 := by decide +kernel
  have different (edge : Vertex × Vertex) (on : edge ∈ edges) : edge.1 ≠ edge.2 :=
    (mem_offDiag.mp (allowed on)).2.2
  have onTarget (edge : Vertex × Vertex) (on : edge ∈ edges) : sort edge ∈ ordered := by
    rcases edge with ⟨x,y⟩
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    rcases lt_or_gt_of_ne (different _ on) with xy | yx
    · simpa only [sort,min_eq_left xy.le,max_eq_right xy.le] using xy
    · simpa only [sort,min_eq_right yx.le,max_eq_left yx.le] using yx
  have injective : Set.InjOn sort (edges : Set (Vertex × Vertex)) := by
    rintro ⟨x,y⟩ onX ⟨u,v⟩ onU equal
    rcases lt_or_gt_of_ne (different _ onX) with xy | yx <;>
      rcases lt_or_gt_of_ne (different _ onU) with uv | vu
    · simpa only [sort,min_eq_left xy.le,max_eq_right xy.le,min_eq_left uv.le,max_eq_right uv.le] using equal
    · have reverse : (x,y) = (v,u) := by
        simpa only [sort,min_eq_left xy.le,max_eq_right xy.le,min_eq_right vu.le,max_eq_left vu.le] using equal
      obtain ⟨a,b⟩ := Prod.mk.inj reverse
      subst v
      subst u
      exact (missing ⟨x,y,xy.ne,onX,onU⟩).elim
    · have reverse : (y,x) = (u,v) := by
        simpa only [sort,min_eq_right yx.le,max_eq_left yx.le,min_eq_left uv.le,max_eq_right uv.le] using equal
      obtain ⟨a,b⟩ := Prod.mk.inj reverse
      subst u
      subst v
      exact (missing ⟨x,y,yx.ne.symm,onX,onU⟩).elim
    · have swapped : (y,x) = (v,u) := by
        simpa only [sort,min_eq_right yx.le,max_eq_left yx.le,min_eq_right vu.le,max_eq_left vu.le] using equal
      exact congrArg Prod.swap swapped
  have le := card_le_card_of_injOn sort onTarget injective
  omega

set_option maxRecDepth 8192 in
private theorem twoLabels_to_zero_one :
    ∀ x y : Vertex, x ≠ y → ∃ perm : Vertex ≃ Vertex, perm x = 0 ∧ perm y = 1 := by
  decide +kernel

private theorem small_dart_detour_unmap (perm : Vertex ≃ Vertex)
    {edges : Finset (Vertex × Vertex)} {s : ℕ}
    (detour : SmallDartDetour (edges.map (perm.prodCongr perm).toEmbedding) s) :
    SmallDartDetour edges s := by
  obtain ⟨v,injective,river,steps⟩ := detour
  have member {x y : Vertex} (on : (x,y) ∈ edges.map (perm.prodCongr perm).toEmbedding) :
      (perm.symm x,perm.symm y) ∈ edges := by
    obtain ⟨a,onA,equal⟩ := mem_map.mp on
    have label := congrArg (perm.prodCongr perm).symm equal
    change (perm.prodCongr perm).symm ((perm.prodCongr perm) a) = _ at label
    rw [Equiv.symm_apply_apply] at label
    change a = (perm.symm x,perm.symm y) at label
    simpa only [← label] using onA
  exact ⟨perm.symm ∘ v,perm.symm.injective.comp injective,member river,fun i => member (steps i)⟩

private theorem sevenDarts_have_detour {edges : Finset (Vertex × Vertex)}
    (off : edges ⊆ allDarts) (seven : edges.card = 7) :
    SmallDartDetour edges 1 ∨ SmallDartDetour edges 2 := by
  obtain ⟨x,y,apart,xy,yx⟩ := sevenDarts_have_reciprocal off seven
  obtain ⟨perm,zero,one⟩ := twoLabels_to_zero_one x y apart
  let mapped := edges.map (perm.prodCongr perm).toEmbedding
  have mappedOff : mapped ⊆ allDarts := by
    intro edge on
    obtain ⟨⟨a,b⟩,old,rfl⟩ := mem_map.mp on
    exact mem_offDiag.mpr ⟨mem_univ _,mem_univ _,
      fun equal => (mem_offDiag.mp (off old)).2.2 (perm.injective equal)⟩
  have includes : reciprocalSeed ⊆ mapped := by
    intro edge on
    simp only [reciprocalSeed,mem_insert,mem_singleton] at on
    rcases on with rfl | rfl
    · exact mem_map.mpr ⟨(x,y),xy,Prod.ext zero one⟩
    · exact mem_map.mpr ⟨(y,x),yx,Prod.ext one zero⟩
  have mappedSize : mapped.card = 7 := (card_map _).trans seven
  exact (seven_darts_with_seed mappedOff mappedSize includes).imp
    (small_dart_detour_unmap perm) (small_dart_detour_unmap perm)

/-- A full-free literal family on four vertices has at most four
singleton rows and at most six longer rows through cutoff four. -/
theorem fourVertex_literal_full_path_count_le_ten {p cutoff : ℕ}
    (paths : Fin p → List (Fin 4)) (distinct : Function.Injective paths)
    (nonempty : ∀ i, paths i ≠ []) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (BeforeIn paths) cutoff) (large : 4 ≤ cutoff) : p ≤ 10 := by
  classical
  let long := (univ : Finset (Fin p)).filter fun i => 2 ≤ (paths i).length
  let short := (univ : Finset (Fin p)).filter fun i => ¬ 2 ≤ (paths i).length
  let head (i : short) : Vertex := (paths i.val)[0]'(List.length_pos_iff.mpr (nonempty i.val))
  have singleton (i : short) : paths i.val = [head i] := by
    have enough := List.length_pos_iff.mpr (nonempty i.val)
    have small := (mem_filter.mp i.property).2
    obtain ⟨x,equal⟩ := List.length_eq_one_iff.mp (by omega : (paths i.val).length = 1)
    have label : head i = x := by
      unfold head
      rw [List.getElem_of_eq equal]
      rfl
    rw [label]
    exact equal
  have headInjective : Function.Injective head := by
    intro i j same
    exact Subtype.ext (distinct ((singleton i).trans ((congrArg (fun x => [x]) same).trans (singleton j).symm)))
  have shortCount : short.card ≤ 4 := by
    simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective head headInjective
  have counts : long.card+short.card = p := by
    simpa only [long,short,card_univ,Fintype.card_fin] using
      card_filter_add_card_filter_not (s := (univ : Finset (Fin p))) (fun i => 2 ≤ (paths i).length)
  have lengths (i : long) : 2 ≤ (paths i.val).length := (mem_filter.mp i.property).2
  let dart (i : long) : Vertex × Vertex :=
    ((paths i.val)[0]'(by have := lengths i; omega),(paths i.val)[1]'(by have := lengths i; omega))
  have step (i : long) : BeforeIn paths i.val (dart i).1 (dart i).2 := by
    refine ⟨List.getElem_mem _,List.getElem_mem _,?_⟩
    dsimp only [dart]
    rw [(simple i.val).idxOf_getElem,(simple i.val).idxOf_getElem]
    decide
  have dartInjective : Function.Injective dart := by
    intro i j same
    by_contra apart
    have parallel := step j
    rw [← same] at parallel
    exact no_parallel_list_steps free.halfFree (by omega)
      (fun equal => apart (Subtype.ext equal)) (step i) parallel
  let darts := long.attach.image dart
  have dartCount : darts.card = long.card := by
    rw [card_image_of_injective _ dartInjective,card_attach]
  have inside : darts ⊆ allDarts := by
    intro edge seen
    obtain ⟨i,_,rfl⟩ := mem_image.mp seen
    exact mem_offDiag.mpr ⟨mem_univ _,mem_univ _,listBefore_ne (step i)⟩
  by_contra! tooMany
  obtain ⟨selected,subset,seven⟩ := exists_subset_card_eq (s := darts)
    (show 7 ≤ darts.card by omega)
  have found := sevenDarts_have_detour (subset.trans inside) seven
  let owner (edge : darts) : long := Classical.choose (mem_image.mp edge.property)
  have identifies (edge : darts) : dart (owner edge) = edge.val :=
    (Classical.choose_spec (mem_image.mp edge.property)).2
  let row (edge : darts) : Fin p := (owner edge).val
  have rowInjective : Function.Injective row := by
    intro a b same
    exact Subtype.ext ((identifies a).symm.trans ((congrArg dart (Subtype.ext same)).trans (identifies b)))
  have comparison (edge : darts) : BeforeIn paths (row edge) edge.val.1 edge.val.2 := by
    have own := step (owner edge)
    rw [identifies edge] at own
    exact own
  have impossible {s : ℕ} (positive : 0 < s) (bound : s+2 ≤ cutoff)
      (detour : SmallDartDetour selected s) : False := by
    obtain ⟨v,injective,riverStep,arcSteps⟩ := detour
    let river : darts := ⟨_,subset riverStep⟩
    let arc (i : Fin (s+1)) : darts := ⟨_,subset (arcSteps i)⟩
    have arcInjective : Function.Injective arc := by
      intro i j same
      have first : i.castSucc = j.castSucc := injective (congrArg (fun e : darts => e.val.1) same)
      exact Fin.ext (congrArg (@Fin.val (s+2)) first)
    have apart (i : Fin (s+1)) : row river ≠ row (arc i) := by
      intro equal
      have same := rowInjective equal
      have first := congrArg Fin.val (injective (congrArg (fun e : darts => e.val.1) same))
      have last := congrArg Fin.val (injective (congrArg (fun e : darts => e.val.2) same))
      change 0 = i.val at first
      change s+1 = i.val+1 at last
      omega
    exact (free bound).false ⟨v,row ∘ arc,row river,injective,rowInjective.comp arcInjective,
      apart,comparison river,fun i => comparison (arc i)⟩
  exact found.elim (impossible (by decide) (by omega)) (impossible (by decide) large)

/-- An exact literal half budget can be feasible even when the full
extremum has no eligible family at the same exact counts. -/
theorem fourVertexEleven_half_feasible_full_infeasible {cutoff : ℕ} (large : 4 ≤ cutoff) :
    (∃ paths : Fin 11 → List (Fin 4), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (BeforeIn paths) cutoff) ∧
    ¬ (∃ paths : Fin 11 → List (Fin 4), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ BridgeFree (BeforeIn paths) cutoff) := by
  obtain ⟨distinct,rows,free⟩ := fourVertexElevenHalfRows_spec
  refine ⟨⟨fourVertexElevenHalfRows,distinct,rows,free cutoff⟩,?_⟩
  rintro ⟨paths,unique,well,full⟩
  have count := fourVertex_literal_full_path_count_le_ten paths unique (fun i => (well i).1)
    (fun i => (well i).2) full large
  omega

end OnlineReachabilityPreservers.SourceAudit
