import OnlineReachabilityPreservers.LocalFrozenCleaning

/-! Contiguous regularization with unique intersections through bridge size six. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "ListBefore" => SourceAudit.BeforeIn

variable {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype I]

omit [LinearOrder I] [Fintype I] in
private theorem contiguousBlocks_separated {paths : I → List V} {width : ℕ}
    {i j : ListBlockIndex paths width} (different : i ≠ j) (same : i.fst = j.fst) :
    (∀ {x y}, x ∈ splitListPaths paths width i → y ∈ splitListPaths paths width j → ListBefore paths i.fst x y) ∨
    (∀ {x y}, x ∈ splitListPaths paths width i → y ∈ splitListPaths paths width j → ListBefore paths i.fst y x) := by
  obtain ⟨i,a⟩ := i
  obtain ⟨j,b⟩ := j
  change i = j at same
  subst j
  have distinct : a.val ≠ b.val := fun eq => different (congrArg (Sigma.mk i) (Fin.ext eq))
  have order {u v : V} {r t : ℕ} (uMem : u ∈ localPathBlock (paths i) width r)
      (vMem : v ∈ localPathBlock (paths i) width t) (lt : r < t) : ListBefore paths i u v := by
    obtain ⟨uOn,rankU⟩ := mem_localPathBlock.mp uMem
    obtain ⟨vOn,rankV⟩ := mem_localPathBlock.mp vMem
    refine ⟨uOn,vOn,?_⟩
    by_contra! reverse
    have divided : (paths i).idxOf v / width ≤ (paths i).idxOf u / width := Nat.div_le_div_right reverse
    rw [rankU,rankV] at divided
    omega
  rcases lt_or_gt_of_ne distinct with ab | ba
  · exact Or.inl (fun h h' => order h h' ab)
  · exact Or.inr (fun h h' => order h' h ba)

omit [Fintype I] in
private theorem sixBlocks_project {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y)
    (three : BridgeFree (ListBefore paths) 3) (width : ℕ) {k : ℕ} (short : k ≤ 4)
    (b : Bridge (ListBefore (splitListPaths paths width)) k) :
    ∃ old : Bridge (ListBefore paths) k, old.river = b.river.fst ∧ old.arc = fun i => (b.arc i).fst := by
  let W := ListBlockIndex paths width
  let parent (j : W) := j.fst
  let pieces := splitListPaths paths width
  have steps {i : W} {x y : V} (bc : ListBefore pieces i x y) : ListBefore paths (parent i) x y :=
    listBefore_of_sublist (paths := fun j => paths (parent j)) (simple (parent i)) List.filter_sublist bc
  have together {i j q : W} {x y : V} (_same : parent i = parent j) (diff : parent i ≠ parent q)
      (xy : ListBefore paths (parent i) x y) (yx : ListBefore pieces q y x)
      (_left : x ∈ pieces i) (_right : y ∈ pieces j) : i = j := by
    have step := steps yx
    exact (listBefore_ne xy (unique diff xy.1 step.2.1 xy.2.1 step.1)).elim
  by_cases small : k ≤ 3
  · let old := listBridge_after_opposite_safe_split_through_five parent
      (fun {i _ _} h => steps (i := i) h) (fun {_ _ _} => splitListPaths_disjoint)
      (fun _ {_ _ _ _} diff one two => no_parallel_list_steps three.halfFree (by decide) diff one two)
      (fun _ {_ _ _ _ _} => together) small b
    exact ⟨old,rfl,rfl⟩
  · have kSix : k = 4 := by omega
    subst k
    let old := listBridge_after_contiguous_opposite_safe_split_six parent
      (fun {i _ _} h => steps (i := i) h) (fun {_ _ _} => splitListPaths_disjoint)
      (fun {_ _ _ _ _} => together) (fun {_ _} => contiguousBlocks_separated) three b
    exact ⟨old,rfl,rfl⟩

private theorem regularizedSix_bridge_free {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y)
    {half : Bool} (four : BridgeFree (ListBefore paths) 4) (free : localOrderAdmissible half 6 paths)
    (D L : ℕ) : localOrderAdmissible half 6 (listRegularizedPaths paths D L) := by
  let copies := splitListVertices paths D
  have copyStep {i : I} {x y : ListVertexBlockIndex paths D} (step : ListBefore copies i x y) :
      ListBefore paths i x.fst y.fst := splitListVertices_step (simple i) step
  have copiedSimple (i : I) : (copies i).Nodup := splitListVertices_simple paths D i (simple i)
  have copyUnique {a b x y} (ne : a ≠ b) (ax : x ∈ copies a) (bx : x ∈ copies b)
      (ay : y ∈ copies a) (by' : y ∈ copies b) : x = y :=
    splitListVertices_unique simple (fun {_ _ _ _} => unique) ne ax bx ay by'
  have oldThree : BridgeFree (ListBefore paths) 3 := fun _ hb => four (hb.trans (by decide))
  have three : BridgeFree (ListBefore copies) 3 :=
    BridgeFree.split_list_vertices_any oldThree (·.fst) (fun {_ _ _} => copyStep)
  cases half
  · have copyFree : BridgeFree (ListBefore copies) 6 :=
      (show BridgeFree (ListBefore paths) 6 from free).split_list_vertices_any (·.fst) (fun {_ _ _} => copyStep)
    intro k hk
    exact ⟨fun b => by
      obtain ⟨old,_,_⟩ := sixBlocks_project copiedSimple (fun {_ _ _ _} => copyUnique) three L (by omega) b
      exact (copyFree hk).false old⟩
  · have copyHalf : HalfBridgeFree (ListBefore copies) 6 :=
      (show HalfBridgeFree (ListBefore paths) 6 from free).split_list_vertices_of_full four (by decide)
        (·.fst) (fun {_ _ _} => copyStep)
    intro k hk b earlier
    obtain ⟨old,river,arcs⟩ := sixBlocks_project copiedSimple (fun {_ _ _ _} => copyUnique) three L (by omega) b
    apply copyHalf hk old
    have sameLast : old.arc (Fin.last k) = (b.arc (Fin.last k)).fst := congrFun arcs _
    have diff : (b.arc (Fin.last k)).fst ≠ b.river.fst := by
      rw [← sameLast,← river]
      exact (old.river_ne_arc _).symm
    rw [sameLast,river]
    have parentLe : (b.arc (Fin.last k)).fst ≤ b.river.fst :=
      (block_parent_mono (fun i => (copies i).toFinset) L) (le_of_lt earlier)
    exact parentLe.lt_of_ne diff

variable [Fintype V]

/-- With unique intersections, the two regularization splits preserve full
exclusion through size six. They also preserve half exclusion through size
six when the input excludes full bridges through size four. The cleaned
witness meets both budgets and all four frozen caps. -/
theorem regularization_list_frozen_unique_six {half : Bool} (paths : I → List V)
    (simple : ∀ i, (paths i).Nodup)
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b → y ∈ paths a → y ∈ paths b → x = y)
    (free : localOrderAdmissible half 6 paths)
    (fourForHalf : half = true → BridgeFree (ListBefore paths) 4)
    (hn : 0 < Fintype.card V) (hp : 0 < Fintype.card I)
    (dense : Fintype.card V ≤ ∑ i, (paths i).length) (long : Fintype.card I ≤ ∑ i, (paths i).length) :
    let n := Fintype.card V
    let p := Fintype.card I
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half 6 clean ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let n := Fintype.card V
  let p := Fintype.card I
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let after := listRegularizedPaths paths D L
  obtain ⟨hD,trimD,_⟩ := four_average_width hn dense
  obtain ⟨hL,trimL,_⟩ := four_average_width hp long
  obtain ⟨rawV,rawI⟩ := regularization_list_counts paths simple hD hL
  have vCap : 3*Fintype.card (ListVertexBlockIndex paths D) ≤ 4*n := by
    change 3*(M/D) ≤ n at trimD
    change Fintype.card (ListVertexBlockIndex paths D) ≤ n+M/D at rawV
    omega
  have iCap : 3*Fintype.card (ListBlockIndex (splitListVertices paths D) L) ≤ 4*p := by
    change 3*(M/L) ≤ p at trimL
    change Fintype.card (ListBlockIndex (splitListVertices paths D) L) ≤ p+M/L at rawI
    omega
  have four : BridgeFree (ListBefore paths) 4 := by
    cases mode : half
    · have full : BridgeFree (ListBefore paths) 6 := by simpa [mode,localOrderAdmissible] using free
      exact fun _ hk => full (hk.trans (by decide))
    · exact fourForHalf mode
  obtain ⟨mass,width,degree⟩ := regularization_list_mass_caps paths simple D L hD hL
  exact regularization_list_frozen_after_caps_with_room after (listRegularizedPaths_simple paths simple D L)
    (regularizedSix_bridge_free simple (fun {_ _ _ _} => unique) four free D L)
    hn hp dense long vCap iCap width degree mass

end OnlineReachabilityPreservers
