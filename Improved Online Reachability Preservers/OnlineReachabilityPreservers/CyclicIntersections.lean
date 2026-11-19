import OnlineReachabilityPreservers.IntersectionOrder
import OnlineReachabilityPreservers.SplitAudit

/-! The intersection order for chosen witnesses in locally ordered paths. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V I : Type*} [DecidableEq V] [LinearOrder I]

local notation "ListBefore" => SourceAudit.BeforeIn

omit [LinearOrder I] in
theorem listBefore_ne {paths : I → List V} {i : I} {x y : V}
    (h : ListBefore paths i x y) : x ≠ y := by
  rintro rfl
  exact (lt_irrefl _ h.2.2)

omit [LinearOrder I] in
theorem listBefore_total {paths : I → List V} {i : I} {x y : V}
    (hx : x ∈ paths i) (hy : y ∈ paths i) (ne : x ≠ y) :
    ListBefore paths i x y ∨ ListBefore paths i y x := by
  rcases lt_or_gt_of_ne (fun eq => ne ((List.idxOf_inj hx).mp eq)) with h | h
  · exact Or.inl ⟨hx, hy, h⟩
  · exact Or.inr ⟨hy, hx, h⟩

theorem no_parallel_list_steps {paths : I → List V} {size : ℕ} (free : HalfBridgeFree (ListBefore paths) size)
    (large : 2 ≤ size)
    {a b : I} (ab : a ≠ b) {x y : V} (one : ListBefore paths a x y) (two : ListBefore paths b x y) : False := by
  have forbid {u v : I} (earlier : u < v) (left : ListBefore paths u x y)
      (right : ListBefore paths v x y) : False := by
    let bridge : Bridge (ListBefore paths) 0 :=
      ⟨![x, y], ![u], v, by
        intro i j eq
        have xy := listBefore_ne one
        fin_cases i <;> fin_cases j <;> simp_all,
        by intro i j _; fin_cases i; fin_cases j; rfl,
        by intro i; fin_cases i; exact earlier.ne', right,
        by intro i; fin_cases i; exact left⟩
    exact free large bridge earlier
  rcases lt_or_gt_of_ne ab with earlier | later
  · exact forbid earlier one two
  · exact forbid later two one

def threeListBridge {paths : I → List V} {a b r : I}
    (ab : a ≠ b) (ra : r ≠ a) (rb : r ≠ b) {x y z : V}
    (first : ListBefore paths a x y) (last : ListBefore paths b y z)
    (river : ListBefore paths r x z) : Bridge (ListBefore paths) 1 where
  vertex := ![x, y, z]
  arc := ![a, b]
  river := r
  distinctVertices := by
    intro i j eq
    have xy := listBefore_ne first
    have yz := listBefore_ne last
    have xz := listBefore_ne river
    fin_cases i <;> fin_cases j <;> simp_all
  distinctArcs := by
    intro i j eq
    fin_cases i <;> fin_cases j <;> simp_all
  river_ne_arc i := by fin_cases i; exacts [ra, rb]
  riverStep := river
  arcStep i := by fin_cases i; exacts [first, last]

/-- A chosen witness of a left-to-right intersection chain. The lists may
specify their own vertex orders. -/
structure ListIntersectionChain (paths : I → List V) (left middle right : I) (x y : V) : Prop where
  left_ne_middle : left ≠ middle
  left_ne_right : left ≠ right
  right_earlier : right < middle
  on_left : x ∈ paths left
  on_right : y ∈ paths right
  middle_step : ListBefore paths middle x y

/-- Two different middle paths cannot have the same chosen left anchor. -/
theorem lemma24_list_left_injective {paths : I → List V} (free : HalfBridgeFree (ListBefore paths) 4)
    {l a b r : I} {x ya yb : V} (ha : ListIntersectionChain paths l a r x ya)
    (hb : ListIntersectionChain paths l b r x yb) : a = b := by
  have forbid {a b : I} {ya yb : V} (ha : ListIntersectionChain paths l a r x ya)
      (hb : ListIntersectionChain paths l b r x yb) (different : a ≠ b)
      (step : ListBefore paths r ya yb) : False :=
    free (by decide) (threeListBridge ha.right_earlier.ne' different.symm hb.right_earlier.ne'
      ha.middle_step step hb.middle_step) hb.right_earlier
  by_contra different
  by_cases rightEqual : ya = yb
  · subst yb
    exact no_parallel_list_steps free (by decide) different ha.middle_step hb.middle_step
  rcases listBefore_total ha.on_right hb.on_right rightEqual with order | order
  · exact forbid ha hb different order
  · exact forbid hb ha (show b ≠ a from fun equal => different equal.symm) order

/-- The chosen right anchors cannot go backwards when the left anchors
of distinct middle paths go forwards. No common vertex order is used. -/
theorem lemma24_list_right_monotone {paths : I → List V} (free : HalfBridgeFree (ListBefore paths) 4)
    {l a b r : I} {xa xb ya yb : V} (different : a ≠ b)
    (ha : ListIntersectionChain paths l a r xa ya) (hb : ListIntersectionChain paths l b r xb yb)
    (left : ListBefore paths l xa xb) : (paths r).idxOf ya ≤ (paths r).idxOf yb := by
  by_contra! backward
  have right : ListBefore paths r yb ya := ⟨hb.on_right, ha.on_right, backward⟩
  have xy : xa ≠ yb := by
    rintro rfl
    exact no_parallel_list_steps free (by decide) ha.right_earlier.ne right ha.middle_step
  have yx : xb ≠ ya := by
    rintro rfl
    exact no_parallel_list_steps free (by decide) ha.left_ne_middle left ha.middle_step
  let bridge : Bridge (ListBefore paths) 2 :=
    ⟨![xa, xb, yb, ya], ![l, b, r], a, by
      intro i j eq
      have xaxb := listBefore_ne left
      have xaya := listBefore_ne ha.middle_step
      have xbyb := listBefore_ne hb.middle_step
      have ybya := listBefore_ne right
      fin_cases i <;> fin_cases j <;> simp_all,
      by
        intro i j eq
        have lb := hb.left_ne_middle
        have lr := hb.left_ne_right
        have br := hb.right_earlier.ne'
        fin_cases i <;> fin_cases j <;> simp_all,
      by intro i; fin_cases i; exacts [ha.left_ne_middle.symm, different, ha.right_earlier.ne'],
      ha.middle_step, by intro i; fin_cases i; exacts [left, hb.middle_step, right]⟩
  exact free (by decide) bridge ha.right_earlier

/-- Full bridge-freeness makes the chosen right anchors strictly increasing. -/
theorem lemma24_list_right_strict {paths : I → List V} (free : BridgeFree (ListBefore paths) 4)
    {l a b r : I} {xa xb ya yb : V} (different : a ≠ b)
    (ha : ListIntersectionChain paths l a r xa ya) (hb : ListIntersectionChain paths l b r xb yb)
    (left : ListBefore paths l xa xb) : ListBefore paths r ya yb := by
  refine ⟨ha.on_right, hb.on_right, (lemma24_list_right_monotone free.halfFree different ha hb left).lt_of_ne ?_⟩
  intro equal
  have same := (List.idxOf_inj ha.on_right).mp equal
  subst yb
  exact (free (show 3 ≤ 4 by decide)).false
    (threeListBridge hb.left_ne_middle ha.left_ne_middle.symm different left hb.middle_step ha.middle_step)

variable [Fintype I]

/-- The middle paths that admit at least one intersection witness. -/
noncomputable def listRMiddles (paths : I → List V) (l r : I) : Finset I := by
  classical
  exact univ.filter (fun i => ∃ x y, ListIntersectionChain paths l i r x y)

/-- Lemma 24's fiber bound for arbitrary simple paths when the fiber counts
middle paths. Choose one witness per middle path. Distinct middle paths
have different anchors even when some pairs intersect several times. -/
theorem lemma24_list_fiber_card {paths : I → List V} (free : HalfBridgeFree (ListBefore paths) 4)
    (l r : I) : (listRMiddles paths l r).card ≤ (paths l).length := by
  classical
  let R := listRMiddles paths l r
  have witness (i : R) : ∃ x y, ListIntersectionChain paths l i.val r x y :=
    (mem_filter.mp i.property).2
  let left (i : R) := Classical.choose (witness i)
  let right (i : R) := Classical.choose (Classical.choose_spec (witness i))
  have chain (i : R) : ListIntersectionChain paths l i.val r (left i) (right i) :=
    Classical.choose_spec (Classical.choose_spec (witness i))
  have size : R.attach.card ≤ (paths l).toFinset.card := by
    apply card_le_card_of_injOn left
    · intro i _
      exact List.mem_toFinset.mpr (chain i).on_left
    · intro i _ j _ equal
      apply Subtype.ext
      exact lemma24_list_left_injective free (chain i) (equal ▸ chain j)
  exact (by simpa [R] using size : (listRMiddles paths l r).card ≤ (paths l).toFinset.card).trans
    (List.toFinset_card_le (paths l))

/-- One left anchor and two right anchors can witness the same middle path. -/
def cyclicIntersectionExample : Fin 3 → List (Fin 4) := ![[0], [2, 1], [0, 1, 2]]

/-- Counting all intersection witnesses can exceed the left path length in a
bridge-free cyclic system. Counting distinct middle paths keeps the bound. -/
theorem lemma24_repeated_right_witness :
    (∀ k, IsEmpty (Bridge (ListBefore cyclicIntersectionExample) k)) ∧
      (∀ i, (cyclicIntersectionExample i).Nodup) ∧
      (cyclicIntersectionExample 0).length = 1 ∧
      ListIntersectionChain cyclicIntersectionExample 0 2 1 0 1 ∧
      ListIntersectionChain cyclicIntersectionExample 0 2 1 0 2 := by
  let parent : Fin 3 → Fin 3 := ![1, 2, 0]
  have injective : ∀ i j, parent i = parent j → i = j := by decide
  have keeps : ∀ i x y, ListBefore cyclicIntersectionExample i x y →
      ListBefore SourceAudit.splitExample (parent i) x y := by
    unfold SourceAudit.BeforeIn
    decide
  refine ⟨fun k => ⟨fun b => (SourceAudit.splitExample_bridge_free k).false
    (b.mapPaths parent (fun {_ _} eq => injective _ _ eq) keeps)⟩, by decide, rfl, ?_, ?_⟩
  · exact ⟨by decide, by decide, by decide, by decide, by decide, by unfold SourceAudit.BeforeIn; decide⟩
  · exact ⟨by decide, by decide, by decide, by decide, by decide, by unfold SourceAudit.BeforeIn; decide⟩

end OnlineReachabilityPreservers
