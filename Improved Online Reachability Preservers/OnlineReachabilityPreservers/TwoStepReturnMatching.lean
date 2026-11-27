import Mathlib.Data.Prod.Lex
import OnlineReachabilityPreservers.CyclicIntersections

/-! Ordered intersections for returns through two distinct other rows. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

variable {V I : Type*} [DecidableEq V] [LinearOrder I]

local instance decidableIntersectionBefore (rows : I → List V) (i : I) (x y : V) :
    Decidable (Before rows i x y) := by
  unfold SourceAudit.BeforeIn
  infer_instance

/-- One comparison on a third row, with an endpoint on each of two
fixed rows. The rows are distinct. -/
structure ListIntersectionStep (rows : I → List V) (left middle right : I) (x y : V) : Prop where
  left_ne_middle : left ≠ middle
  left_ne_right : left ≠ right
  right_ne_middle : right ≠ middle
  on_left : x ∈ rows left
  on_right : y ∈ rows right
  step : Before rows middle x y

/-- With full exclusion through four, distinct middle rows give distinct
anchors and their comparisons agree on the two fixed rows. -/
theorem full_list_intersection_matching {rows : I → List V}
    (free : BridgeFree (Before rows) 4) {left right a b : I} {x x' y y' : V}
    (different : a ≠ b)
    (first : ListIntersectionStep rows left a right x y)
    (second : ListIntersectionStep rows left b right x' y') :
    x ≠ x' ∧ y ≠ y' ∧ (Before rows left x x' ↔ Before rows right y y') := by
  let tag (i : I) : Bool := decide (i ≠ right)
  let Label := {u : Lex (Bool × I) // (ofLex u).1 = tag (ofLex u).2}
  let label (i : I) : Label := ⟨toLex (tag i, i), rfl⟩
  let project (i : Label) : I := (ofLex i.val).2
  let ordered (i : Label) := rows (project i)
  have uniqueLabels : Function.Injective project := by
    intro i j equal
    apply Subtype.ext
    apply ofLex.injective
    exact Prod.ext (i.property.trans ((congrArg tag equal).trans j.property.symm)) equal
  have orderedFree : BridgeFree (Before ordered) 4 := by
    intro k small
    exact ⟨fun b => (free small).false (b.mapPaths project uniqueLabels (fun _ _ _ step => step))⟩
  have rightFirst {i : I} (apart : i ≠ right) : label right < label i := by
    change toLex (tag right, right) < toLex (tag i, i)
    apply Prod.Lex.toLex_lt_toLex.mpr
    left
    have firstTag : tag right = false := by simp [tag]
    have laterTag : tag i = true := by simp [tag, apart]
    rw [show (tag right, right).1 = tag right from rfl, show (tag i, i).1 = tag i from rfl,
      firstTag, laterTag]
    decide
  have chain {c : I} {u v : V} (step : ListIntersectionStep rows left c right u v) :
      ListIntersectionChain ordered (label left) (label c) (label right) u v :=
    ⟨fun eq => step.left_ne_middle (congrArg project eq),
      fun eq => step.left_ne_right (congrArg project eq), rightFirst step.right_ne_middle.symm,
      step.on_left, step.on_right, step.step⟩
  have differentLabels : label a ≠ label b := fun eq => different (congrArg project eq)
  have separated : x ≠ x' := by
    rintro rfl
    exact differentLabels (lemma24_list_left_injective orderedFree.halfFree (chain first) (chain second))
  have forward : Before rows left x x' → Before rows right y y' :=
    lemma24_list_right_strict orderedFree differentLabels (chain first) (chain second)
  have backward : Before rows left x' x → Before rows right y' y :=
    lemma24_list_right_strict orderedFree differentLabels.symm (chain second) (chain first)
  have separateTargets : y ≠ y' := by
    rcases listBefore_total first.on_left second.on_left separated with order | order
    · exact listBefore_ne (forward order)
    · exact (listBefore_ne (backward order)).symm
  refine ⟨separated, separateTargets, forward, ?_⟩
  intro order
  rcases listBefore_total first.on_left second.on_left separated with earlier | later
  · exact earlier
  · exact (lt_asymm order.2.2 (backward later).2.2).elim

/-- A comparison on the first alternative row and a comparison on a
third row return backward along the parent at the fixed vertex. -/
structure TwoStepReturnAt (rows : I → List V) (parent first third : I) (x y z : V) : Prop where
  cross : ListIntersectionStep rows first third parent z y
  into_return : Before rows first x z
  parent_step : Before rows parent y x

/-- At a fixed parent, first alternative row and common vertex,
different third rows give distinct corresponding corners in order. -/
theorem two_step_returns_agree_in_order {rows : I → List V}
    (free : BridgeFree (Before rows) 4) {parent first a b : I} {x y y' z z' : V}
    (different : a ≠ b) (one : TwoStepReturnAt rows parent first a x y z)
    (two : TwoStepReturnAt rows parent first b x y' z') :
    y ≠ y' ∧ z ≠ z' ∧ (Before rows parent y y' ↔ Before rows first z z') := by
  obtain ⟨distinctZ, distinctY, order⟩ := full_list_intersection_matching free different one.cross two.cross
  exact ⟨distinctY, distinctZ, order.symm⟩

omit [LinearOrder I] in
/-- At most one pair of corners can belong to a given third row
when the original paths have unique intersections. -/
theorem two_step_return_corners_unique {rows : I → List V}
    (unique : ∀ ⦃i j u v⦄, i ≠ j → u ∈ rows i → u ∈ rows j →
      v ∈ rows i → v ∈ rows j → u = v)
    {parent first third : I} {x y y' z z' : V}
    (one : TwoStepReturnAt rows parent first third x y z)
    (two : TwoStepReturnAt rows parent first third x y' z') :
    y = y' ∧ z = z' :=
  ⟨unique one.cross.right_ne_middle one.cross.on_right one.cross.step.2.1
      two.cross.on_right two.cross.step.2.1,
    unique one.cross.left_ne_middle one.cross.on_left one.cross.step.1
      two.cross.on_left two.cross.step.1⟩

variable [Fintype I]

/-- The distinct third rows that can complete a return after choosing
the parent, the first alternative row, and their common vertex. -/
noncomputable def twoStepReturnThirdRows (rows : I → List V) (parent first : I) (x : V) : Finset I := by
  classical
  exact univ.filter fun third => ∃ y z, TwoStepReturnAt rows parent first third x y z

omit [LinearOrder I] in
theorem mem_twoStepReturnThirdRows {rows : I → List V} {parent first third : I} {x : V} :
    third ∈ twoStepReturnThirdRows rows parent first x ↔
      ∃ y z, TwoStepReturnAt rows parent first third x y z := by
  classical
  simp only [twoStepReturnThirdRows, mem_filter, mem_univ, true_and]

/-- The number of possible third rows is bounded by both the available
predecessors on the parent and the successors on the first alternative. -/
theorem two_step_return_third_rows_card {rows : I → List V}
    (free : BridgeFree (Before rows) 4) (parent first : I) (x : V) :
    let thirds := twoStepReturnThirdRows rows parent first x
    thirds.card ≤ ((rows parent).toFinset.filter fun y => Before rows parent y x).card ∧
      thirds.card ≤ ((rows first).toFinset.filter fun z => Before rows first x z).card := by
  classical
  let thirds := twoStepReturnThirdRows rows parent first x
  have witness (i : thirds) : ∃ y z, TwoStepReturnAt rows parent first i.val x y z :=
    mem_twoStepReturnThirdRows.mp i.property
  choose ys zs returns using witness
  have separate {a b : thirds} (apart : a ≠ b) : ys a ≠ ys b ∧ zs a ≠ zs b := by
    obtain ⟨left, right, _⟩ := two_step_returns_agree_in_order free
      (fun eq => apart (Subtype.ext eq)) (returns a) (returns b)
    exact ⟨left, right⟩
  constructor
  · rw [← card_attach (s := thirds)]
    exact card_le_card_of_injOn ys
      (fun a _ => mem_filter.mpr ⟨List.mem_toFinset.mpr (returns a).parent_step.1, (returns a).parent_step⟩)
      (fun a _ b _ equal => by by_contra apart; exact (separate apart).1 equal)
  · rw [← card_attach (s := thirds)]
    exact card_le_card_of_injOn zs
      (fun a _ => mem_filter.mpr ⟨List.mem_toFinset.mpr (returns a).into_return.2.1, (returns a).into_return⟩)
      (fun a _ b _ equal => by by_contra apart; exact (separate apart).2 equal)

variable [Fintype V]

/-- All third rows and corner pairs that complete the return. -/
noncomputable def twoStepReturnWitnesses (rows : I → List V) (parent first : I) (x : V) :
    Finset (I × V × V) := by
  classical
  exact univ.filter fun w => TwoStepReturnAt rows parent first w.1 x w.2.1 w.2.2

/-- Under unique intersections, counting the witnesses or their distinct
third rows gives the same result. -/
theorem two_step_return_witness_count_eq {rows : I → List V}
    (unique : ∀ ⦃i j u v⦄, i ≠ j → u ∈ rows i → u ∈ rows j →
      v ∈ rows i → v ∈ rows j → u = v)
    (parent first : I) (x : V) :
    (twoStepReturnWitnesses rows parent first x).card =
      (twoStepReturnThirdRows rows parent first x).card := by
  classical
  let W := twoStepReturnWitnesses rows parent first x
  have present {w : I × V × V} (member : w ∈ W) :
      TwoStepReturnAt rows parent first w.1 x w.2.1 w.2.2 :=
    (mem_filter.mp member).2
  have labels : W.image Prod.fst = twoStepReturnThirdRows rows parent first x := by
    ext label
    constructor
    · intro member
      obtain ⟨⟨i, y, z⟩, on, rfl⟩ := mem_image.mp member
      exact mem_twoStepReturnThirdRows.mpr ⟨y, z, present on⟩
    · intro member
      obtain ⟨y, z, witness⟩ := mem_twoStepReturnThirdRows.mp member
      exact mem_image.mpr ⟨(label, y, z), mem_filter.mpr ⟨mem_univ _, witness⟩, rfl⟩
  have injective : Set.InjOn Prod.fst (W : Set (I × V × V)) := by
    rintro ⟨i, y, z⟩ inW ⟨j, y', z'⟩ inW' same
    change i = j at same
    subst j
    have one : TwoStepReturnAt rows parent first i x y z := present (w := (i, y, z)) inW
    have two : TwoStepReturnAt rows parent first i x y' z' := present (w := (i, y', z')) inW'
    obtain ⟨left, right⟩ := two_step_return_corners_unique unique one two
    rw [left, right]
  exact (card_image_of_injOn injective).symm.trans (congrArg Finset.card labels)

end OnlineReachabilityPreservers
