import OnlineReachabilityPreservers.FullSevenWidthCleaning
import OnlineReachabilityPreservers.TwoStepReturnMatching

/-! Original reverse comparisons of crossed two-step returns. -/

namespace OnlineReachabilityPreservers

local notation "Before" => SourceAudit.BeforeIn

variable {I J V : Type*}

/-- A piece contains the parent vertices between any two of its vertices. -/
def ListPiecesOrderConvex [DecidableEq V] (rows : I → List V) (pieces : J → List V) (parent : J → I) : Prop :=
  ∀ ⦃i : J⦄ ⦃x y z : V⦄, x ∈ pieces i → z ∈ pieces i →
    Before rows (parent i) x y → Before rows (parent i) y z → y ∈ pieces i

/-- Consecutive width blocks are order convex. -/
theorem splitListPaths_order_convex [LinearOrder V] (rows : I → List V) (width : ℕ) :
    ListPiecesOrderConvex rows (splitListPaths rows width) Sigma.fst := by
  intro j x y z left right earlier later
  obtain ⟨_, atX⟩ := mem_localPathBlock.mp left
  obtain ⟨_, atZ⟩ := mem_localPathBlock.mp right
  have lower := Nat.div_le_div_right (c := width) earlier.2.2.le
  have upper := Nat.div_le_div_right (c := width) later.2.2.le
  exact mem_localPathBlock.mpr ⟨earlier.2.1,
    le_antisymm (upper.trans_eq atZ) ((atX.symm.le).trans lower)⟩

variable [DecidableEq V]

private theorem comparison_in_piece {rows : I → List V} {pieces : J → List V} {parent : J → I}
    (steps : ∀ {i x y}, Before pieces i x y → Before rows (parent i) x y)
    {i : J} {x y : V} (left : x ∈ pieces i) (right : y ∈ pieces i)
    (old : Before rows (parent i) x y) : Before pieces i x y := by
  rcases listBefore_total left right (listBefore_ne old) with direct | reverse
  · exact direct
  · exact (lt_asymm old.2.2 (steps reverse).2.2).elim

variable [LinearOrder I]

/-- A crossed two-step return on order-convex pieces has no reverse
comparison on any original row if the one-step condition holds. -/
theorem crossed_two_step_return_no_original_reverse
    {rows : I → List V} {pieces : J → List V} {parent : J → I}
    (free : BridgeFree (Before rows) 3)
    (steps : ∀ {i x y}, Before pieces i x y → Before rows (parent i) x y)
    (convex : ListPiecesOrderConvex rows pieces parent)
    (mirror : ∀ {i j q x y}, parent i = parent j → parent i ≠ parent q →
      Before rows (parent i) x y → Before pieces q y x → x ∈ pieces i → y ∈ pieces j → i = j)
    {i j a c : J} {x y z : V}
    (apart : i ≠ j) (same : parent i = parent j)
    (aOther : parent i ≠ parent a) (cOther : parent i ≠ parent c)
    (detoursApart : parent a ≠ parent c)
    (onX : x ∈ pieces i) (onY : y ∈ pieces j)
    (old : Before rows (parent i) y x)
    (first : Before pieces a x z) (last : Before pieces c z y) :
    ∀ q, ¬ Before rows q x y := by
  have onParentA := steps first
  have onParentC := steps last
  have forbid {q : J} (other : parent i ≠ parent q) (reverse : Before pieces q x y) : False :=
    apart.symm (mirror same.symm (same ▸ other) (same ▸ old) reverse onY onX)
  intro q reverse
  by_cases onFirst : q = parent a
  · have rev : Before rows (parent a) x y := onFirst ▸ reverse
    rcases listBefore_total rev.2.1 onParentA.2.1 (listBefore_ne onParentC).symm with yToZ | zToY
    · have retainedY : y ∈ pieces a := convex first.1 first.2.1 rev yToZ
      exact forbid aOther (comparison_in_piece (fun {_ _ _} => steps) first.1 retainedY rev)
    · exact no_parallel_list_steps free.halfFree (by decide) detoursApart zToY onParentC
  by_cases onLast : q = parent c
  · have rev : Before rows (parent c) x y := onLast ▸ reverse
    rcases listBefore_total onParentC.1 rev.1 (listBefore_ne onParentA).symm with zToX | xToZ
    · have retainedX : x ∈ pieces c := convex last.1 last.2.1 zToX rev
      exact forbid cOther (comparison_in_piece (fun {_ _ _} => steps) retainedX last.2.1 rev)
    · exact no_parallel_list_steps free.halfFree (by decide) detoursApart.symm xToZ onParentA
  exact (free (k := 1) (by decide)).false
    (threeListBridge detoursApart onFirst onLast onParentA onParentC reverse)

/-- A crossed return on convex pieces that cover their parents has each
of its three corners absent from the opposite row of the triangle. -/
theorem crossed_two_step_return_missing_opposite_corners
    {rows : I → List V} {pieces : J → List V} {parent : J → I}
    (free : BridgeFree (Before rows) 3)
    (steps : ∀ {i x y}, Before pieces i x y → Before rows (parent i) x y)
    (convex : ListPiecesOrderConvex rows pieces parent)
    (cover : ∀ {p x}, x ∈ rows p → ∃ j, parent j = p ∧ x ∈ pieces j)
    (mirror : ∀ {i j q x y}, parent i = parent j → parent i ≠ parent q →
      Before rows (parent i) x y → Before pieces q y x → x ∈ pieces i → y ∈ pieces j → i = j)
    {i j a c : J} {x y z : V}
    (apart : i ≠ j) (same : parent i = parent j)
    (aOther : parent i ≠ parent a) (cOther : parent i ≠ parent c)
    (detoursApart : parent a ≠ parent c)
    (onX : x ∈ pieces i) (onY : y ∈ pieces j)
    (old : Before rows (parent i) y x)
    (first : Before pieces a x z) (last : Before pieces c z y) :
    y ∉ rows (parent a) ∧ z ∉ rows (parent i) ∧ x ∉ rows (parent c) := by
  have firstOld := steps first
  have lastOld := steps last
  have noReturn := crossed_two_step_return_no_original_reverse
    free (fun {_ _ _} => steps) convex (fun {_ _ _ _ _} => mirror)
    apart same aOther cOther detoursApart onX onY old first last
  refine ⟨?_, ?_, ?_⟩
  · intro inA
    rcases listBefore_total firstOld.1 inA (listBefore_ne old).symm with reverse | parallel
    · exact noReturn (parent a) reverse
    · exact no_parallel_list_steps free.halfFree (by decide) aOther.symm parallel old
  · intro inParent
    have zToX : Before rows (parent i) z x :=
      (listBefore_total old.2.1 inParent (listBefore_ne firstOld)).resolve_left
        (fun parallel => no_parallel_list_steps free.halfFree (by decide) aOther parallel firstOld)
    have yToZ : Before rows (parent i) y z :=
      (listBefore_total old.1 inParent (listBefore_ne lastOld).symm).resolve_right
        (fun parallel => no_parallel_list_steps free.halfFree (by decide) cOther parallel lastOld)
    obtain ⟨middle, parentEq, inMiddle⟩ := cover inParent
    have toX : middle = i := mirror parentEq (parentEq.symm ▸ aOther)
      (parentEq.symm ▸ zToX) first inMiddle onX
    have toY : j = middle := mirror (same.symm.trans parentEq.symm) (same ▸ cOther)
      (same ▸ yToZ) last onY inMiddle
    exact apart (toX.symm.trans toY.symm)
  · intro inC
    rcases listBefore_total inC lastOld.2.1 (listBefore_ne old).symm with reverse | parallel
    · exact noReturn (parent c) reverse
    · exact no_parallel_list_steps free.halfFree (by decide) cOther.symm parallel old

/-- The one-step condition suffices on convex pieces if every original
two-step return on distinct parents has a direct reverse comparison. -/
theorem fullBridgeFree_of_convex_split_with_reverse_comparisons
    {rows : I → List V} {pieces : J → List V} {parent : J → I}
    (free : BridgeFree (Before rows) 7)
    (steps : ∀ {i x y}, Before pieces i x y → Before rows (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (convex : ListPiecesOrderConvex rows pieces parent)
    (mirror : ∀ {i j q x y}, parent i = parent j → parent i ≠ parent q →
      Before rows (parent i) x y → Before pieces q y x → x ∈ pieces i → y ∈ pieces j → i = j)
    (reverse : ∀ ⦃p a c x y z⦄, TwoStepReturnAt rows p a c x y z → ∃ q, Before rows q x y) :
    BridgeFree (Before pieces) 7 := by
  have noTwo : NoCrossedTwoStepReturn rows pieces parent := by
    intro i j a c x y z apart same aOther cOther detoursApart onX onY old first last
    have route : TwoStepReturnAt rows (parent i) (parent a) (parent c) x y z :=
      ⟨⟨detoursApart, aOther.symm, cOther, (steps first).2.1, old.1, steps last⟩,
        steps first, old⟩
    obtain ⟨q, rev⟩ := reverse route
    exact crossed_two_step_return_no_original_reverse
      (fun _ h => free (h.trans (by decide))) (fun {_ _ _} => steps) convex (fun {_ _ _ _ _} => mirror)
      apart same aOther cOther detoursApart onX onY old first last q rev
  exact fullBridgeFree_of_opposite_and_two_step_safe_split parent (fun {_ _ _} => steps)
    (fun {_ _ _} => disjoint) (fun {_ _ _ _ _} => mirror) noTwo free le_rfl

end OnlineReachabilityPreservers
