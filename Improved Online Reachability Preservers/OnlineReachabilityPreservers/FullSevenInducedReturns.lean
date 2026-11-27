import OnlineReachabilityPreservers.FullSevenPathLinks
import OnlineReachabilityPreservers.FullSevenReverseComparison

/-! A covering path split only needs to protect induced two-step returns. -/

namespace OnlineReachabilityPreservers

local notation "Before" => SourceAudit.BeforeIn

variable {I J V : Type*} [DecidableEq V]

/-- The row–vertex incidences of this directed triangle give an induced
six-cycle: each corner is absent from its opposite row. -/
def InducedTwoStepReturnAt (rows : I → List V) (parent first last : I) (x y z : V) : Prop :=
  TwoStepReturnAt rows parent first last x y z ∧
    y ∉ rows first ∧ z ∉ rows parent ∧ x ∉ rows last

/-- Protect a direct reversal or the ends of an induced two-step return. -/
def fullSevenInducedPathLink (rows : I → List V) (i : I) (x y : V) : Prop :=
  Before rows i x y ∧
    ((∃ j, Before rows j y x) ∨ ∃ a c z, InducedTwoStepReturnAt rows i a c y x z)

theorem fullSevenInducedPathLink_le {rows : I → List V} {i : I} {x y : V}
    (link : fullSevenInducedPathLink rows i x y) : fullSevenPathLink rows i x y := by
  refine ⟨link.1, ?_⟩
  rcases link.2 with direct | ⟨a, c, z, induced⟩
  · exact Or.inl direct
  · exact Or.inr ⟨a, c, z, induced.1⟩

/-- With the one-step condition and coverage, only induced two-step
returns need to be checked on the actual pieces. -/
theorem fullBridgeFree_of_cover_and_induced_returns [LinearOrder I]
    {rows : I → List V} {pieces : J → List V} (parent : J → I)
    (free : BridgeFree (Before rows) 7)
    (steps : ∀ {i x y}, Before pieces i x y → Before rows (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (cover : ∀ {p x}, x ∈ rows p → ∃ j, parent j = p ∧ x ∈ pieces j)
    (mirror : ∀ {i j q x y}, parent i = parent j → parent i ≠ parent q →
      Before rows (parent i) x y → Before pieces q y x → x ∈ pieces i → y ∈ pieces j → i = j)
    (keepInduced : ∀ {i j a c x y z}, parent i = parent j → x ∈ pieces i → y ∈ pieces j →
      InducedTwoStepReturnAt rows (parent i) (parent a) (parent c) x y z →
      Before pieces a x z → Before pieces c z y → i = j) : BridgeFree (Before pieces) 7 := by
  refine fullBridgeFree_of_opposite_and_two_step_safe_split parent (fun {_ _ _} => steps)
    (fun {_ _ _} => disjoint) (fun {_ _ _ _ _} => mirror) ?_ free le_rfl
  intro i j a c x y z apart same aOther cOther detoursApart onX onY old first last
  have absent := crossed_two_step_return_missing_opposite_corners_of_cover
    (fun _ h => free (h.trans (by decide))) (fun {_ _ _} => steps) (fun {_ _} => cover)
    (fun {_ _ _ _ _} => mirror) apart same aOther cOther detoursApart onX onY old first last
  have route : TwoStepReturnAt rows (parent i) (parent a) (parent c) x y z :=
    ⟨⟨detoursApart, aOther.symm, cOther, (steps first).2.1, old.1, steps last⟩, steps first, old⟩
  exact apart (keepInduced same onX onY ⟨route, absent⟩ first last)

/-- Keeping the protected endpoints together suffices for covering
order-preserving pieces, even when they interleave. -/
theorem fullBridgeFree_of_full_seven_induced_path_links [LinearOrder I]
    {rows : I → List V} {pieces : J → List V} (parent : J → I)
    (free : BridgeFree (Before rows) 7)
    (steps : ∀ {i x y}, Before pieces i x y → Before rows (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (cover : ∀ {p x}, x ∈ rows p → ∃ j, parent j = p ∧ x ∈ pieces j)
    (together : ∀ {i j x y}, parent i = parent j → x ∈ pieces i → y ∈ pieces j →
      fullSevenInducedPathLink rows (parent i) x y → i = j) : BridgeFree (Before pieces) 7 := by
  refine fullBridgeFree_of_cover_and_induced_returns parent free (fun {_ _ _} => steps)
    (fun {_ _ _} => disjoint) (fun {_ _} => cover) ?_ ?_
  · intro i j q x y same _ forward reverse onX onY
    exact together same onX onY ⟨forward, Or.inl ⟨parent q, steps reverse⟩⟩
  · intro i j a c x y z same onX onY induced _ _
    have link : fullSevenInducedPathLink rows (parent i) y x :=
      ⟨induced.1.parent_step, Or.inr ⟨parent a, parent c, z, induced⟩⟩
    exact (together same.symm onY onX (same ▸ link)).symm

/-- If a two-step return has an opposite incidence, its endpoints are
already linked by a direct reversal or by two direct reversals. -/
theorem fullSevenPathLink_induced_or_two_links [LinearOrder I]
    {rows : I → List V} (free : BridgeFree (Before rows) 3) {i : I} {x y : V}
    (link : fullSevenPathLink rows i x y) : fullSevenInducedPathLink rows i x y ∨
      ∃ z, fullSevenInducedPathLink rows i x z ∧ fullSevenInducedPathLink rows i z y := by
  have forward := link.1
  rcases link.2 with direct | ⟨a, c, z, route⟩
  · exact Or.inl ⟨forward, Or.inl direct⟩
  have noParallel {j q : I} {u v : V} :=
    no_parallel_list_steps (a := j) (b := q) (x := u) (y := v) free.halfFree (by decide)
  by_cases inA : x ∈ rows a
  · have reverse := (listBefore_total route.into_return.1 inA (listBefore_ne forward).symm).resolve_right
      (fun parallel => noParallel route.cross.left_ne_right.symm forward parallel)
    exact Or.inl ⟨forward, Or.inl ⟨a, reverse⟩⟩
  by_cases inC : y ∈ rows c
  · have reverse := (listBefore_total inC route.cross.step.2.1 (listBefore_ne forward).symm).resolve_right
      (fun parallel => noParallel route.cross.right_ne_middle forward parallel)
    exact Or.inl ⟨forward, Or.inl ⟨c, reverse⟩⟩
  by_cases inParent : z ∈ rows i
  · have left := (listBefore_total forward.1 inParent (listBefore_ne route.cross.step).symm).resolve_right
      (fun parallel => noParallel route.cross.right_ne_middle parallel route.cross.step)
    have right := (listBefore_total inParent forward.2.1 (listBefore_ne route.into_return).symm).resolve_right
      (fun parallel => noParallel route.cross.left_ne_right.symm parallel route.into_return)
    exact Or.inr ⟨z, ⟨left, Or.inl ⟨c, route.cross.step⟩⟩, ⟨right, Or.inl ⟨a, route.into_return⟩⟩⟩
  exact Or.inl ⟨forward, Or.inr ⟨a, c, z, route, inA, inParent, inC⟩⟩

/-- The two link rules give the same static capped partitions under
full exclusion through three. -/
theorem cappedPathPartition_fullSevenInduced_iff [LinearOrder I]
    {rows : I → List V} (free : BridgeFree (Before rows) 3) (i : I)
    (width : ℕ) (groups : Finset (Finset V)) :
    CappedPathPartition (rows i).toFinset (fullSevenInducedPathLink rows i) width groups ↔
      CappedPathPartition (rows i).toFinset (fullSevenPathLink rows i) width groups := by
  constructor
  · intro partition
    refine ⟨partition.cover, partition.apart, partition.nonempty, partition.fits, ?_⟩
    intro x y link
    rcases fullSevenPathLink_induced_or_two_links free link with direct | ⟨z, left, right⟩
    · exact partition.together direct
    · obtain ⟨a, onA, xIn, zInA⟩ := partition.together left
      obtain ⟨b, onB, zInB, yIn⟩ := partition.together right
      have same : a = b := by
        by_contra apart
        exact Finset.disjoint_left.mp (partition.apart onA onB apart) zInA zInB
      exact ⟨a, onA, xIn, same.symm ▸ yIn⟩
  · intro partition
    exact ⟨partition.cover, partition.apart, partition.nonempty, partition.fits,
      fun {_ _} link => partition.together (fullSevenInducedPathLink_le link)⟩

end OnlineReachabilityPreservers
