import OnlineReachabilityPreservers.CyclicIntersections
import OnlineReachabilityPreservers.FiniteChainPacking

/-! Reversed common intervals and their matched neighboring rank positions. -/

namespace OnlineReachabilityPreservers

local notation "ListBefore" => SourceAudit.BeforeIn

variable {V I : Type*} [DecidableEq V] [LinearOrder I]

/-- A reverse link between adjacent common vertices of two paths. -/
def OppositeNeighbors (paths : I → List V) (a b : I) (x y : V) : Prop :=
  a ≠ b ∧ ListBefore paths a x y ∧ ListBefore paths b y x ∧
    ¬ ∃ z, ListBefore paths a x z ∧ ListBefore paths a z y ∧ z ∈ paths b

/-- All reverse steps with one given starting vertex on a path use a common opposite path. -/
theorem oppositePartner_out_unique {paths : I → List V}
    (free : BridgeFree (ListBefore paths) 3) {a b c : I} {x y z : V}
    (ab : a ≠ b) (ac : a ≠ c) (xy : ListBefore paths a x y) (xz : ListBefore paths a x z)
    (yx : ListBefore paths b y x) (zx : ListBefore paths c z x) : b = c := by
  by_contra different
  have bc : b ≠ c := different
  by_cases same : y = z
  · exact no_parallel_list_steps free.halfFree (by decide) different yx (same.symm ▸ zx)
  rcases listBefore_total xy.2.1 xz.2.1 same with yz | zy
  · exact (free (k := 1) (by decide)).false (threeListBridge ac ab.symm bc yz zx yx)
  · exact (free (k := 1) (by decide)).false (threeListBridge ab ac.symm bc.symm zy yx zx)

/-- The same uniqueness holds at a given ending vertex. -/
theorem oppositePartner_in_unique {paths : I → List V}
    (free : BridgeFree (ListBefore paths) 3) {a b c : I} {x y z : V}
    (ab : a ≠ b) (ac : a ≠ c) (yx : ListBefore paths a y x) (zx : ListBefore paths a z x)
    (xy : ListBefore paths b x y) (xz : ListBefore paths c x z) : b = c := by
  by_contra different
  have bc : b ≠ c := different
  by_cases same : y = z
  · exact no_parallel_list_steps free.halfFree (by decide) different xy (same.symm ▸ xz)
  rcases listBefore_total yx.1 zx.1 same with yz | zy
  · exact (free (k := 1) (by decide)).false (threeListBridge ab.symm bc.symm ac.symm xy yz xz)
  · exact (free (k := 1) (by decide)).false (threeListBridge ac.symm bc ab.symm xz zy xy)

/-- After retaining only adjacent shared vertices, each vertex has at most one outgoing link. -/
theorem oppositeNeighbors_out_unique {paths : I → List V}
    (free : BridgeFree (ListBefore paths) 3) {a b c : I} {x y z : V}
    (xy : OppositeNeighbors paths a b x y) (xz : OppositeNeighbors paths a c x z) : y = z := by
  have partner := oppositePartner_out_unique free xy.1 xz.1 xy.2.1 xz.2.1 xy.2.2.1 xz.2.2.1
  subst c
  by_contra different
  rcases listBefore_total xy.2.1.2.1 xz.2.1.2.1 different with yz | zy
  · exact xz.2.2.2 ⟨y,xy.2.1,yz,xy.2.2.1.1⟩
  · exact xy.2.2.2 ⟨z,xz.2.1,zy,xz.2.2.1.1⟩

/-- Each vertex has at most one incoming link as well. -/
theorem oppositeNeighbors_in_unique {paths : I → List V}
    (free : BridgeFree (ListBefore paths) 3) {a b c : I} {x y z : V}
    (yx : OppositeNeighbors paths a b y x) (zx : OppositeNeighbors paths a c z x) : y = z := by
  have partner := oppositePartner_in_unique free yx.1 zx.1 yx.2.1 zx.2.1 yx.2.2.1 zx.2.2.1
  subst c
  by_contra different
  rcases listBefore_total yx.2.1.1 zx.2.1.1 different with yz | zy
  · exact yx.2.2.2 ⟨z,yz,zx.2.1,zx.2.2.1.2.1⟩
  · exact zx.2.2.2 ⟨y,zy,yx.2.1,yx.2.2.1.2.1⟩

/-- Adjacent common vertices occur in reverse order on the partner path. -/
theorem oppositeNeighbors_swap_of_halfTwo {paths : I → List V}
    (free : HalfBridgeFree (ListBefore paths) 2) {a b : I} {x y : V}
    (xy : OppositeNeighbors paths a b x y) : OppositeNeighbors paths b a y x := by
  refine ⟨xy.1.symm,xy.2.2.1,xy.2.1,?_⟩
  rintro ⟨z,yz,zx,inA⟩
  have xz : ListBefore paths a x z := by
    rcases listBefore_total xy.2.1.1 inA (listBefore_ne zx).symm with xz | zx'
    · exact xz
    · exact (no_parallel_list_steps free (by decide) xy.1 zx' zx).elim
  have zy : ListBefore paths a z y := by
    rcases listBefore_total inA xy.2.1.2.1 (listBefore_ne yz).symm with zy | yz'
    · exact zy
    · exact (no_parallel_list_steps free (by decide) xy.1 yz' yz).elim
  exact xy.2.2.2 ⟨z,xz,zy,yz.2.1⟩


theorem oppositeNeighbors_swap {paths : I → List V}
    (free : BridgeFree (ListBefore paths) 3) {a b : I} {x y : V}
    (xy : OppositeNeighbors paths a b x y) : OppositeNeighbors paths b a y x :=
  oppositeNeighbors_swap_of_halfTwo (fun _ size => free.halfFree (size.trans (by decide))) xy

/-- A reversed shared interval decomposes into links between consecutive common vertices. -/
theorem oppositeNeighbors_connect_of_halfTwo {paths : I → List V}
    (free : HalfBridgeFree (ListBefore paths) 2) {a b : I} (apart : a ≠ b)
    {x y : V} (xy : ListBefore paths a x y) (yx : ListBefore paths b y x) :
    Relation.TransGen (OppositeNeighbors paths a b) x y := by
  have connects (d : ℕ) : ∀ {x y : V},
      (paths a).idxOf y - (paths a).idxOf x ≤ d →
      ListBefore paths a x y → ListBefore paths b y x →
      Relation.TransGen (OppositeNeighbors paths a b) x y := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro x y gap xy yx
      classical
      by_cases between : ∃ z, ListBefore paths a x z ∧ ListBefore paths a z y ∧ z ∈ paths b
      · obtain ⟨z,xz,zy,onB⟩ := between
        have left : ListBefore paths b z x := by
          rcases listBefore_total onB yx.2.1 (listBefore_ne xz).symm with left | parallel
          · exact left
          · exact (no_parallel_list_steps free (by decide) apart xz parallel).elim
        have right : ListBefore paths b y z := by
          rcases listBefore_total yx.1 onB (listBefore_ne zy).symm with right | parallel
          · exact right
          · exact (no_parallel_list_steps free (by decide) apart zy parallel).elim
        have ltLeft : (paths a).idxOf z - (paths a).idxOf x < d := by
          have xzOrder := xz.2.2
          have zyOrder := zy.2.2
          omega
        have ltRight : (paths a).idxOf y - (paths a).idxOf z < d := by
          have xzOrder := xz.2.2
          have zyOrder := zy.2.2
          omega
        exact (ih _ ltLeft le_rfl xz left).trans (ih _ ltRight le_rfl zy right)
      · exact Relation.TransGen.single ⟨apart,xy,yx,between⟩
  exact connects _ le_rfl xy yx

theorem oppositeNeighbors_connect {paths : I → List V}
    (free : BridgeFree (ListBefore paths) 3) {a b : I} (apart : a ≠ b)
    {x y : V} (xy : ListBefore paths a x y) (yx : ListBefore paths b y x) :
    Relation.TransGen (OppositeNeighbors paths a b) x y :=
  oppositeNeighbors_connect_of_halfTwo (fun _ size => free.halfFree (size.trans (by decide))) apart xy yx

end OnlineReachabilityPreservers

namespace OnlineReachabilityPreservers

variable {V I : Type*} [DecidableEq V] [LinearOrder I]

/-- The position order on the vertices of one simple path. -/
def pathPositions (row : List V) (simple : row.Nodup) : {v : V // v ∈ row} ≃ Fin row.length where
  toFun v := ⟨row.idxOf v.val, List.idxOf_lt_length_of_mem v.property⟩
  invFun i := ⟨row[i.val], List.getElem_mem i.isLt⟩
  left_inv v := Subtype.ext (List.getElem_idxOf (List.idxOf_lt_length_of_mem v.property))
  right_inv i := Fin.ext (simple.idxOf_getElem (i := i.val) i.isLt)


structure PackedPathRanks (paths : I → List V) where
  rank : ∀ i, {v : V // v ∈ paths i} ≃ Fin (paths i).length
  adjacent : ∀ {a b x y} (h : OppositeNeighbors paths a b x y),
    (rank a ⟨y,h.2.1.2.1⟩).val = (rank a ⟨x,h.2.1.1⟩).val + 1

local notation "ListBefore" => SourceAudit.BeforeIn

/-- Order each path's incidences so that neighboring shared vertices occupy consecutive ranks. -/
theorem exists_packedPathRanks (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (ListBefore paths) 3) : Nonempty (PackedPathRanks paths) := by
  classical
  let pos (i : I) := pathPositions (paths i) (simple i)
  let link (i : I) (r s : Fin (paths i).length) : Prop :=
    ∃ j, OppositeNeighbors paths i j ((pos i).symm r).val ((pos i).symm s).val
  have ordered (i : I) {r s : Fin (paths i).length} (h : link i r s) : r < s := by
    obtain ⟨j,adjacent⟩ := h
    have left := congrArg Fin.val ((pos i).apply_symm_apply r)
    have right := congrArg Fin.val ((pos i).apply_symm_apply s)
    have before := adjacent.2.1.2.2
    change ((pos i) ((pos i).symm r)).val < ((pos i) ((pos i).symm s)).val at before
    rw [left, right] at before
    exact before
  have pred (i : I) {r s t : Fin (paths i).length} (rt : link i r t) (st : link i s t) : r = s := by
    obtain ⟨j,hj⟩ := rt
    obtain ⟨k,hk⟩ := st
    exact (pos i).symm.injective (Subtype.ext (oppositeNeighbors_in_unique free hj hk))
  have succ (i : I) {r s t : Fin (paths i).length} (rs : link i r s) (rt : link i r t) : s = t := by
    obtain ⟨j,hj⟩ := rs
    obtain ⟨k,hk⟩ := rt
    exact (pos i).symm.injective (Subtype.ext (oppositeNeighbors_out_unique free hj hk))
  have pack (i : I) := exists_chain_packing (link i) (ordered i) (pred i) (succ i)
  let index (i : I) := Classical.choose (pack i)
  refine ⟨⟨fun i => (pos i).trans (index i), fun {a b x y} h => ?_⟩⟩
  have arc : link a (pos a ⟨x,h.2.1.1⟩) (pos a ⟨y,h.2.1.2.1⟩) := by
    change ∃ j, OppositeNeighbors paths a j
      ((pos a).symm (pos a ⟨x,h.2.1.1⟩)).val ((pos a).symm (pos a ⟨y,h.2.1.2.1⟩)).val
    simpa only [Equiv.symm_apply_apply] using (show ∃ j, OppositeNeighbors paths a j x y from ⟨b,h⟩)
  exact Classical.choose_spec (pack a) arc

abbrev PackedBoundary (paths : I → List V) := Σ i, Fin (paths i).length

/-- A boundary between adjacent shared vertices is coupled to the reversed boundary. -/
def OppositeBoundary {paths : I → List V} (indexes : PackedPathRanks paths)
    (a b : PackedBoundary paths) : Prop :=
  ∃ x y, ∃ h : OppositeNeighbors paths a.fst b.fst x y,
    a.snd = indexes.rank a.fst ⟨x,h.2.1.1⟩ ∧ b.snd = indexes.rank b.fst ⟨y,h.2.2.1.1⟩

theorem OppositeBoundary.swap {paths : I → List V} (indexes : PackedPathRanks paths)
    (free : BridgeFree (ListBefore paths) 3) {a b : PackedBoundary paths}
    (paired : OppositeBoundary indexes a b) : OppositeBoundary indexes b a := by
  obtain ⟨x,y,h,first,second⟩ := paired
  exact ⟨y,x,oppositeNeighbors_swap free h,second,first⟩

theorem OppositeBoundary.unique {paths : I → List V} (indexes : PackedPathRanks paths)
    (free : BridgeFree (ListBefore paths) 3) {a b c : PackedBoundary paths}
    (ab : OppositeBoundary indexes a b) (ac : OppositeBoundary indexes a c) : b = c := by
  obtain ⟨x,y,xy,left,right⟩ := ab
  obtain ⟨x',z,xz,left',right'⟩ := ac
  have same := congrArg Subtype.val ((indexes.rank a.fst).injective (left.symm.trans left'))
  change x = x' at same
  subst x'
  have owner := oppositePartner_out_unique free xy.1 xz.1 xy.2.1 xz.2.1 xy.2.2.1 xz.2.2.1
  have endEq := oppositeNeighbors_out_unique free xy xz
  subst z
  obtain ⟨b,s⟩ := b
  obtain ⟨c,t⟩ := c
  change b = c at owner
  subst c
  exact congrArg (Sigma.mk b) (right.trans right'.symm)

/-- A partial involution on the finite cut positions. -/
noncomputable def oppositeCutPartner {paths : I → List V} (indexes : PackedPathRanks paths)
    (a : PackedBoundary paths) : Option (PackedBoundary paths) := by
  classical
  exact if h : ∃ b, OppositeBoundary indexes a b then some (Classical.choose h) else none

theorem oppositeCutPartner_eq {paths : I → List V} (indexes : PackedPathRanks paths)
    (free : BridgeFree (ListBefore paths) 3) {a b : PackedBoundary paths} :
    oppositeCutPartner indexes a = some b ↔ OppositeBoundary indexes a b := by
  classical
  unfold oppositeCutPartner
  split
  · rename_i h
    have paired := Classical.choose_spec h
    constructor
    · rintro equal
      exact (Option.some.inj equal) ▸ paired
    · exact fun other => congrArg some (OppositeBoundary.unique indexes free paired other)
  · rename_i h
    constructor
    · simp
    · exact fun paired => (h ⟨b,paired⟩).elim


end OnlineReachabilityPreservers
