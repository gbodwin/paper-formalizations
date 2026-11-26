import OnlineReachabilityPreservers.FrozenHalfFourConflicts

/-! Repair opposite conflicts on contiguous width pieces through full cutoff six. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "Before" => SourceAudit.BeforeIn

section Conflicts

variable {I J V : Type*} [DecidableEq V]

/-- The two cut incidences at the later endpoint of a split opposite pair. -/
def CrossedOppositeConflict (paths : I → List V) (pieces : J → List V)
    (parent : J → I) (a b : J × V) : Prop :=
  a.2 = b.2 ∧
    ∃ (early : J) (v : V), early ≠ a.1 ∧ parent early = parent a.1 ∧ parent a.1 ≠ parent b.1 ∧
      v ∈ pieces early ∧ a.2 ∈ pieces a.1 ∧ Before paths (parent a.1) v a.2 ∧ Before pieces b.1 b.2 v

theorem CrossedOppositeConflict.source_mem {paths : I → List V} {pieces : J → List V} {parent : J → I}
    {a b : J × V} (edge : CrossedOppositeConflict paths pieces parent a b) : a.2 ∈ pieces a.1 :=
  edge.2.elim fun _ h => h.elim fun _ h => h.2.2.2.2.1

theorem CrossedOppositeConflict.target_mem {paths : I → List V} {pieces : J → List V} {parent : J → I}
    {a b : J × V} (edge : CrossedOppositeConflict paths pieces parent a b) : b.2 ∈ pieces b.1 :=
  edge.2.elim fun _ h => h.elim fun _ h => h.2.2.2.2.2.2.1

theorem CrossedOppositeConflict.ne {paths : I → List V} {pieces : J → List V} {parent : J → I}
    {a b : J × V} (edge : CrossedOppositeConflict paths pieces parent a b) : a ≠ b := by
  intro eq
  obtain ⟨_,_,_,_,_,apart,_,_,_,_⟩ := edge
  exact apart (congrArg (fun q : J × V => parent q.1) eq)

private theorem reverse_predecessor_unique [LinearOrder I] {paths : I → List V}
    (free : BridgeFree (Before paths) 3) {a b c : I} (ab : a ≠ b) (ac : a ≠ c)
    {u v w : V} (uw : Before paths a u w) (vw : Before paths a v w)
    (wu : Before paths b w u) (wv : Before paths c w v) : b = c := by
  by_contra different
  by_cases eq : u = v
  · exact no_parallel_list_steps free.halfFree (by decide) different (eq ▸ wu) wv
  rcases listBefore_total uw.1 vw.1 eq with uv | vu
  · exact (free (by decide)).false (threeListBridge ab.symm (fun h => different h.symm) ac.symm wu uv wv)
  · exact (free (by decide)).false (threeListBridge ac.symm different ab.symm wv vu wu)

private theorem reverse_successor_unique [LinearOrder I] {paths : I → List V}
    (free : BridgeFree (Before paths) 3) {a b c : I} (ab : a ≠ b) (ac : a ≠ c)
    {u v w : V} (wu : Before paths a w u) (wv : Before paths a w v)
    (uw : Before paths b u w) (vw : Before paths c v w) : b = c := by
  by_contra different
  by_cases eq : u = v
  · exact no_parallel_list_steps free.halfFree (by decide) different (eq ▸ uw) vw
  rcases listBefore_total wu.2.1 wv.2.1 eq with uv | vu
  · exact (free (by decide)).false (threeListBridge ac ab.symm different uv vw uw)
  · exact (free (by decide)).false (threeListBridge ab ac.symm (fun h => different h.symm) vu uw vw)

/-- Full-three exclusion makes every incidence the source of at most one opposite cut. -/
theorem CrossedOppositeConflict.out_unique [LinearOrder I] {paths : I → List V} {pieces : J → List V}
    {parent : J → I} (free : BridgeFree (Before paths) 3)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y)
    (apart : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    {a b c : J × V} (ab : CrossedOppositeConflict paths pieces parent a b)
    (ac : CrossedOppositeConflict paths pieces parent a c) : b = c := by
  have sameVertex : b.2 = c.2 := ab.1.symm.trans ac.1
  have beforeB := ab.target_mem
  have beforeC := ac.target_mem
  obtain ⟨eqB,_,u,_,_,neqB,_,_,uw,wu⟩ := ab
  obtain ⟨eqC,_,v,_,_,neqC,_,_,vw,wv⟩ := ac
  have labels := reverse_predecessor_unique free neqB neqC uw vw (eqB.symm ▸ steps wu) (eqC.symm ▸ steps wv)
  have samePiece : b.1 = c.1 := by
    by_contra separate
    exact apart separate labels beforeB (sameVertex.symm ▸ beforeC)
  exact Prod.ext samePiece sameVertex

/-- Full-three exclusion also makes every incidence the target of at most one opposite cut. -/
theorem CrossedOppositeConflict.in_unique [LinearOrder I] {paths : I → List V} {pieces : J → List V}
    {parent : J → I} (free : BridgeFree (Before paths) 3)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y)
    (apart : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    {a b c : J × V} (ab : CrossedOppositeConflict paths pieces parent a b)
    (cb : CrossedOppositeConflict paths pieces parent c b) : a = c := by
  have sameVertex : a.2 = c.2 := ab.1.trans cb.1.symm
  have beforeA := ab.source_mem
  have beforeC := cb.source_mem
  obtain ⟨eqA,_,u,_,_,neqA,_,_,uw,wu⟩ := ab
  obtain ⟨eqC,_,v,_,_,neqC,_,_,vw,wv⟩ := cb
  have labels := reverse_successor_unique free neqA.symm neqC.symm (steps wu) (steps wv) (eqA ▸ uw) (eqC ▸ vw)
  have samePiece : a.1 = c.1 := by
    by_contra separate
    exact apart separate labels beforeA (sameVertex.symm ▸ beforeC)
  exact Prod.ext samePiece sameVertex

/-- Covering the opposite-cut conflicts on ordered pieces preserves full
exclusion through size six. -/
theorem eraseOppositeCutConflicts_fullFree [LinearOrder I] {paths : I → List V} {pieces : J → List V}
    {parent : J → I} (free : BridgeFree (Before paths) 6)
    (simple : ∀ i, (pieces i).Nodup)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y)
    (apart : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (ordered : ∀ {i j}, i ≠ j → parent i = parent j →
      (∀ ⦃x y⦄, x ∈ pieces i → y ∈ pieces j → Before paths (parent i) x y) ∨
      (∀ ⦃x y⦄, x ∈ pieces j → y ∈ pieces i → Before paths (parent i) x y))
    (deleted : Finset (J × V))
    (cover : ∀ {a b}, CrossedOppositeConflict paths pieces parent a b → a ∈ deleted ∨ b ∈ deleted) :
    BridgeFree (Before (erasePieceIncidences pieces deleted)) 6 := by
  let clean := erasePieceIncidences pieces deleted
  have containing {i : J} {x : V} (on : x ∈ clean i) : x ∈ pieces i :=
    (mem_erasePieceIncidences.mp on).1
  have lift {i : J} {x y : V} (step : Before clean i x y) : Before pieces i x y :=
    listBefore_of_sublist (simple i) (erasePieceIncidences_sublist pieces deleted i) step
  have liftOld {i : J} {x y : V} (step : Before clean i x y) : Before paths (parent i) x y :=
    steps (lift step)
  have cleanApart {i j : J} {x : V} (neq : i ≠ j) (same : parent i = parent j)
      (left : x ∈ clean i) (right : x ∈ clean j) : False :=
    apart neq same (containing left) (containing right)
  have together {i j q : J} {x y : V} (same : parent i = parent j) (neq : parent i ≠ parent q)
      (forward : Before paths (parent i) x y) (reverse : Before clean q y x)
      (left : x ∈ clean i) (right : y ∈ clean j) : i = j := by
    by_contra separate
    have conflict : CrossedOppositeConflict paths pieces parent (j,y) (q,y) :=
      ⟨rfl,i,x,separate,same,same ▸ neq,containing left,containing right,same ▸ forward,lift reverse⟩
    exact (cover conflict).elim (mem_erasePieceIncidences.mp right).2 (mem_erasePieceIncidences.mp reverse.1).2
  have cleanOrdered {i j : J} (neq : i ≠ j) (same : parent i = parent j) :
      (∀ ⦃x y⦄, x ∈ clean i → y ∈ clean j → Before paths (parent i) x y) ∨
      (∀ ⦃x y⦄, x ∈ clean i → y ∈ clean j → Before paths (parent i) y x) := by
    rcases ordered neq same with forward | backward
    · exact Or.inl (fun {_ _} a b => forward (containing a) (containing b))
    · exact Or.inr (fun {_ _} a b => backward (containing b) (containing a))
  intro d cutoff
  refine ⟨fun bridge => ?_⟩
  by_cases short : d ≤ 3
  · exact (free cutoff).false (listBridge_after_opposite_safe_split_through_five parent
      (fun {_ _ _} => liftOld) (fun {_ _ _} => cleanApart)
      (fun _ {_ _ _ _} diff left right => no_parallel_list_steps free.halfFree (by decide) diff left right)
      (fun _ {_ _ _ _ _} => together) short bridge)
  · have size : d = 4 := by omega
    subst d
    exact (free (by decide)).false (listBridge_after_contiguous_opposite_safe_split_six parent
      (fun {_ _ _} => liftOld) (fun {_ _ _} => cleanApart) (fun {_ _ _ _ _} => together)
      (fun {_ _} => cleanOrdered) (fun _ small => free (small.trans (by decide))) bridge)

end Conflicts

end OnlineReachabilityPreservers
