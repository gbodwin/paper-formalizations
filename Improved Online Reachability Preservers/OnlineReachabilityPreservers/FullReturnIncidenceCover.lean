import OnlineReachabilityPreservers.FullReturnRadius
import OnlineReachabilityPreservers.FrozenHalfFourConflicts
import OnlineReachabilityPreservers.LocalSourceCounting

/-! Repair short crossed returns by erasing their labeled incidences. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

variable {V I J : Type*}

/-- A set of piece incidences meets every crossed return of the tested
radius. It may meet either endpoint on the repeated parent's pieces or
an incidence used by any of the return steps. -/
def CrossedParentReturnIncidenceCover [DecidableEq V] (parents : I → List V) (pieces : J → List V)
    (parent : J → I) (radius : ℕ) (deleted : Finset (J × V)) : Prop :=
  ∀ ⦃i j : J⦄ {d : ℕ}, i ≠ j → parent i = parent j → d ≤ radius →
    ∀ (v : Fin (d+1) → V) (a : Fin d → J),
      (∀ t, parent i ≠ parent (a t)) → Function.Injective (parent ∘ a) →
      v 0 ∈ pieces i → v (Fin.last d) ∈ pieces j →
      Before parents (parent i) (v (Fin.last d)) (v 0) →
      (∀ t, Before pieces (a t) (v t.castSucc) (v t.succ)) →
      (i,v 0) ∈ deleted ∨ (j,v (Fin.last d)) ∈ deleted ∨
        ∃ t, (a t,v t.castSucc) ∈ deleted ∨ (a t,v t.succ) ∈ deleted

/-- An incidence cover is equivalent to removing every crossed return
in the retained pieces, with the pre-split parent comparisons fixed. -/
theorem noCrossedParentReturnUpTo_erasePieceIncidences_iff [LinearOrder V]
    {parents : I → List V} {pieces : J → List V} {parent : J → I} {radius : ℕ}
    (simple : ∀ i, (pieces i).Nodup) (deleted : Finset (J × V)) :
    NoCrossedParentReturnUpTo parents (erasePieceIncidences pieces deleted) parent radius ↔
      CrossedParentReturnIncidenceCover parents pieces parent radius deleted := by
  let kept := erasePieceIncidences pieces deleted
  have sub := erasePieceIncidences_sublist pieces deleted
  constructor
  · intro noReturn i j d apart same short v a other injective first last backward along
    by_contra missed
    have atFirst : v 0 ∈ kept i := mem_erasePieceIncidences.mpr ⟨first,fun hit => missed (Or.inl hit)⟩
    have atLast : v (Fin.last d) ∈ kept j :=
      mem_erasePieceIncidences.mpr ⟨last,fun hit => missed (Or.inr (Or.inl hit))⟩
    have steps (t : Fin d) : Before kept (a t) (v t.castSucc) (v t.succ) := by
      have atStart : v t.castSucc ∈ kept (a t) :=
        mem_erasePieceIncidences.mpr ⟨(along t).1,fun hit => missed (Or.inr (Or.inr ⟨t,Or.inl hit⟩))⟩
      have atEnd : v t.succ ∈ kept (a t) :=
        mem_erasePieceIncidences.mpr ⟨(along t).2.1,fun hit => missed (Or.inr (Or.inr ⟨t,Or.inr hit⟩))⟩
      exact (listBefore_sublist_iff (simple (a t)) (sub (a t)) atStart atEnd).mpr (along t)
    exact noReturn apart same short v a other injective atFirst atLast backward steps
  · intro cover i j d apart same short v a other injective first last backward along
    have atFirst := mem_erasePieceIncidences.mp first
    have atLast := mem_erasePieceIncidences.mp last
    have steps (t : Fin d) := listBefore_of_sublist (simple (a t)) (sub (a t)) (along t)
    rcases cover apart same short v a other injective atFirst.1 atLast.1 backward steps with
      hit | hit | ⟨t, hit | hit⟩
    · exact atFirst.2 hit
    · exact atLast.2 hit
    · exact (mem_erasePieceIncidences.mp (along t).1).2 hit
    · exact (mem_erasePieceIncidences.mp (along t).2.1).2 hit

/-- At a full cutoff of at least seven, covering the crossed returns
at radius `cutoff-5` repairs a disjoint order-preserving split. -/
theorem fullBridgeFree_after_crossed_parent_return_erasure [LinearOrder V] [LinearOrder I]
    {parents : I → List V} {pieces : J → List V} {cutoff : ℕ} (parent : J → I)
    (simple : ∀ i, (pieces i).Nodup)
    (steps : ∀ {i x y}, Before pieces i x y → Before parents (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (free : BridgeFree (Before parents) cutoff) (large : 7 ≤ cutoff) (deleted : Finset (J × V))
    (cover : CrossedParentReturnIncidenceCover parents pieces parent (cutoff-5) deleted) :
    BridgeFree (Before (erasePieceIncidences pieces deleted)) cutoff :=
  fullBridgeFree_of_short_parent_returns parent
    (fun {i _ _} forward => steps (listBefore_of_sublist (simple i) (erasePieceIncidences_sublist pieces deleted i) forward))
    (fun {_ _ _} apart same first last => disjoint apart same
      (mem_erasePieceIncidences.mp first).1 (mem_erasePieceIncidences.mp last).1)
    ((noCrossedParentReturnUpTo_erasePieceIncidences_iff simple deleted).mpr cover) free large

end OnlineReachabilityPreservers
