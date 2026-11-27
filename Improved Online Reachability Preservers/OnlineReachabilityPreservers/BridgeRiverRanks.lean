import OnlineReachabilityPreservers.BackwardCopyReturns

/-! Project bridges in path pieces using the ranks of possible river endpoints. -/

namespace OnlineReachabilityPreservers

local notation "Before" => SourceAudit.BeforeIn

/-- A rank-increasing river cannot have a detour of the tested length
in the precedence graph without its own piece. -/
def NoCrossRankRiverDetour {J V : Type*} [DecidableEq J] [DecidableEq V] [Fintype J] [Fintype V]
    (pieces : J → List V) (rank : V → ℕ) (cutoff : ℕ) : Prop :=
  ∀ ⦃j x y⦄, Before pieces j x y → rank x < rank y →
    x ∉ reachIn (listPiecePrecedenceGraph (fun i => if i = j then [] else pieces i)) y (cutoff-1)

private theorem Bridge.same_rank_of_noCrossRankRiverDetour {J V : Type*}
    [DecidableEq J] [DecidableEq V] [Fintype J] [Fintype V]
    {pieces : J → List V} {rank : V → ℕ} {k d : ℕ}
    (b : Bridge (Before pieces) d) (small : d+2 ≤ k)
    (ordered : ∀ {i x y}, Before pieces i x y → rank x ≤ rank y)
    (noDetour : NoCrossRankRiverDetour pieces rank k) :
    ∀ i : Fin (d+2), rank (b.vertex i) = rank (b.vertex 0) := by
  let other (i : J) := if i = b.river then [] else pieces i
  let G := listPiecePrecedenceGraph other
  have inside (i : Fin (d+1)) : Edge G (b.vertex i.castSucc) (b.vertex i.succ) := by
    have notRiver := (b.river_ne_arc i).symm
    apply listPiecePrecedenceGraph_edge.mpr
    refine ⟨b.arc i,?_⟩
    simpa only [SourceAudit.BeforeIn,other,ite_eq_right notRiver] using b.arcStep i
  have found : b.vertex 0 ∈ reachIn G (b.vertex (Fin.last (d+1))) (d+1) :=
    reachIn_of_fin_steps b.vertex inside
  have reached := monotone_nat_of_le_succ (reachIn_subset_succ G (b.vertex (Fin.last (d+1))))
    (show d+1 ≤ k-1 by omega) found
  have mono : Monotone (rank ∘ b.vertex) := Fin.monotone_iff_le_succ.mpr (fun i => ordered (b.arcStep i))
  have endRank : rank (b.vertex (Fin.last (d+1))) ≤ rank (b.vertex 0) := by
    by_contra! increasing
    exact noDetour b.riverStep increasing reached
  intro i
  exact le_antisymm ((mono (Fin.le_last i)).trans endRank) (mono (Fin.zero_le i))

/-- With disjoint rank sets for pieces of the same row, any bridge whose
river and detour stay at one rank projects without merging its labels. -/
theorem localOrderAdmissible_of_noCrossRankRiverDetour {I J V : Type*}
    [LinearOrder I] [LinearOrder J] [DecidableEq V] [Fintype J] [Fintype V]
    {rows : I → List V} {pieces : J → List V} {k : ℕ} {half : Bool}
    (parent : J → I) (arrival : Monotone parent) (rank : V → ℕ)
    (steps : ∀ {i x y}, Before pieces i x y → Before rows (parent i) x y)
    (ordered : ∀ {i x y}, Before pieces i x y → rank x ≤ rank y)
    (apart : ∀ {i j x y}, i ≠ j → parent i = parent j → x ∈ pieces i → y ∈ pieces j → rank x ≠ rank y)
    (noDetour : NoCrossRankRiverDetour pieces rank k)
    (legal : localOrderAdmissible half k rows) : localOrderAdmissible half k pieces := by
  have projection {d : ℕ} (b : Bridge (Before pieces) d) (small : d+2 ≤ k) :
      ∃ old : Bridge (Before rows) d, old.river = parent b.river ∧ ∀ i, old.arc i = parent (b.arc i) := by
    have all := b.same_rank_of_noCrossRankRiverDetour small ordered noDetour
    have owner {i j : J} {a c : Fin (d+2)} (p : parent i = parent j)
        (x : b.vertex a ∈ pieces i) (y : b.vertex c ∈ pieces j) : i = j := by
      by_contra distinct
      exact apart distinct p x y ((all a).trans (all c).symm)
    let old : Bridge (Before rows) d := {
      vertex := b.vertex
      arc := parent ∘ b.arc
      river := parent b.river
      distinctVertices := b.distinctVertices
      distinctArcs := by
        intro a c eq
        exact b.distinctArcs (owner eq (b.arcStep a).1 (b.arcStep c).1)
      river_ne_arc := fun i eq => b.river_ne_arc i (owner eq b.riverStep.1 (b.arcStep i).1)
      riverStep := steps b.riverStep
      arcStep := fun i => steps (b.arcStep i) }
    exact ⟨old,rfl,fun _ => rfl⟩
  cases half
  · intro d small
    refine ⟨fun b => ?_⟩
    obtain ⟨old,_,_⟩ := projection b small
    exact (legal small).false old
  · intro d small b earlier
    obtain ⟨old,river,arc⟩ := projection b small
    have order := arrival earlier.le
    rw [← river,← arc] at order
    exact legal small old (order.lt_of_ne (old.river_ne_arc _).symm)

end OnlineReachabilityPreservers
