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

theorem Bridge.same_rank_of_noCrossRankRiverDetour {J V : Type*}
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


/-- Keep each piece's vertices with a given label in their original order. -/
def listPiecesWithLabel {J V A : Type*} [DecidableEq A]
    (pieces : J → List V) (label : V → A) (a : A) : J → List V :=
  fun j => (pieces j).filter fun x => decide (label x = a)

private theorem listPiecesWithLabel_before {J V A : Type*} [DecidableEq V] [DecidableEq A]
    {pieces : J → List V} {label : V → A} {a : A} {j : J} {x y : V}
    (simple : (pieces j).Nodup) (step : Before pieces j x y)
    (hx : label x = a) (hy : label y = a) : Before (listPiecesWithLabel pieces label a) j x y := by
  have first : x ∈ listPiecesWithLabel pieces label a j := by
    simp [listPiecesWithLabel,step.1,hx]
  have second : y ∈ listPiecesWithLabel pieces label a j := by
    simp [listPiecesWithLabel,step.2.1,hy]
  rcases listBefore_total first second (listBefore_ne step) with forward | backward
  · exact forward
  · have reverse := listBefore_of_sublist simple List.filter_sublist backward
    exact (lt_asymm step.2.2 reverse.2.2).elim

/-- If every bridge up to the cutoff stays within one label, checking the
restricted pieces suffices. The restrictions keep the original piece indices. -/
theorem localOrderAdmissible_of_label_restrictions {J V A : Type*}
    [LinearOrder J] [DecidableEq V] [DecidableEq A]
    {pieces : J → List V} {k : ℕ} {half : Bool}
    (simple : ∀ i, (pieces i).Nodup) (label : V → A)
    (inside : ∀ {d} (b : Bridge (Before pieces) d), d+2 ≤ k →
      ∀ i, label (b.vertex i) = label (b.vertex 0))
    (restrictions : ∀ a, localOrderAdmissible half k (listPiecesWithLabel pieces label a)) :
    localOrderAdmissible half k pieces := by
  have restrict {d : ℕ} (b : Bridge (Before pieces) d) (small : d+2 ≤ k) :
      ∃ b' : Bridge (Before (listPiecesWithLabel pieces label (label (b.vertex 0)))) d,
        b'.river = b.river ∧ b'.arc = b.arc := by
    have same := inside b small
    let b' : Bridge (Before (listPiecesWithLabel pieces label (label (b.vertex 0)))) d := {
      vertex := b.vertex
      arc := b.arc
      river := b.river
      distinctVertices := b.distinctVertices
      distinctArcs := b.distinctArcs
      river_ne_arc := b.river_ne_arc
      riverStep := listPiecesWithLabel_before (simple b.river) b.riverStep (same _) (same _)
      arcStep := fun i => listPiecesWithLabel_before (simple (b.arc i)) (b.arcStep i) (same _) (same _) }
    exact ⟨b',rfl,rfl⟩
  cases half
  · intro d small
    refine ⟨fun b => ?_⟩
    obtain ⟨b',_,_⟩ := restrict b small
    exact (restrictions _ small).false b'
  · intro d small b earlier
    obtain ⟨b',river,arcs⟩ := restrict b small
    exact restrictions _ small b' (by simpa only [river,arcs] using earlier)

/-- Test short returns in each separately restricted graph, provided
that a bridge through the cutoff must lie within a single label. -/
theorem localOrderAdmissible_of_labelwise_short_returns {I J V A : Type*}
    [LinearOrder I] [LinearOrder J] [DecidableEq V] [DecidableEq A] [Fintype J] [Fintype V]
    {rows : I → List V} {pieces : J → List V} {k : ℕ} {half : Bool}
    (simple : ∀ i, (pieces i).Nodup) (parent : J → I) (arrival : Monotone parent) (label : V → A)
    (steps : ∀ {i x y}, Before pieces i x y → Before rows (parent i) x y)
    (inside : ∀ {d} (b : Bridge (Before pieces) d), d+2 ≤ k →
      ∀ i, label (b.vertex i) = label (b.vertex 0))
    (separated : ∀ a, let inner := listPiecesWithLabel pieces label a
      ShortReturnSeparated (listPiecePrecedenceGraph inner) id rows inner parent (k-2))
    (legal : localOrderAdmissible half k rows) : localOrderAdmissible half k pieces := by
  apply localOrderAdmissible_of_label_restrictions simple label inside
  intro a
  have project {i x y} (step : Before (listPiecesWithLabel pieces label a) i x y) :
      Before rows (parent i) x y :=
    steps (listBefore_of_sublist (simple i) List.filter_sublist step)
  exact localOrderAdmissible_of_shortReturnSeparated parent arrival (fun {_ _ _} => project)
    (fun {i _ _} step => listPiecePrecedenceGraph_edge.mpr ⟨i,step⟩) (separated a) legal

/-- A monotone rank with no short detour for a rank-increasing river
permits short-return tests confined to each rank. -/
theorem localOrderAdmissible_of_rankwise_short_returns {I J V : Type*}
    [LinearOrder I] [LinearOrder J] [DecidableEq V] [Fintype J] [Fintype V]
    {rows : I → List V} {pieces : J → List V} {k : ℕ} {half : Bool}
    (simple : ∀ i, (pieces i).Nodup) (parent : J → I) (arrival : Monotone parent) (rank : V → ℕ)
    (steps : ∀ {i x y}, Before pieces i x y → Before rows (parent i) x y)
    (ordered : ∀ {i x y}, Before pieces i x y → rank x ≤ rank y)
    (noDetour : NoCrossRankRiverDetour pieces rank k)
    (separated : ∀ r, let inner := listPiecesWithLabel pieces rank r
      ShortReturnSeparated (listPiecePrecedenceGraph inner) id rows inner parent (k-2))
    (legal : localOrderAdmissible half k rows) : localOrderAdmissible half k pieces :=
  localOrderAdmissible_of_labelwise_short_returns simple parent arrival rank
    (fun {_ _ _} => steps)
    (fun b small => b.same_rank_of_noCrossRankRiverDetour small (fun {_ _ _} => ordered) noDetour)
    separated legal

end OnlineReachabilityPreservers
