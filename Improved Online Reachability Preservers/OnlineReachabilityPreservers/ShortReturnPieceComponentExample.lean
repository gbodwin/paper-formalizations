import OnlineReachabilityPreservers.HalfFiveTerminalPacking
import OnlineReachabilityPreservers.ShortReturnPieceComponents

/-! Three independent backward pairs fit at the original path width. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset

/-- A long row with three independent backward pairs and eight unused
arrival labels. Its frozen path width is four. -/
def shortReturnGroupExampleRows : Fin 12 → List (Fin 6) :=
  ![[0,1,2,3,4,5], [1,0], [3,2], [5,4], [], [], [], [], [], [], [], []]

theorem shortReturnGroupExample_mass_simple :
    (∑ i, (shortReturnGroupExampleRows i).length) = 12 ∧
      ∀ i, (shortReturnGroupExampleRows i).Nodup := by
  decide +kernel

private theorem shortReturnGroupExample_zero_increases :
    ∀ (x y : Fin 6), BeforeIn shortReturnGroupExampleRows 0 x y → x < y := by
  unfold BeforeIn
  decide +kernel

private theorem shortReturnGroupExample_other_decreases :
    ∀ (r : Fin 12) (x y : Fin 6), r ≠ 0 → BeforeIn shortReturnGroupExampleRows r x y → y < x := by
  unfold BeforeIn
  decide +kernel

private instance (r : Fin 12) (s t : Fin 6) : Decidable (BeforeIn shortReturnGroupExampleRows r s t) := by
  unfold BeforeIn
  infer_instance

set_option maxRecDepth 16384 in
private theorem shortReturnGroupExample_reverse_cut :
    ∀ (r i : Fin 12) (t x y : Fin 6), r ≠ 0 → r ≠ i →
      (∃ s : Fin 6, BeforeIn shortReturnGroupExampleRows r s t) →
      BeforeIn shortReturnGroupExampleRows i x y → t < x → t < y := by
  decide +kernel

/-- A detour for the long row can only move backward. Any other river
has a cut which only that river crosses backward. -/
theorem shortReturnGroupExampleRows_fullFree (cutoff : ℕ) :
    BridgeFree (BeforeIn shortReturnGroupExampleRows) cutoff := by
  intro s _
  refine ⟨fun b => ?_⟩
  by_cases long : b.river = 0
  · have forward := shortReturnGroupExample_zero_increases _ _ (long ▸ b.riverStep)
    have decreasing (j : Fin (s+2)) : b.vertex j ≤ b.vertex 0 := by
      induction j using Fin.induction with
      | zero => exact le_rfl
      | succ j ih =>
        have nonzero : b.arc j ≠ 0 := fun eq => b.river_ne_arc j (long.trans eq.symm)
        exact (shortReturnGroupExample_other_decreases _ _ _ nonzero (b.arcStep j)).le.trans ih
    exact forward.not_ge (decreasing _)
  · let endVertex := b.vertex (Fin.last (s+1))
    have reverse := shortReturnGroupExample_other_decreases _ _ _ long b.riverStep
    have stays (j : Fin (s+2)) : endVertex < b.vertex j := by
      induction j using Fin.induction with
      | zero => exact reverse
      | succ j ih =>
        exact shortReturnGroupExample_reverse_cut _ _ _ _ _ long (b.river_ne_arc j)
          ⟨b.vertex 0, b.riverStep⟩ (b.arcStep j) ih
    exact (lt_irrefl _) (stays (Fin.last (s+1)))

abbrev ShortReturnGroupExampleVertex := ListVertexBlockIndex shortReturnGroupExampleRows 8

abbrev shortReturnGroupExampleCopies := splitListVertices shortReturnGroupExampleRows 8

private theorem shortReturnGroupExample_copy_injective :
    Function.Injective (fun v : ShortReturnGroupExampleVertex => v.fst) := by
  unfold Function.Injective
  decide +kernel

theorem shortReturnGroupExampleCopies_fullFree (cutoff : ℕ) :
    BridgeFree (BeforeIn shortReturnGroupExampleCopies) cutoff := by
  intro s small
  refine ⟨fun b => (shortReturnGroupExampleRows_fullFree cutoff small).false
    (b.mapVertices (fun v => v.fst) shortReturnGroupExample_copy_injective
      (fun i _ _ step => splitListVertices_step (shortReturnGroupExample_mass_simple.2 i) step))⟩

private def shortReturnGroupExamplePair (v : ShortReturnGroupExampleVertex) : ℕ := v.fst.val / 2

private theorem shortReturnGroupExamplePair_mono :
    ∀ (i : Fin 12) (x y : ShortReturnGroupExampleVertex),
      BeforeIn shortReturnGroupExampleCopies i x y → shortReturnGroupExamplePair x ≤ shortReturnGroupExamplePair y := by
  unfold BeforeIn
  decide +kernel

private theorem shortReturnGroupExamplePair_small :
    ∀ (x : ShortReturnGroupExampleVertex),
      (univ.filter fun y => shortReturnGroupExamplePair y = shortReturnGroupExamplePair x).card ≤ 2 := by
  decide +kernel

/-- Each connected group lies in one of the three pairs at every cutoff. -/
theorem shortReturnGroupExample_component_room (k : ℕ) (i : Fin 12) (x : ShortReturnGroupExampleVertex) :
    (shortReturnRowComponent shortReturnGroupExampleCopies k i x).card ≤ 2 := by
  let G := listPiecePrecedenceGraph shortReturnGroupExampleCopies
  have returnMono {a b : ShortReturnGroupExampleVertex} (back : Reach G a b) :
      shortReturnGroupExamplePair a ≤ shortReturnGroupExamplePair b := by
    induction back with
    | refl => exact le_rfl
    | tail _ e ih =>
      obtain ⟨j, step⟩ := listPiecePrecedenceGraph_edge.mp e
      exact ih.trans (shortReturnGroupExamplePair_mono j _ _ step)
  have equal {a b : ShortReturnGroupExampleVertex}
      (step : BeforeIn shortReturnGroupExampleCopies i a b) (back : b ∈ reachIn G a (k-3)) :
      shortReturnGroupExamplePair a = shortReturnGroupExamplePair b :=
    le_antisymm (shortReturnGroupExamplePair_mono i _ _ step) (returnMono (reachIn_sound back))
  have equality {a b : ShortReturnGroupExampleVertex}
      (e : Edge (shortReturnRowGraph shortReturnGroupExampleCopies k i) a b) :
      shortReturnGroupExamplePair a = shortReturnGroupExamplePair b := by
    rcases shortReturnRowGraph_edge.mp e with left | right
    · exact equal left.1 left.2
    · exact (equal right.1 right.2).symm
  have subset : shortReturnRowComponent shortReturnGroupExampleCopies k i x ⊆
      univ.filter (fun y => shortReturnGroupExamplePair y = shortReturnGroupExamplePair x) := by
    intro y on
    have reach := (componentLabel_eq.mp (mem_filter.mp on).2).1
    refine mem_filter.mpr ⟨mem_univ y, ?_⟩
    clear on
    induction reach with
    | refl => rfl
    | tail _ e ih => exact ih.trans (equality e)
  exact (card_le_card subset).trans (shortReturnGroupExamplePair_small x)

private theorem shortReturnGroupExample_all_on_long :
    ∀ x : ShortReturnGroupExampleVertex, x ∈ shortReturnGroupExampleCopies 0 := by
  decide +kernel

private def shortReturnGroupExampleReturns (x y : ShortReturnGroupExampleVertex) : Prop :=
  (BeforeIn shortReturnGroupExampleCopies 0 x y ∧
    y ∈ reachIn (listPiecePrecedenceGraph shortReturnGroupExampleCopies) x 1) ∨
  (BeforeIn shortReturnGroupExampleCopies 0 y x ∧
    x ∈ reachIn (listPiecePrecedenceGraph shortReturnGroupExampleCopies) y 1)

private instance (x y : ShortReturnGroupExampleVertex) : Decidable (shortReturnGroupExampleReturns x y) := by
  unfold shortReturnGroupExampleReturns BeforeIn
  infer_instance

private theorem shortReturnGroupExample_all_short_return :
    ∀ x : ShortReturnGroupExampleVertex, ∃ y : ShortReturnGroupExampleVertex, shortReturnGroupExampleReturns x y := by
  decide +kernel

/-- A single block for all protected endpoints would require six slots. -/
theorem shortReturnGroupExample_single_block_fails :
    4 < (shortReturnProtectedVertices shortReturnGroupExampleCopies 1 0).card := by
  classical
  have all : shortReturnProtectedVertices shortReturnGroupExampleCopies 1 0 = univ := by
    ext x
    refine ⟨fun _ => mem_univ _, fun _ => ?_⟩
    exact mem_filter.mpr ⟨List.mem_toFinset.mpr (shortReturnGroupExample_all_on_long x),
      shortReturnGroupExample_all_short_return x⟩
  rw [all, card_univ]
  decide +kernel

/-- At the same original widths, grouping the three pairs separately
gives the frozen quarter-mass bound at every full cutoff. -/
theorem shortReturnGroupExample_frozen (cutoff : ℕ) :
    ∃ n' ≤ 6, ∃ p' ≤ 12, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (BeforeIn clean) cutoff ∧
      12 ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ 12 ∧ frozenListCaps 6 12 12 clean := by
  have mass := shortReturnGroupExample_mass_simple.1
  have dense : 6 ≤ ∑ i, (shortReturnGroupExampleRows i).length := by rw [mass]; decide
  have long : 12 ≤ ∑ i, (shortReturnGroupExampleRows i).length := mass.ge
  have result := regularization_list_frozen_of_short_return_component_room (half := false) (k := cutoff)
    shortReturnGroupExampleRows shortReturnGroupExample_mass_simple.2 (by decide) (by decide) dense long
    (by
      dsimp only
      rw [mass]
      exact shortReturnGroupExampleCopies_fullFree cutoff)
    (by
      dsimp only
      rw [mass]
      intro i x _
      exact (shortReturnGroupExample_component_room cutoff i x).trans (by decide))
  simpa only [mass, localOrderAdmissible, Bool.false_eq_true, ite_false] using result

end OnlineReachabilityPreservers.SourceAudit
