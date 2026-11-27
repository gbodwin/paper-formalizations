import OnlineReachabilityPreservers.LocalOrderExtremal

/-! Bridge exclusion is preserved when path families meet at one vertex. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- If rows with different labels share only one possible vertex, every
arc of a bridge has the label of its river. A detour that changed labels
would have to visit the shared vertex at least twice. -/
theorem Bridge.arc_label_eq_of_single_shared_vertex {I V A : Type*}
    [DecidableEq V] [DecidableEq A] {rows : I → List V} {d : ℕ}
    (b : Bridge (Before rows) d) (label : I → A) (joint : V)
    (overlap : ∀ ⦃i j x⦄, label i ≠ label j → x ∈ rows i → x ∈ rows j → x = joint)
    (a : Fin (d+1)) : label (b.arc a) = label b.river := by
  let side := label b.river
  let off : Finset (Fin (d+1)) := univ.filter (fun i => label (b.arc i) ≠ side)
  by_contra! different
  have on : a ∈ off := mem_filter.mpr ⟨mem_univ _, different⟩
  have existsOff : off.Nonempty := ⟨a, on⟩
  let first := off.min' existsOff
  let last := off.max' existsOff
  have firstOff : label (b.arc first) ≠ side := (mem_filter.mp (min'_mem off existsOff)).2
  have lastOff : label (b.arc last) ≠ side := (mem_filter.mp (max'_mem off existsOff)).2
  have before (i : Fin (d+1)) (earlier : i < first) : label (b.arc i) = side := by
    by_contra! wrong
    exact earlier.not_ge (off.min'_le i (mem_filter.mpr ⟨mem_univ _, wrong⟩))
  have after (i : Fin (d+1)) (later : last < i) : label (b.arc i) = side := by
    by_contra! wrong
    exact later.not_ge (off.le_max' i (mem_filter.mpr ⟨mem_univ _, wrong⟩))
  have firstAt : b.vertex first.castSucc = joint := by
    rcases Fin.eq_zero_or_eq_succ first with zero | ⟨i, succ⟩
    · rw [zero] at firstOff ⊢
      exact overlap firstOff (b.arcStep 0).1 b.riverStep.1
    · have earlier := before i.castSucc (by rw [succ]; exact Fin.castSucc_lt_succ)
      rw [succ] at firstOff ⊢
      exact overlap (firstOff.trans_eq earlier.symm) (b.arcStep i.succ).1 (b.arcStep i.castSucc).2.1
  have lastAt : b.vertex last.succ = joint := by
    rcases Fin.eq_castSucc_or_eq_last last with ⟨i, previous⟩ | endArc
    · have later := after i.succ (by rw [previous]; exact Fin.castSucc_lt_succ)
      rw [previous] at lastOff ⊢
      exact overlap (lastOff.trans_eq later.symm) (b.arcStep i.castSucc).2.1 (b.arcStep i.succ).1
    · rw [endArc] at lastOff ⊢
      exact overlap lastOff (b.arcStep (Fin.last d)).2.1 b.riverStep.2.1
  have ordered : first ≤ last := off.min'_le _ (max'_mem off existsOff)
  have collision := b.distinctVertices (firstAt.trans lastAt.symm)
  have positions := congrArg Fin.val collision
  have firstBefore := Fin.le_iff_val_le_val.mp ordered
  simp only [Fin.val_castSucc, Fin.val_succ] at positions
  omega

/-- At any cutoff, one-vertex intersections between labelled row families
preserve full or half exclusion if it holds within every family. -/
theorem localOrderAdmissible_of_single_shared_vertex {I V A : Type*}
    [LinearOrder I] [DecidableEq V] [DecidableEq A] {rows : I → List V} {k : ℕ} {half : Bool}
    (label : I → A) (joint : V)
    (overlap : ∀ ⦃i j x⦄, label i ≠ label j → x ∈ rows i → x ∈ rows j → x = joint)
    (free : ∀ side : A, localOrderAdmissible half k (fun i => if label i = side then rows i else [])) :
    localOrderAdmissible half k rows := by
  let restrict {d : ℕ} (b : Bridge (Before rows) d) :
      Bridge (Before (fun i => if label i = label b.river then rows i else [])) d := by
    have steps {i x y} (same : label i = label b.river) (on : Before rows i x y) :
        Before (fun j => if label j = label b.river then rows j else []) i x y := by
      simpa only [SourceAudit.BeforeIn, ite_eq_left same] using on
    exact ⟨b.vertex, b.arc, b.river, b.distinctVertices, b.distinctArcs, b.river_ne_arc,
      steps rfl b.riverStep,
      fun a => steps (b.arc_label_eq_of_single_shared_vertex label joint overlap a) (b.arcStep a)⟩
  cases half
  · intro d size
    exact ⟨fun b => (free (label b.river) size).false (restrict b)⟩
  · intro d size b earlier
    exact free (label b.river) size (restrict b) earlier

end OnlineReachabilityPreservers
