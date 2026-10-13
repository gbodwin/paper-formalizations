import DirectedFlowCutGap.PackingIterationSpecification

namespace DirectedFlowCutGap.PackingIteration
open BinaryArithmetic BinaryRational BinaryFractionalRows

theorem bounded_mono {x : Fraction} {A B : ℕ} (h : StoredBounded x A) (le : A≤B) :
    StoredBounded x B := ⟨h.1.trans le,h.2.trans le⟩

/-- The update factor depends only on the original capacity fields. Consequently
stored weight width grows additively per iteration, even without reduction. -/
theorem entry_width (ci amount y : Fraction) (B W : ℕ)
    (hc : StoredBounded ci B) (ha : StoredBounded amount B) (hy : StoredBounded y W) :
    StoredBounded (PackingEntry.result ci amount y) (W+2*B+8) := by
  have factor := (PackingEntry.widths ci amount ci B hc ha hc).2.2.1
  have hm := mul_stored_bounded (stored_raw_bound hy) (stored_raw_bound factor)
  simpa only [PackingEntry.result,show W+(2*B+7)+1=W+2*B+8 by omega] using hm

theorem update_width (amount : Fraction) (cs ys : List Fraction) (mask : List Bool) (B W : ℕ)
    (amt : StoredBounded amount B) (cap : ∀ x∈cs,StoredBounded x B)
    (weights : ∀ x∈ys,StoredBounded x W) :
    ∀ z∈PackingUpdateRow.result amount cs ys mask,StoredBounded z (W+2*B+8) := by
  induction cs generalizing ys mask with
  | nil => simp [PackingUpdateRow.result]
  | cons ci cs ih =>
    cases ys with
    | nil => simp [PackingUpdateRow.result]
    | cons y ys =>
      cases mask with
      | nil => simp [PackingUpdateRow.result]
      | cons enabled fs =>
        intro z hz
        simp only [PackingUpdateRow.result,List.mem_cons] at hz
        rcases hz with rfl | hz
        · cases enabled with
          | false => exact bounded_mono (weights y List.mem_cons_self) (by omega)
          | true => exact entry_width ci amount y B W (cap ci List.mem_cons_self) amt (weights y List.mem_cons_self)
        · exact ih ys fs (fun z hz => cap z (List.mem_cons_of_mem _ hz))
            (fun z hz => weights z (List.mem_cons_of_mem _ hz)) z hz

theorem loads_width (amount : Fraction) (ys : List Fraction) (mask : List Bool) (B W : ℕ)
    (amt : StoredBounded amount B) (loads : ∀ x∈ys,StoredBounded x W) :
    ∀ z∈PackingLoadRow.result amount ys mask,StoredBounded z (W+B+3) := by
  induction ys generalizing mask with
  | nil => simp [PackingLoadRow.result]
  | cons y ys ih =>
    cases mask with
    | nil => simp [PackingLoadRow.result]
    | cons enabled fs =>
      intro z hz
      simp only [PackingLoadRow.result,List.mem_cons] at hz
      rcases hz with rfl | hz
      · have hb := add_stored_bounded (stored_raw_bound (loads y List.mem_cons_self))
          (stored_raw_bound (PackingLoadRow.operand_width enabled amount B amt))
        simpa only [PackingLoadEntry.result,show W+(B+1)+2=W+B+3 by omega] using hb
      · exact ih fs (fun z hz => loads z (List.mem_cons_of_mem _ hz)) z hz
end DirectedFlowCutGap.PackingIteration
