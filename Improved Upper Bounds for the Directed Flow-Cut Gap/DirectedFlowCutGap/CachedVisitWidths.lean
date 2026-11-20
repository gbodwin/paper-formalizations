import DirectedFlowCutGap.PaidCacheTrace

/-! The bounds apply to operands of completed instructions in a reached
cached state. No assumptions about operations on unreachable inputs enter
these bounds. -/
namespace DirectedFlowCutGap.PaidCacheTrace

open BinaryArithmetic ImmutableReferenceSimulation EncodedSequenceAccess
open CachedReferenceExecution (FastState)
open TotalGuardedPackedExecution (Next)
open CachedHeapWidths (ReadOperands readerWidth attempt_read_inbounds attempt_read_width)
open CachedControllerStorage (AppendOperands attempt_append_width)

/-- Every completed heap read uses the indexed branch. Both read and append
operands fit widths obtained from the very same reached packed state. -/
theorem Walk.next_operands {C H B steps cells copies limit : ℕ} {p : Program C}
    {initial current next : FastState C} (before : Walk p initial steps cells copies current)
    (input : initial.freeze.Bounded H B) (within : steps≤limit) (ran : Next p next current) :
    let addr (src : Reg) := (copyBits (current.registers.get src)).1
    match p current.pc with
    | .branch src _ _ _ _ | .field _ src _ _ | .emit src _ =>
        value (addr src)<current.store.cells.size ∧
          ReadOperands current.store (addr src) (readerWidth (H+limit) (B+limit))
    | .make _ recipe _ =>
        AppendOperands current.store (recipe.cell current.registers) (readerWidth (H+limit+1) (B+limit))
    | .request _ _ =>
        AppendOperands current.store (.flag (current.source.headD false)) (readerWidth (H+limit+1) (B+limit))
    | _ => True := by
  have reached := (before.bounded input).1.mono (Nat.add_le_add_left within H) (Nat.add_le_add_left within B)
  obtain ⟨_,_,performed,_⟩ := ran
  have valid := attempt_read_inbounds p current performed
  have loads := attempt_read_width p current reached
  have stores := attempt_append_width p current reached
  cases executed : p current.pc <;> simp only [executed] at valid loads stores ⊢
  all_goals first | exact True.intro | exact stores | exact ⟨valid,loads⟩

end DirectedFlowCutGap.PaidCacheTrace
