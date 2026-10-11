import DirectedFlowCutGap.BinaryPackingTrees

/-! Explicit callback-count multiplication for the actual cache-aware outer
controller. The callback budget must hold on every row, not only good-quality
answers. The concrete heavy provider has such a uniform bound separately. -/
namespace DirectedFlowCutGap.BinaryPackingBudget
set_option backward.isDefEq.respectTransparency false
open BinaryArithmetic BinaryFractionalRows BinaryApproximatePacking
open FiniteDrawTrees LazyFairBitTrees
variable {n Q : ℕ} (c : Row n) (columns : Set (FractionalCover.Column n))
variable (draw : Oracle FiniteDrawTrees.Tree c columns)
variable (hdraw : ∀ row,Within Q (draw row))

include hdraw in
theorem advance_within (p : Pending c columns) (s : BinaryFractionalCore.State n) :
    Within Q (advance c columns draw p s) := by
  unfold advance
  dsimp only []
  split_ifs
  · exact .pure _ _
  · cases p with
    | some q => exact .pure _ _
    | none => exact within_bind (hdraw _) _ (r := 0) (fun _ => .pure 0 _)

include hdraw in
theorem runFrom_within (fuel : Bits) (p : Pending c columns)
    (s : BinaryFractionalCore.State n) : Within (value fuel*Q) (runFromM c columns draw fuel p s) := by
  have aux : ∀ t,∀ f : Bits,value f=t → ∀ p s,Within (value f*Q) (runFromM c columns draw f p s) := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro f hf p s
      rw [runFromM]
      dsimp only []
      split_ifs with hz
      · exact .pure _ _
      · have hp := (predecessor_spec f).1
        have hpos : 0<value f := Nat.pos_of_ne_zero
          (fun he => hz ((isZero_spec f).1.mpr he))
        have hi := ih (value (predecessor f).1) (by rw [hp,←hf];omega)
          (predecessor f).1 rfl
        have he : value f*Q=Q+value (predecessor f).1*Q := by
          have hv : value f=value (predecessor f).1+1 := by omega
          rw [hv];ring
        rw [he]
        apply within_bind (advance_within c columns draw hdraw p s)
        intro next
        exact within_bind (hi next.pending next.state) _ (r := 0) (fun _ => .pure 0 _)
  exact aux (value fuel) fuel rfl p s

include hdraw in
theorem run_within (delta : BinaryRational.Fraction) (fuel : Bits) :
    Within ((value fuel+1)*Q) (runM c columns draw delta fuel) := by
  have he : (value fuel+1)*Q=Q+value fuel*Q := by ring
  rw [he]
  apply within_bind (hdraw _)
  intro first
  exact within_bind (runFrom_within c columns draw hdraw fuel _ _) _ (r := 0) (fun _ => .pure 0 _)

include hdraw in
theorem solve_within :
    Within ((value (BinaryFractionalCore.parameters (BinaryFractionalCore.dimension c).1).fuel+1)*Q)
      (solveInputM c columns draw) :=
  within_bind (run_within c columns draw hdraw _ _) _ (r := 0) (fun _ => .pure 0 _)

end DirectedFlowCutGap.BinaryPackingBudget
