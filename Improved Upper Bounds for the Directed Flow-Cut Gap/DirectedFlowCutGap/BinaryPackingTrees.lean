import DirectedFlowCutGap.BinaryApproximatePacking
import DirectedFlowCutGap.MonadicBitSampler

/-! The existing cache-aware outer packing controller interpreted through its
actual callback tree. Every branch, physical answer and operation field is
retained. A structural finite-tree budget exists separately; no polynomial
bit budget or cost of constructing such a budget is asserted here. -/
namespace DirectedFlowCutGap.BinaryPackingTrees
set_option backward.isDefEq.respectTransparency false
open BinaryArithmetic BinaryFractionalRows BinaryApproximatePacking
open FiniteDrawTrees LazyFairBitTrees MonadicBitSampler
variable {n : ℕ}

section Execute
variable {M : Type → Type} [Monad M] [LawfulMonad M]
variable (sample : (k : ℕ) → 0<k → M (Fin k))
variable (c : Row n) (columns : Set (FractionalCover.Column n))
variable (draw : Oracle FiniteDrawTrees.Tree c columns)

theorem advance_execute (p : Pending c columns) (s : BinaryFractionalCore.State n) :
    execute sample (advance c columns draw p s)=
      advance c columns (fun row => execute sample (draw row)) p s := by
  unfold advance
  dsimp only []
  split_ifs
  · rfl
  · cases p with
    | some q => rfl
    | none =>
        change execute sample (FiniteDrawTrees.bind _ _)=_
        rw [execute_bind]
        rfl

theorem runFrom_execute (fuel : Bits) (p : Pending c columns)
    (s : BinaryFractionalCore.State n) :
    execute sample (runFromM c columns draw fuel p s)=
      runFromM c columns (fun row => execute sample (draw row)) fuel p s := by
  have aux : ∀ t,∀ f : Bits,value f=t → ∀ p s,
      execute sample (runFromM c columns draw f p s)=
        runFromM c columns (fun row => execute sample (draw row)) f p s := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro f hf p s
      conv_lhs => rw [runFromM]
      conv_rhs => rw [runFromM]
      dsimp only []
      split_ifs with hz
      · rfl
      · have hp := (predecessor_spec f).1
        have hpos : 0<value f := Nat.pos_of_ne_zero
          (fun he => hz ((isZero_spec f).1.mpr he))
        have hi := ih (value (predecessor f).1) (by rw [hp,←hf];omega)
          (predecessor f).1 rfl
        change execute sample (FiniteDrawTrees.bind _ _)=_
        rw [execute_bind,advance_execute]
        congr 1
        funext next
        change execute sample (FiniteDrawTrees.bind _ _)=_
        rw [execute_bind,hi]
        rfl
  exact aux (value fuel) fuel rfl p s

theorem run_execute (delta : BinaryRational.Fraction) (fuel : Bits) :
    execute sample (runM c columns draw delta fuel)=
      runM c columns (fun row => execute sample (draw row)) delta fuel := by
  unfold runM
  change execute sample (FiniteDrawTrees.bind _ _)=_
  rw [execute_bind]
  congr 1
  funext first
  change execute sample (FiniteDrawTrees.bind _ _)=_
  rw [execute_bind,runFrom_execute]
  rfl

theorem solve_execute :
    execute sample (solveInputM c columns draw)=
      solveInputM c columns (fun row => execute sample (draw row)) := by
  unfold solveInputM
  change execute sample (FiniteDrawTrees.bind _ _)=_
  rw [execute_bind,run_execute]
  rfl
end Execute

variable (c : Row n) (columns : Set (FractionalCover.Column n))
variable (draw : Oracle FiniteDrawTrees.Tree c columns)
variable (hdraw : ∀ row,Binary (draw row))

include hdraw in
theorem advance_binary (p : Pending c columns) (s : BinaryFractionalCore.State n) :
    Binary (advance c columns draw p s) := by
  unfold advance
  dsimp only []
  split_ifs
  · exact .pure _
  · cases p with
    | some q => exact .pure _
    | none => exact binary_bind (hdraw _) _ (fun _ => .pure _)

include hdraw in
theorem runFrom_binary (fuel : Bits) (p : Pending c columns)
    (s : BinaryFractionalCore.State n) : Binary (runFromM c columns draw fuel p s) := by
  have aux : ∀ t,∀ f : Bits,value f=t → ∀ p s,Binary (runFromM c columns draw f p s) := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro f hf p s
      rw [runFromM]
      dsimp only []
      split_ifs with hz
      · exact .pure _
      · have hp := (predecessor_spec f).1
        have hpos : 0<value f := Nat.pos_of_ne_zero
          (fun he => hz ((isZero_spec f).1.mpr he))
        have hi := ih (value (predecessor f).1) (by rw [hp,←hf];omega)
          (predecessor f).1 rfl
        apply binary_bind (advance_binary c columns draw hdraw p s)
        intro next
        exact binary_bind (hi next.pending next.state) _ (fun _ => .pure _)
  exact aux (value fuel) fuel rfl p s

include hdraw in
theorem run_binary (delta : BinaryRational.Fraction) (fuel : Bits) :
    Binary (runM c columns draw delta fuel) := by
  apply binary_bind (hdraw _)
  intro first
  exact binary_bind (runFrom_binary c columns draw hdraw fuel _ _) _ (fun _ => .pure _)

include hdraw in
theorem solve_binary : Binary (solveInputM c columns draw) :=
  binary_bind (run_binary c columns draw hdraw _ _) _ (fun _ => .pure _)

end DirectedFlowCutGap.BinaryPackingTrees
