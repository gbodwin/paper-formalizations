import DirectedFlowCutGap.PaidVertexAmplification

/-! Interleave the reached row stacks with the enclosing sample frames.
Failed samples retain their reached row work and save no sample frame. -/
namespace DirectedFlowCutGap.AmplificationFrameLayout

open BinaryArithmetic EncodedArrayStorage
open ChargedPhysicalVertexSolver (rowsCount)

abbrev Code := List (Instruction Unit)

private def save : Code := EncodedFrameStack.push ()
private def restore : Code := EncodedFrameStack.pop ()

private def walk (one : Bits → Code × Option Bits) : ℕ → Bits → Code
  | 0,_ => []
  | k+1,tape =>
    let row := one tape
    match row.2 with
    | none => row.1
    | some rest => row.1++save++walk one k rest++restore

private theorem walk_bounds (one : Bits → Code × Option Bits) (cells work : ℕ)
    (fits : ∀ tape, fresh (one tape).1≤cells ∧ (one tape).1.length≤work) (k : ℕ) (tape : Bits) :
    fresh (walk one k tape)≤k*(cells+2) ∧ (walk one k tape).length≤k*(work+8) := by
  induction k generalizing tape with
  | zero => exact ⟨Nat.zero_le _,Nat.zero_le _⟩
  | succ k ih =>
    have head := fits tape
    have saveCells : fresh save=2 := rfl
    have restoreCells : fresh restore=0 := rfl
    have saveWork : save.length=4 := rfl
    have restoreWork : restore.length=4 := rfl
    simp only [walk,Nat.succ_mul]
    cases (one tape).2 with
    | none => dsimp only; constructor <;> omega
    | some rest =>
      have next := ih rest
      simp only [fresh_append,List.length_append,saveCells,restoreCells,saveWork,restoreWork]
      constructor <;> omega

private def rowCode {n : ℕ} (D : BinaryFractionalGuesses.Input n) (costs : FractionalCoverRawCore.RawRow n)
    (round : PaidVertexSampling.Runner n) (T : ℕ) (cover : PhysicalCoverReader.Plan n) (tape : Bits) : Code :=
  match cover with
  | .covers rows => PaidVertexSampling.rowFrameCode D costs round T rows tape
  | _ => []

def code {n : ℕ} (D : BinaryFractionalGuesses.Input n) (round : PaidVertexSampling.Runner n)
    (draw extra confidence : ℕ) (plan : PhysicalCoverReader.Plan n) (tape : Bits) : Code :=
  let ready := BinaryAmplificationPreparation.prepare D.costs draw extra confidence
  let one : Bits → Code × Option Bits := fun input =>
    (rowCode D ready.costs round ready.trials plan input,
      (PaidVertexSampling.fromPlanWithFrameStack D ready.costs round ready.trials plan input).1.1.map Prod.snd)
  walk one (extra+1) tape

theorem bounds {n : ℕ} (D : BinaryFractionalGuesses.Input n) (round : PaidVertexSampling.Runner n)
    (draw extra confidence : ℕ) (plan : PhysicalCoverReader.Plan n) (tape : Bits) :
    let trace := code D round draw extra confidence plan tape
    fresh trace≤(extra+1)*(2*rowsCount plan+2) ∧ trace.length≤(extra+1)*(8*rowsCount plan+8) := by
  apply walk_bounds
  intro input
  cases plan with
  | invalid | infeasible _ | zero _ => exact ⟨Nat.zero_le _,Nat.zero_le _⟩
  | covers rows => exact PaidVertexSampling.rowFrameCode_bounds D _ round _ rows input

end DirectedFlowCutGap.AmplificationFrameLayout
