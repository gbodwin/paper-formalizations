import DirectedFlowCutGap.PhysicalVertexRounding
import DirectedFlowCutGap.ChargedPhysicalVertexSolver

/-! Execute the stored fractional cover, each physical rounding call, and the binary cut comparisons. -/

namespace DirectedFlowCutGap.PhysicalVertexSampling

open BinaryArithmetic BinaryFractionalRows BinaryRational FiniteDrawTrees EncodedVertexSolver
open RetainedGridState (Flags)
open PhysicalIntegerRounding (Result)
open LiteralTapeComposition (execute execute_map execute_bind)

abbrev Runner (n : ℕ) := ℕ → RoundingInput n → Bits → Option (Result n)

def chooseRowsWith {n : ℕ} (D : BinaryFractionalGuesses.Input n) (costs : FractionalCoverRawCore.RawRow n)
    (round : Runner n) (T : ℕ) :
    List (FractionalCoverRawCore.RawRow n) → Bits → Option ((Option (ChargedCutSelection.Scored D.costs) × ℕ) × Bits)
  | [], tape => some ((none,1),tape)
  | y::ys, tape => (round T ⟨D.adjacency,y,costs⟩ tape).bind fun a =>
      (chooseRowsWith D costs round T ys a.suffix).map fun (best,rest) =>
        (ChargedCutSelection.select (a.mask,a.paid) best,rest)

def chooseRows {n : ℕ} (D : BinaryFractionalGuesses.Input n) (round : Runner n) (T : ℕ) :=
  chooseRowsWith D (decodeRow D.costs) round T

private theorem chooseRows_observe {n : ℕ} (D : BinaryFractionalGuesses.Input n) (round : Runner n)
    (tree : Rounding n) (T : ℕ)
    (refines : ∀ input tape, (round T input tape).map Result.observe = execute T (tree input) tape)
    (rows : List (FractionalCoverRawCore.RawRow n)) (tape : Bits) :
    (chooseRows D round T rows tape).map (fun (best,rest) => (ChargedCutSelection.result best,rest)) =
      execute T (EncodedCutSelection.best (decodeRow D.costs)
        (rows.map fun y => tree (roundingInput (BinaryFractionalGuesses.decodeInput D) y))) tape := by
  induction rows generalizing tape with
  | nil => rfl
  | cons y ys ih =>
    let params := roundingInput (BinaryFractionalGuesses.decodeInput D) y
    let tail := EncodedCutSelection.best (decodeRow D.costs)
      (ys.map fun z => tree (roundingInput (BinaryFractionalGuesses.decodeInput D) z))
    change (chooseRows D round T (y::ys) tape).map (fun (best,rest) => (ChargedCutSelection.result best,rest)) =
      execute T (tree params >>= fun a =>
        map (fun b => some (b.elim a (EncodedCutSelection.cheaper (decodeRow D.costs) a))) tail) tape
    rw [execute_bind,← refines]
    have left : chooseRows D round T (y::ys) tape = (round T params tape).bind fun a =>
        (chooseRows D round T ys a.suffix).map fun (best,rest) =>
          (ChargedCutSelection.select (a.mask,a.paid) best,rest) := rfl
    rw [left]
    cases first : round T params tape with
    | none => rfl
    | some a =>
      simp only [Option.bind_some,Option.map_some,Result.observe,execute_map]
      rw [← ih]
      cases h : chooseRows D round T ys a.suffix with
      | none => rfl
      | some answer =>
        rcases answer with ⟨scored,rest⟩
        simp only [Option.map_some]
        change some (ChargedCutSelection.result (ChargedCutSelection.select (a.mask,a.paid) scored),rest)=_
        rw [show ChargedCutSelection.result (ChargedCutSelection.select (a.mask,a.paid) scored) = _ from
          ChargedCutSelection.select_value (a.mask,a.paid) scored]
        rfl

def fromPlanWith {n : ℕ} (D : BinaryFractionalGuesses.Input n) (costs : FractionalCoverRawCore.RawRow n)
    (round : Runner n) (T : ℕ) :
    PhysicalCoverReader.Plan n → Bits → Option ((Output n × ℕ) × Bits)
  | .invalid,tape => some ((.invalid,4*n+10),tape)
  | .infeasible d,tape => some ((.infeasible d,4*n+10),tape)
  | .zero mask,tape => some ((.cut mask,4*n+10),tape)
  | .covers rows,tape => (chooseRowsWith D costs round T rows tape).map fun (best,rest) =>
      (((ChargedCutSelection.result best).elim .invalid .cut,best.2+4*n+10),rest)

def fromPlan {n : ℕ} (D : BinaryFractionalGuesses.Input n) (round : Runner n) (T : ℕ) :=
  fromPlanWith D (decodeRow D.costs) round T

theorem fromPlan_observe {n : ℕ} (D : BinaryFractionalGuesses.Input n) (round : Runner n) (tree : Rounding n) (T : ℕ)
    (refines : ∀ input tape, (round T input tape).map Result.observe = execute T (tree input) tape)
    (plan : PhysicalCoverReader.Plan n) (tape : Bits) :
    (fromPlan D round T plan tape).map (fun ((out,_),rest) => (out,rest)) =
      execute T (PhysicalVertexSolver.treeFromPlan (BinaryFractionalGuesses.decodeInput D) tree plan) tape := by
  cases plan with
  | invalid | infeasible _ => rfl
  | zero mask =>
    have equal : maskOfSet (column mask)=mask := by
      apply Vector.ext
      intro i hi
      simp [maskOfSet,column]
    simp only [fromPlan,fromPlanWith,Option.map_some,PhysicalVertexSolver.treeFromPlan,roundOutput,equal]
    rfl
  | covers rows =>
    have casesEq := congrArg
      (Option.map fun (a,rest) => (a.elim Output.invalid Output.cut,rest))
      (chooseRows_observe D round tree T refines rows tape)
    simpa only [PhysicalVertexSolver.treeFromPlan,execute_map,fromPlan,fromPlanWith,chooseRows,Option.map_map,Function.comp_def,
      BinaryFractionalGuesses.decodeInput] using casesEq

end DirectedFlowCutGap.PhysicalVertexSampling
