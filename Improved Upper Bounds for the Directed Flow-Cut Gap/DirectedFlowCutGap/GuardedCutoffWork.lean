import DirectedFlowCutGap.GuardedFuelFreeRounding
import DirectedFlowCutGap.GuardedIntegerRoundingPolynomial
import DirectedFlowCutGap.BinaryIntegerCutoff

/-! Charge the cutoff prefix even if packed rounding exhausts its tape. -/
namespace DirectedFlowCutGap.GuardedCutoffWork

open BinaryArithmetic
open RetainedGridState (PairFlags)
open PhysicalIntegerRounding (Result)
open PhysicalCoverAccess (Read)
open IntegerEpochParameters (cap)

def budget (n L T : ℕ) : ℕ :=
  EncodedEpochParameters.operationBound n+2*n+10+
    (if L ≤ n ∧ 64*cap n ≤ L ∧ n ≤ L^3 then GuardedIntegerRoundingWork.budget n L T else 0)

open Polynomial in
theorem budget_polynomial : ∃ p : Polynomial ℕ, ∀ n L T, budget n L T ≤ p.eval (n+T) := by
  obtain ⟨p,hard⟩ := GuardedIntegerRoundingWork.hard_polynomial
  obtain ⟨q,old⟩ := PhysicalIntegerRoundingCost.round_budget_polynomial
  refine ⟨q+p,fun n L T => ?_⟩
  have setup : EncodedEpochParameters.operationBound n+2*n+10 ≤ q.eval (n+T) :=
    (Nat.le_add_right _ _).trans (old n L T)
  rw [eval_add]
  unfold budget
  split
  next fits => exact Nat.add_le_add setup (hard n L T fits.1)
  next => exact setup.trans (Nat.le_add_right _ _)

private theorem positive_level {n L : ℕ} (inside : (BinaryIntegerCutoff.compute n L).inside=true)
    (hard : (BinaryIntegerCutoff.compute n L).hard=true) : 0<L := by
  have enough := ((BinaryIntegerCutoff.hard_true n L ((BinaryIntegerCutoff.inside_true n L).mp inside)).mp hard).1
  have capPositive : 0<cap n := by unfold cap; positivity
  omega

def runBinary {n : ℕ} (T : ℕ) (adj : PairFlags n) (L : ℕ) (tape : Bits) : Read (Result n × ℕ) :=
  let gate := BinaryIntegerCutoff.compute n L
  let setup := gate.parameters.work+2*n+10
  let cut : Read (Result n) := if inside : gate.inside then
    if hard : gate.hard then
      let r := GuardedFuelFreeRounding.hard T adj L (positive_level inside hard) tape
      (r.1.map (fun result => { result with paid := setup+result.paid }),setup+r.2)
    else (some ⟨Vector.replicate n true,tape,setup⟩,setup)
  else (some ⟨Vector.replicate n false,tape,setup⟩,setup)
  (cut.1.map (fun r => (r,gate.paid)),cut.2+gate.paid)

theorem binary_value {n : ℕ} (T : ℕ) (adj : PairFlags n) (L : ℕ) (tape : Bits) :
    (runBinary T adj L tape).1=BinaryIntegerCutoff.run T adj L tape := by
  by_cases inside : (BinaryIntegerCutoff.compute n L).inside=true
  · by_cases hard : (BinaryIntegerCutoff.compute n L).hard=true
    · simp only [runBinary,BinaryIntegerCutoff.run,dite_eq_left inside,dite_eq_left hard,
        ite_eq_left inside,ite_eq_left hard,GuardedFuelFreeRounding.hard_value]
    · simp only [runBinary,BinaryIntegerCutoff.run,dite_eq_left inside,dite_eq_right hard,
        ite_eq_left inside,ite_eq_right hard]
  · simp only [runBinary,BinaryIntegerCutoff.run,dite_eq_right inside,ite_eq_right inside]

theorem binary_paid {n T L B : ℕ} (adj : PairFlags n) (tape : Bits) (level : L.size ≤ B) :
    (runBinary T adj L tape).2 ≤ budget n L T+BinaryIntegerCutoff.budget n B := by
  let gate := BinaryIntegerCutoff.compute n L
  have overhead : gate.paid ≤ BinaryIntegerCutoff.budget n B := BinaryIntegerCutoff.compute_paid level
  have setup := EncodedEpochParameters.compute_bound n
  by_cases inside : L ≤ n
  · have hi := (BinaryIntegerCutoff.inside_true n L).mpr inside
    by_cases constraints : 64*cap n ≤ L ∧ n ≤ L^3
    · have hard := (BinaryIntegerCutoff.hard_true n L inside).mpr constraints
      have core := GuardedFuelFreeRounding.hard_paid (T:=T) (L:=L) adj (positive_level hi hard) tape
      simp only [runBinary,budget,BinaryIntegerCutoff.parameters_value,dite_eq_left hi,dite_eq_left hard,
        ite_eq_left (And.intro inside constraints)]
      change (EncodedEpochParameters.compute n).work+2*n+10+(GuardedFuelFreeRounding.hard T adj L (positive_level hi hard) tape).2+gate.paid ≤ _
      omega
    · have hard := fun h => constraints ((BinaryIntegerCutoff.hard_true n L inside).mp h)
      simp only [runBinary,budget,BinaryIntegerCutoff.parameters_value,dite_eq_left hi,dite_eq_right hard,
        ite_eq_right (fun h : L ≤ n ∧ 64*cap n ≤ L ∧ n ≤ L^3 => constraints h.2),Nat.add_zero]
      change (EncodedEpochParameters.compute n).work+2*n+10+gate.paid ≤ _
      omega
  · have hi := fun h => inside ((BinaryIntegerCutoff.inside_true n L).mp h)
    simp only [runBinary,budget,BinaryIntegerCutoff.parameters_value,dite_eq_right hi,
      ite_eq_right (fun h : L ≤ n ∧ 64*cap n ≤ L ∧ n ≤ L^3 => inside h.1),Nat.add_zero]
    change (EncodedEpochParameters.compute n).work+2*n+10+gate.paid ≤ _
    omega

end DirectedFlowCutGap.GuardedCutoffWork
