import DirectedFlowCutGap.MeasuredMultiplicityCover

/-! Adding a charge to an oracle with the same exact choices preserves the
entire raw covering state. A stopped iteration pays neither oracle. -/
namespace DirectedFlowCutGap.MeasuredCoverExtraWork

open MeasuredMultiplicityCover (MeasuredOracle Execution start advance run)
open FractionalCoverRawCore (RawRow)

variable {r : ℕ}

private def Preserve (earlier later : Execution r) (budget : ℕ) : Prop :=
  later.stored = earlier.stored ∧ later.arithmetic = earlier.arithmetic ∧
    later.oracleWork ≤ earlier.oracleWork+budget

theorem run_preserves (c : RawRow r) (earlier later : MeasuredOracle r)
    (choices : ∀ y, (later y).1 = (earlier y).1)
    {fee : ℕ} (cost : ∀ y, (later y).2 ≤ (earlier y).2+fee) (k : ℕ) :
    (run c later k).stored = (run c earlier k).stored ∧
    (run c later k).arithmetic = (run c earlier k).arithmetic ∧
    (run c later k).oracleWork ≤ (run c earlier k).oracleWork+(k+1)*fee := by
  have runStart : Preserve (start c earlier) (start c later) fee := by
    simp only [Preserve,start,choices,true_and]
    exact cost _
  have runStep (s : MeasuredMultiplicityCover.Stored r) :
      Preserve (advance c earlier s) (advance c later s) fee := by
    by_cases stopped : (BinaryRawRational.le RawNonnegativeRational.Code.one
      (MeasuredMultiplicityForms.dot c s.weights).1).1 = true
    · simp only [Preserve,advance,ite_eq_left stopped,zero_add,true_and,Nat.zero_le]
    · simpa only [Preserve,advance,ite_eq_right stopped,choices,true_and] using cost s.weights
  induction k with
  | zero => simpa only [Preserve,run,Nat.zero_add,Nat.one_mul] using runStart
  | succ k ih =>
    obtain ⟨stored,arithmetic,oracleWork⟩ := ih
    obtain ⟨nextStored,nextArithmetic,nextOracle⟩ := runStep (run c earlier k).stored
    simp only [Nat.add_mul,Nat.one_mul] at oracleWork
    simp only [run,stored,arithmetic,nextStored,nextArithmetic,true_and,Nat.add_mul,Nat.one_mul]
    omega

end DirectedFlowCutGap.MeasuredCoverExtraWork
