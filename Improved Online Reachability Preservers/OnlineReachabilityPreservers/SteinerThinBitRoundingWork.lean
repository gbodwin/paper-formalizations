import OnlineReachabilityPreservers.SteinerBinaryArithmetic

/-! Compare thin thresholds without materializing a large shifted factor. -/

namespace OnlineReachabilityPreservers

/-- Drop at most one low bit per supplied input cell. The shift is itself
binary and might be larger than the whole input. -/
def binaryShiftRightWithWork (shift : List Bool) : List Bool → List Bool × ℕ
  | [] => ([],3)
  | bit::tail =>
    let zero := binaryZeroWithWork shift
    if zero.1 then (bit::tail,zero.2+4)
    else
      let prior := binaryDecrementWithWork shift
      let next := binaryShiftRightWithWork prior.1 tail
      (next.1,zero.2+prior.2+next.2+6)

private theorem binaryConsValue_div_two (bit : Bool) (tail : List Bool) :
    binaryWordValue (bit::tail)/2 = binaryWordValue tail := by
  cases bit
  · change (0+2*binaryWordValue tail)/2 = _
    omega
  · change (1+2*binaryWordValue tail)/2 = _
    omega

theorem binaryShiftRightWithWork_spec (shift word : List Bool) :
    let out := binaryShiftRightWithWork shift word
    binaryWordValue out.1 = binaryWordValue word/2^(binaryWordValue shift) ∧
      out.1.length ≤ word.length ∧ out.2 ≤ 3+word.length*(9*shift.length+12) := by
  induction word generalizing shift with
  | nil => simp [binaryShiftRightWithWork,binaryWordValue]
  | cons bit tail ih =>
    let zero := binaryZeroWithWork shift
    let prior := binaryDecrementWithWork shift
    let next := binaryShiftRightWithWork prior.1 tail
    obtain ⟨tested,zeroWork⟩ := binaryZeroWithWork_spec shift
    change zero.1 = decide (binaryWordValue shift = 0) at tested
    change zero.2 ≤ 4*shift.length+3 at zeroWork
    change (let out := if zero.1 then (bit::tail,zero.2+4)
      else (next.1,zero.2+prior.2+next.2+6)
      binaryWordValue out.1 = binaryWordValue (bit::tail)/2^(binaryWordValue shift) ∧
        out.1.length ≤ tail.length+1 ∧ out.2 ≤ 3+(tail.length+1)*(9*shift.length+12))
    by_cases done : zero.1 = true
    · have exhausted := of_decide_eq_true (tested.symm.trans done)
      rw [ite_eq_left done,exhausted,pow_zero,Nat.div_one]
      refine ⟨rfl,le_rfl,?_⟩
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · have positive : 0 < binaryWordValue shift :=
        Nat.pos_of_ne_zero fun empty => done (tested.trans (decide_eq_true empty))
      obtain ⟨width,priorWork,priorValue⟩ := binaryDecrementWithWork_spec shift
      obtain ⟨nextValue,nextLength,nextWork⟩ := ih prior.1
      change prior.1.length = shift.length at width
      change prior.2 ≤ 5*shift.length+3 at priorWork
      change binaryWordValue next.1 = binaryWordValue tail/2^(binaryWordValue prior.1) at nextValue
      change next.2 ≤ 3+tail.length*(9*prior.1.length+12) at nextWork
      have exponent : binaryWordValue prior.1+1 = binaryWordValue shift := priorValue positive
      rw [ite_eq_right done]
      refine ⟨?_,nextLength.trans (Nat.le_succ _),?_⟩
      · rw [nextValue,← binaryConsValue_div_two bit tail,Nat.div_div_eq_div_mul,
          Nat.mul_comm 2,← pow_succ,exponent]
      · rw [width] at nextWork
        rw [Nat.add_mul,Nat.one_mul]
        omega

/-- Decide the thin rounding inequality using a right shift of the sampled
threshold and a binary comparison. -/
def thinThresholdTestWithBinaryWork (sample factor load : List Bool) : Bool × ℕ :=
  let quotient := binaryShiftRightWithWork load sample
  let passed := binaryLessWithWork quotient.1 factor false
  (passed.1,quotient.2+passed.2+4)

/-- The comparison tally depends on word lengths, even if the supplied
load encodes a shift far larger than the sampled threshold's width. -/
def thinThresholdTestBinaryWorkBudget (sample factor load : ℕ) : ℕ :=
  (3+sample*(9*load+12))+(14*(sample+factor)+4)+4

theorem thinThresholdTestWithBinaryWork_spec (sample factor load : List Bool) :
    let out := thinThresholdTestWithBinaryWork sample factor load
    out.1 = decide (binaryWordValue sample < binaryWordValue factor*2^(binaryWordValue load)) ∧
      out.2 ≤ thinThresholdTestBinaryWorkBudget sample.length factor.length load.length := by
  let quotient := binaryShiftRightWithWork load sample
  let passed := binaryLessWithWork quotient.1 factor false
  obtain ⟨value,length,work⟩ := binaryShiftRightWithWork_spec load sample
  obtain ⟨answer,comparison⟩ := binaryLessWithWork_noBorrow_spec quotient.1 factor
  change binaryWordValue quotient.1 = _ at value
  change quotient.1.length ≤ sample.length at length
  change passed.1 = _ at answer
  change passed.2 ≤ 14*(quotient.1.length+factor.length)+4 at comparison
  change passed.1 = decide _ ∧ quotient.2+passed.2+4 ≤ _
  refine ⟨?_,Nat.add_le_add_right (Nat.add_le_add work (comparison.trans (by gcongr))) _⟩
  rw [answer,value]
  exact decide_eq_decide.mpr (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)))

end OnlineReachabilityPreservers
