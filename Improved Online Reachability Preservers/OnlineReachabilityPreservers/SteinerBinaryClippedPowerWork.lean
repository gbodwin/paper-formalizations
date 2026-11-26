import OnlineReachabilityPreservers.SteinerBinaryArithmetic

/-! Compute a clipped power of two by scanning only the supplied word widths. -/

namespace OnlineReachabilityPreservers

private def binaryPowerTwoWithinWithWork (exponent : List Bool) : List Bool → Option (List Bool) × ℕ
  | [] => (none,3)
  | _::remaining =>
    let zero := binaryZeroWithWork exponent
    if zero.1 then (some [true],zero.2+5) else
      let prior := binaryDecrementWithWork exponent
      let next := binaryPowerTwoWithinWithWork prior.1 remaining
      (next.1.map (false::·),zero.2+prior.2+next.2+9)

private def binaryPowerTwoWithinSpec (exponent width : ℕ) : Option (List Bool) → Prop
  | none => width ≤ exponent
  | some word => exponent < width ∧ word.length ≤ width ∧ binaryWordValue word = 2^exponent

private theorem binaryPowerTwoWithinWithWork_spec (exponent widthWitness : List Bool) :
    let out := binaryPowerTwoWithinWithWork exponent widthWitness
    binaryPowerTwoWithinSpec (binaryWordValue exponent) widthWitness.length out.1 ∧
      out.2 ≤ 3+widthWitness.length*(9*exponent.length+15) := by
  induction widthWitness generalizing exponent with
  | nil => simp [binaryPowerTwoWithinWithWork,binaryPowerTwoWithinSpec]
  | cons bit rest ih =>
    let zero := binaryZeroWithWork exponent
    let prior := binaryDecrementWithWork exponent
    let tail := binaryPowerTwoWithinWithWork prior.1 rest
    let out := if zero.1 then (some [true],zero.2+5)
      else (tail.1.map (false::·),zero.2+prior.2+tail.2+9)
    obtain ⟨zeroValue,zeroCost⟩ := binaryZeroWithWork_spec exponent
    change zero.1 = decide (binaryWordValue exponent = 0) at zeroValue
    change zero.2 ≤ 4*exponent.length+3 at zeroCost
    change binaryPowerTwoWithinSpec (binaryWordValue exponent) (rest.length+1) out.1 ∧
      out.2 ≤ 3+(rest.length+1)*(9*exponent.length+15)
    unfold out
    rw [zeroValue,Nat.succ_mul rest.length]
    by_cases empty : binaryWordValue exponent = 0
    · rw [decide_eq_true empty]
      refine ⟨?_,?_⟩
      · simp [binaryPowerTwoWithinSpec,empty]
        decide
      · change zero.2+5 ≤ _
        omega
    · rw [decide_eq_false empty]
      obtain ⟨length,priorCost,priorValue⟩ := binaryDecrementWithWork_spec exponent
      have decrement : binaryWordValue prior.1+1 = binaryWordValue exponent :=
        priorValue (Nat.pos_of_ne_zero empty)
      obtain ⟨shape,tailCost⟩ := ih prior.1
      change prior.1.length = exponent.length at length
      change prior.2 ≤ 5*exponent.length+3 at priorCost
      change binaryPowerTwoWithinSpec (binaryWordValue prior.1) rest.length tail.1 at shape
      change tail.2 ≤ 3+rest.length*(9*prior.1.length+15) at tailCost
      rw [length] at tailCost
      refine ⟨?_,?_⟩
      · change binaryPowerTwoWithinSpec (binaryWordValue exponent) (rest.length+1) (tail.1.map (false::·))
        cases returned : tail.1 with
        | none =>
          rw [returned] at shape
          change rest.length ≤ binaryWordValue prior.1 at shape
          change rest.length+1 ≤ binaryWordValue exponent
          omega
        | some word =>
          rw [returned] at shape
          obtain ⟨small,wordWidth,value⟩ := shape
          change binaryWordValue exponent < rest.length+1 ∧ (false::word).length ≤ rest.length+1 ∧
            binaryWordValue (false::word) = 2^(binaryWordValue exponent)
          refine ⟨by omega,by simpa using Nat.succ_le_succ wordWidth,?_⟩
          change 0+2*binaryWordValue word = _
          rw [value,← decrement,pow_succ,Nat.zero_add,Nat.mul_comm]
      · change zero.2+prior.2+tail.2+9 ≤ _
        omega

/-- Use the ceiling word as the maximum number of positions to inspect.
The exponent itself can encode a much larger value. -/
def binaryClippedPowerTwoWithWork (exponent ceiling : List Bool) : List Bool × ℕ :=
  let candidate := binaryPowerTwoWithinWithWork exponent ceiling
  match candidate.1 with
  | none => (ceiling,candidate.2+4)
  | some word =>
    let below := binaryLessWithWork word ceiling false
    (if below.1 then word else ceiling,candidate.2+below.2+5)

def binaryClippedPowerTwoWorkBudget (exponentWidth ceilingWidth : ℕ) : ℕ :=
  12+ceilingWidth*(9*exponentWidth+43)

/-- Return the exact clipped power of two, including padded and zero ceilings. -/
theorem binaryClippedPowerTwoWithWork_spec (exponent ceiling : List Bool) :
    let out := binaryClippedPowerTwoWithWork exponent ceiling
    binaryWordValue out.1 = min (2^(binaryWordValue exponent)) (binaryWordValue ceiling) ∧
      out.1.length ≤ ceiling.length ∧ out.2 ≤ binaryClippedPowerTwoWorkBudget exponent.length ceiling.length := by
  let candidate := binaryPowerTwoWithinWithWork exponent ceiling
  obtain ⟨shape,work⟩ := binaryPowerTwoWithinWithWork_spec exponent ceiling
  change binaryPowerTwoWithinSpec (binaryWordValue exponent) ceiling.length candidate.1 at shape
  change candidate.2 ≤ 3+ceiling.length*(9*exponent.length+15) at work
  let out := match candidate.1 with
    | none => (ceiling,candidate.2+4)
    | some word =>
      let below := binaryLessWithWork word ceiling false
      (if below.1 then word else ceiling,candidate.2+below.2+5)
  change binaryWordValue out.1 = min (2^(binaryWordValue exponent)) (binaryWordValue ceiling) ∧
    out.1.length ≤ ceiling.length ∧ out.2 ≤ binaryClippedPowerTwoWorkBudget exponent.length ceiling.length
  unfold out
  cases returned : candidate.1 with
  | none =>
    rw [returned] at shape
    change ceiling.length ≤ binaryWordValue exponent at shape
    have enough : binaryWordValue ceiling ≤ 2^binaryWordValue exponent :=
      (binaryWordValue_lt_pow ceiling).le.trans (Nat.pow_le_pow_right (by decide) shape)
    refine ⟨(min_eq_right enough).symm,le_rfl,?_⟩
    change candidate.2+4 ≤ _
    unfold binaryClippedPowerTwoWorkBudget
    rw [Nat.mul_add]
    rw [Nat.mul_add] at work
    omega
  | some word =>
    rw [returned] at shape
    obtain ⟨_,width,value⟩ := shape
    let below := binaryLessWithWork word ceiling false
    obtain ⟨tested,testCost⟩ := binaryLessWithWork_noBorrow_spec word ceiling
    change below.1 = decide (binaryWordValue word < binaryWordValue ceiling) at tested
    change below.2 ≤ 14*(word.length+ceiling.length)+4 at testCost
    change binaryWordValue (if below.1 then word else ceiling) =
        min (2^(binaryWordValue exponent)) (binaryWordValue ceiling) ∧
      (if below.1 then word else ceiling).length ≤ ceiling.length ∧ candidate.2+below.2+5 ≤ _
    refine ⟨?_,?_,?_⟩
    · rw [tested,← value]
      by_cases smaller : binaryWordValue word < binaryWordValue ceiling
      · rw [decide_eq_true smaller]
        exact (min_eq_left smaller.le).symm
      · rw [decide_eq_false smaller]
        exact (min_eq_right (le_of_not_gt smaller)).symm
    · split
      · exact width
      · exact le_rfl
    · unfold binaryClippedPowerTwoWorkBudget
      rw [Nat.mul_add]
      rw [Nat.mul_add] at work
      omega

end OnlineReachabilityPreservers
