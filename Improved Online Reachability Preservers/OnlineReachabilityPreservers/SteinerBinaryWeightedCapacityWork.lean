import OnlineReachabilityPreservers.SteinerBinaryWeightedLoadWork
import OnlineReachabilityPreservers.SteinerRoundedCapacities

/-! Compare binary multiples to obtain the exact rounded weighted capacity up to the flow supply. -/

namespace OnlineReachabilityPreservers

private theorem belowCeilingDiv_iff (amount divisor count : ℕ) (positive : 0 < divisor) :
    count < (amount+(divisor-1))/divisor ↔ count*divisor < amount := by
  calc
    _ ↔ ¬ ((amount+(divisor-1))/divisor < count+1) := by omega
    _ ↔ ¬ (amount+(divisor-1) < (count+1)*divisor) := not_congr (Nat.div_lt_iff_lt_mul positive)
    _ ↔ _ := by rw [Nat.add_mul,Nat.one_mul]; omega

/-- Increase the candidate quotient and its stored divisor multiple until
that multiple reaches the numerator or the supplied steps run out. -/
def binaryCeilingDivLoopWithWork (amount divisor : List Bool) :
    ℕ → List Bool → List Bool → List Bool × ℕ
  | 0, count, _ => (count,2)
  | fuel+1, count, multiple =>
    let needed := binaryLessWithWork multiple amount false
    if needed.1 then
      let nextCount := addBinaryWordsWithWork count [] true
      let nextMultiple := addBinaryWordsWithWork multiple divisor false
      let tail := binaryCeilingDivLoopWithWork amount divisor fuel nextCount.1 nextMultiple.1
      (tail.1,needed.2+nextCount.2+nextMultiple.2+tail.2+7)
    else (count,needed.2+4)

private def binaryCeilingDivStepWorkBudget (amount divisor count multiple : ℕ) : ℕ :=
  (14*(multiple+amount)+4)+(20*count+5)+(20*(multiple+divisor)+5)+7

def binaryCeilingDivWorkBudget (amount divisor count multiple fuel : ℕ) : ℕ :=
  2+fuel*binaryCeilingDivStepWorkBudget amount divisor (count+fuel) (multiple+fuel*(divisor+1))

/-- A represented candidate at or below the ceiling can advance by at most
the given budget. The resulting count is clipped exactly at the ceiling. -/
theorem binaryCeilingDivLoopWithWork_spec (amount divisor : List Bool) (fuel : ℕ) (count multiple : List Bool)
    (positive : 0 < binaryWordValue divisor)
    (product : binaryWordValue multiple = binaryWordValue count*binaryWordValue divisor)
    (below : binaryWordValue count ≤ (binaryWordValue amount+(binaryWordValue divisor-1))/binaryWordValue divisor) :
    let out := binaryCeilingDivLoopWithWork amount divisor fuel count multiple
    binaryWordValue out.1 = min (binaryWordValue count+fuel)
      ((binaryWordValue amount+(binaryWordValue divisor-1))/binaryWordValue divisor) ∧
      out.1.length ≤ count.length+fuel ∧
      out.2 ≤ binaryCeilingDivWorkBudget amount.length divisor.length count.length multiple.length fuel := by
  let a := binaryWordValue amount
  let d := binaryWordValue divisor
  let target := (a+(d-1))/d
  induction fuel generalizing count multiple with
  | zero => simp [binaryCeilingDivLoopWithWork,binaryCeilingDivWorkBudget,min_eq_left below]
  | succ fuel ih =>
    let needed := binaryLessWithWork multiple amount false
    let k := binaryWordValue count
    let widthCount := count.length+(fuel+1)
    let widthMultiple := multiple.length+(fuel+1)*(divisor.length+1)
    let fee := binaryCeilingDivStepWorkBudget amount.length divisor.length widthCount widthMultiple
    obtain ⟨comparison,checkCost⟩ := binaryLessWithWork_noBorrow_spec multiple amount
    change needed.1 = decide (binaryWordValue multiple < a) at comparison
    change needed.2 ≤ 14*(multiple.length+amount.length)+4 at checkCost
    have crossing : binaryWordValue multiple < a ↔ k < target := by
      rw [product]
      exact (belowCeilingDiv_iff a d k positive).symm
    have monotone {c m : ℕ} (cBound : c ≤ widthCount) (mBound : m ≤ widthMultiple) :
        binaryCeilingDivStepWorkBudget amount.length divisor.length c m ≤ fee := by
      unfold fee binaryCeilingDivStepWorkBudget
      gcongr
    have roomCount : count.length ≤ widthCount := Nat.le_add_right _ _
    have roomMultiple : multiple.length ≤ widthMultiple := Nat.le_add_right _ _
    change (let out := if needed.1 then _ else (count,needed.2+4)
      binaryWordValue out.1 = min (k+(fuel+1)) target ∧ out.1.length ≤ count.length+(fuel+1) ∧
        out.2 ≤ 2+(fuel+1)*fee)
    by_cases needs : k < target
    · have on : needed.1 = true := comparison.trans (decide_eq_true (crossing.mpr needs))
      simp only [on,ite_true]
      let countNext := addBinaryWordsWithWork count [] true
      let multipleNext := addBinaryWordsWithWork multiple divisor false
      let tail := binaryCeilingDivLoopWithWork amount divisor fuel countNext.1 multipleNext.1
      obtain ⟨countValue,countWidth,countCost⟩ := addBinaryWordsWithWork_spec count [] true
      obtain ⟨multipleValue,multipleWidth,multipleCost⟩ := addBinaryWordsWithWork_spec multiple divisor false
      change binaryWordValue countNext.1 = k+0+1 at countValue
      change binaryWordValue multipleNext.1 = binaryWordValue multiple+d+0 at multipleValue
      change countNext.1.length ≤ count.length+0+1 at countWidth
      change countNext.2 ≤ 20*(count.length+0)+5 at countCost
      change multipleNext.1.length ≤ multiple.length+divisor.length+1 at multipleWidth
      change multipleNext.2 ≤ 20*(multiple.length+divisor.length)+5 at multipleCost
      rw [Nat.add_zero] at countValue
      rw [product,Nat.add_zero] at multipleValue
      have nextProduct : binaryWordValue multipleNext.1 = binaryWordValue countNext.1*d := by
        rw [countValue,multipleValue,Nat.add_mul,Nat.one_mul]
      have nextBelow : binaryWordValue countNext.1 ≤ target := by rw [countValue]; exact needs
      obtain ⟨tailValue,tailWidth,tailCost⟩ := ih countNext.1 multipleNext.1 nextProduct nextBelow
      change binaryWordValue tail.1 = min (binaryWordValue countNext.1+fuel) target at tailValue
      change tail.1.length ≤ countNext.1.length+fuel at tailWidth
      change tail.2 ≤ binaryCeilingDivWorkBudget amount.length divisor.length countNext.1.length multipleNext.1.length fuel at tailCost
      rw [countValue] at tailValue
      have countFits : countNext.1.length+fuel ≤ widthCount := by dsimp only [widthCount]; omega
      have multipleFits : multipleNext.1.length+fuel*(divisor.length+1) ≤ widthMultiple := by
        dsimp only [widthMultiple]
        rw [Nat.add_mul,Nat.one_mul]
        omega
      have tailFits : tail.2 ≤ 2+fuel*fee :=
        tailCost.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (monotone countFits multipleFits)) _)
      have checked : needed.2+countNext.2+multipleNext.2+7 ≤ fee := by
        apply LE.le.trans _ (monotone roomCount roomMultiple)
        unfold binaryCeilingDivStepWorkBudget
        omega
      refine ⟨tailValue.trans (congrArg (fun c => min c target) (by omega)),tailWidth.trans countFits,?_⟩
      change needed.2+countNext.2+multipleNext.2+tail.2+7 ≤ 2+(fuel+1)*fee
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · have off : needed.1 = false := comparison.trans (decide_eq_false (fun before => needs (crossing.mp before)))
      simp only [off,Bool.false_eq_true,ite_false]
      have equal : k = target := le_antisymm below (Nat.le_of_not_gt needs)
      have firstCost : needed.2+4 ≤ fee := by
        apply LE.le.trans _ (monotone roomCount roomMultiple)
        unfold binaryCeilingDivStepWorkBudget
        omega
      refine ⟨?_,roomCount,?_⟩
      · change k = min (k+(fuel+1)) target
        rw [← equal,min_eq_right (Nat.le_add_right _ _)]
      · rw [Nat.add_mul,Nat.one_mul]
        omega

/-- Compute the rounded capacity of the represented weighted row, capped
at the supplied flow amount. -/
def binaryClippedWeightedCapacityWithWork (cost : List Bool) (row : BinaryWeightedLoad) (supply : ℕ) : List Bool × ℕ :=
  binaryCeilingDivLoopWithWork row.amount cost supply [] []

theorem binaryClippedWeightedCapacityWithWork_spec (cost : List Bool) (row : BinaryWeightedLoad) (charge supply : ℕ)
    (positive : 0 < binaryWordValue cost) (represented : row.Encodes (binaryWordValue cost) charge) :
    let result := binaryClippedWeightedCapacityWithWork cost row supply
    binaryWordValue result.1 = min supply (roundedWeightedCapacity (binaryWordValue cost) charge) ∧
      result.1.length ≤ supply ∧ result.2 ≤ binaryCeilingDivWorkBudget row.amount.length cost.length 0 0 supply := by
  obtain ⟨value,length,work⟩ := binaryCeilingDivLoopWithWork_spec row.amount cost supply [] [] positive
    (by simp [binaryWordValue]) (Nat.zero_le _)
  refine ⟨?_,?_,work⟩
  · simpa only [binaryWordValue,Nat.zero_add,represented.2.2,roundedWeightedCapacity,binaryClippedWeightedCapacityWithWork]
      using value
  · simpa [binaryClippedWeightedCapacityWithWork] using length

theorem binaryCeilingDivWorkBudget_mono_widths {a a' d d' : ℕ} (numerator : a ≤ a') (denominator : d ≤ d')
    (count multiple fuel : ℕ) :
    binaryCeilingDivWorkBudget a d count multiple fuel ≤ binaryCeilingDivWorkBudget a' d' count multiple fuel := by
  unfold binaryCeilingDivWorkBudget binaryCeilingDivStepWorkBudget
  gcongr

/-- Enlarge the input widths and the capped quotient search allowance. -/
theorem binaryCeilingDivWorkBudget_le {a a' d d' c c' w w' f f' : ℕ}
    (numerator : a ≤ a') (denominator : d ≤ d') (count : c ≤ c') (multiple : w ≤ w') (fuel : f ≤ f') :
    binaryCeilingDivWorkBudget a d c w f ≤ binaryCeilingDivWorkBudget a' d' c' w' f' := by
  unfold binaryCeilingDivWorkBudget binaryCeilingDivStepWorkBudget
  gcongr

end OnlineReachabilityPreservers
