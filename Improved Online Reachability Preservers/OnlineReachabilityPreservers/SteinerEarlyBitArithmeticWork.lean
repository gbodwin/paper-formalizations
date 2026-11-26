import OnlineReachabilityPreservers.SteinerBinaryArithmetic
import OnlineReachabilityPreservers.SteinerFinWeightedReplayWork

/-! Evaluate the forest trial-count arithmetic on explicit binary words. -/

namespace OnlineReachabilityPreservers

/-- Compute the early trial count using binary addition, multiplication,
and a four-bit shift. -/
def earlyTrialCountWithBinaryWork (vertexBits heightBits : List Bool) : List Bool × ℕ :=
  let width := positiveBinaryLengthWithWork vertexBits
  let level := addBinaryWordsWithWork heightBits [] true
  let square := mulBinaryWordsWithWork level.1 level.1
  let count := mulBinaryWordsWithWork square.1 width.1
  (false::false::false::false::count.1,width.2+level.2+square.2+count.2+11)

/-- Bit-list work for the trial formula at the two supplied word lengths. -/
def earlyTrialCountBitBudget (nBits heightBits : ℕ) : ℕ :=
  (5+nBits*(20*nBits+9))+(20*heightBits+5)+
  binaryMultiplicationWorkBudget (heightBits+1) (heightBits+1)+
  binaryMultiplicationWorkBudget ((heightBits+1)*(heightBits+3)) (nBits+1)+11

theorem earlyTrialCountWithBinaryWork_spec (vertexBits heightBits : List Bool) :
    let out := earlyTrialCountWithBinaryWork vertexBits heightBits
    binaryWordValue out.1 = 16*(binaryWordValue heightBits+1)^2*(max 1 vertexBits.length) ∧
      out.1.length ≤ (vertexBits.length+1)*((heightBits.length+1)*(heightBits.length+3)+2)+4 ∧
      out.2 ≤ earlyTrialCountBitBudget vertexBits.length heightBits.length := by
  let width := positiveBinaryLengthWithWork vertexBits
  let level := addBinaryWordsWithWork heightBits [] true
  let square := mulBinaryWordsWithWork level.1 level.1
  let count := mulBinaryWordsWithWork square.1 width.1
  let h := heightBits.length
  let n := vertexBits.length
  obtain ⟨widthValue,widthLength,widthWork⟩ := positiveBinaryLengthWithWork_spec vertexBits
  obtain ⟨levelValue,levelLength,levelWork⟩ := addBinaryWordsWithWork_spec heightBits [] true
  obtain ⟨squareValue,squareLength,squareWork⟩ := mulBinaryWordsWithWork_spec level.1 level.1
  obtain ⟨countValue,countLength,countWork⟩ := mulBinaryWordsWithWork_spec square.1 width.1
  change binaryWordValue width.1 = _ at widthValue
  change width.1.length ≤ n+1 at widthLength
  change binaryWordValue level.1 = binaryWordValue heightBits+0+1 at levelValue
  change level.1.length ≤ h+1 at levelLength
  change level.2 ≤ 20*h+5 at levelWork
  change binaryWordValue square.1 = binaryWordValue level.1*binaryWordValue level.1 at squareValue
  change square.1.length ≤ level.1.length*(level.1.length+2) at squareLength
  change square.2 ≤ binaryMultiplicationWorkBudget level.1.length level.1.length at squareWork
  change binaryWordValue count.1 = binaryWordValue square.1*binaryWordValue width.1 at countValue
  change count.1.length ≤ width.1.length*(square.1.length+2) at countLength
  change count.2 ≤ binaryMultiplicationWorkBudget square.1.length width.1.length at countWork
  have squareCap : square.1.length ≤ (h+1)*(h+3) := by
    apply squareLength.trans
    exact Nat.mul_le_mul levelLength (Nat.add_le_add_right levelLength 2)
  have countCap : count.1.length ≤ (n+1)*((h+1)*(h+3)+2) :=
    countLength.trans (Nat.mul_le_mul widthLength (Nat.add_le_add_right squareCap 2))
  change binaryWordValue (false::false::false::false::count.1) = _ ∧
    count.1.length+4 ≤ (n+1)*((h+1)*(h+3)+2)+4 ∧
    width.2+level.2+square.2+count.2+11 ≤ earlyTrialCountBitBudget n h
  refine ⟨?_,Nat.add_le_add_right countCap 4,?_⟩
  · change 0+2*(0+2*(0+2*(0+2*binaryWordValue count.1))) = _
    rw [countValue,squareValue,levelValue,widthValue,Nat.add_zero]
    ring
  · exact Nat.add_le_add_right (Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add widthWork levelWork)
        (squareWork.trans (binaryMultiplicationWorkBudget_le levelLength levelLength)))
      (countWork.trans (binaryMultiplicationWorkBudget_le squareCap widthLength))) _

/-- With canonical vertex bits, the binary evaluator gives the exact count
used by the prepared early metric. -/
theorem earlyTrialCountWithBinaryWork_refines {vertexBits : List Bool} (heightBits : List Bool)
    (vertices : CanonicalBinaryWord vertexBits) :
    let out := earlyTrialCountWithBinaryWork vertexBits heightBits
    let reference := finEarlyTrialCountWithWordWork (binaryWordValue vertexBits) (binaryWordValue heightBits)
    binaryWordValue out.1 = reference.1.val ∧
      out.2 ≤ earlyTrialCountBitBudget vertexBits.length heightBits.length := by
  let reference := finEarlyTrialCountWithWordWork (binaryWordValue vertexBits) (binaryWordValue heightBits)
  obtain ⟨value,_,work⟩ := earlyTrialCountWithBinaryWork_spec vertexBits heightBits
  have width : max 1 vertexBits.length = (binaryWordValue vertexBits).log2+1 := by
    rw [← binaryWordValue_size_eq_length vertices,max_size_eq_log2_add_one]
  refine ⟨?_,work⟩
  rw [reference.1.property,earlyTrialCount,Fintype.card_fin]
  simpa only [width] using value

end OnlineReachabilityPreservers
