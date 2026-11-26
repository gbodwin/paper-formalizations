import OnlineReachabilityPreservers.SteinerBinaryArithmetic
import OnlineReachabilityPreservers.SteinerFinTraceReplayWork

/-! Evaluate the thin setup arithmetic on explicit binary words. -/

namespace OnlineReachabilityPreservers

private def positiveBinaryLengthWithWork (bits : List Bool) : List Bool × ℕ :=
  if bits.isEmpty then ([true],4) else
    let width := binaryWordLengthWithWork bits
    (width.1,width.2+2)

private theorem positiveBinaryLengthWithWork_spec (bits : List Bool) :
    let out := positiveBinaryLengthWithWork bits
    binaryWordValue out.1 = max 1 bits.length ∧ out.1.length ≤ bits.length+1 ∧
      out.2 ≤ 5+bits.length*(20*bits.length+9) := by
  cases bits with
  | nil => decide
  | cons b tail =>
    let bits := b::tail
    let width := binaryWordLengthWithWork bits
    obtain ⟨value,length,work⟩ := binaryWordLengthWithWork_spec bits
    change binaryWordValue width.1 = max 1 bits.length ∧ width.1.length ≤ bits.length+1 ∧
      width.2+2 ≤ 5+bits.length*(20*bits.length+9)
    change width.2 ≤ 3+bits.length*(20*bits.length+9) at work
    have nonempty : 1 ≤ bits.length := by simp [bits]
    rw [Nat.max_eq_right nonempty]
    exact ⟨value,length.trans (Nat.le_succ _),by omega⟩

/-- Return the thin update cap and rounding offset as binary words. The
input words encode the counts of vertices and arcs. -/
def thinReplayControlsWithBinaryWork (vertexBits arcBits : List Bool) : (List Bool × List Bool) × ℕ :=
  let vertexWidth := positiveBinaryLengthWithWork vertexBits
  let arcWidth := positiveBinaryLengthWithWork arcBits
  let scaled := mulBinaryWordsWithWork arcBits arcWidth.1
  let fuel := addBinaryWordsWithWork scaled.1 [] true
  ((fuel.1,false::false::vertexWidth.1),vertexWidth.2+arcWidth.2+scaled.2+fuel.2+9)

/-- Polynomial work in the lengths of the two binary input words. -/
def thinReplayControlsBitBudget (nBits mBits : ℕ) : ℕ :=
  (5+nBits*(20*nBits+9))+(5+mBits*(20*mBits+9))+
  (3+(mBits+1)*(20*((mBits+1)*(mBits+2))+12))+(20*((mBits+1)*(mBits+2))+5)+9

theorem thinReplayControlsWithBinaryWork_spec (vertexBits arcBits : List Bool) :
    let out := thinReplayControlsWithBinaryWork vertexBits arcBits
    binaryWordValue out.1.1 = binaryWordValue arcBits*(max 1 arcBits.length)+1 ∧
      binaryWordValue out.1.2 = 4*(max 1 vertexBits.length) ∧
      out.1.1.length ≤ (arcBits.length+1)*(arcBits.length+2)+1 ∧
      out.1.2.length ≤ vertexBits.length+3 ∧
      out.2 ≤ thinReplayControlsBitBudget vertexBits.length arcBits.length := by
  let vertexWidth := positiveBinaryLengthWithWork vertexBits
  let arcWidth := positiveBinaryLengthWithWork arcBits
  let scaled := mulBinaryWordsWithWork arcBits arcWidth.1
  let fuel := addBinaryWordsWithWork scaled.1 [] true
  let a := arcBits.length
  obtain ⟨vertexValue,vertexLength,vertexCost⟩ := positiveBinaryLengthWithWork_spec vertexBits
  obtain ⟨arcValue,arcLength,arcCost⟩ := positiveBinaryLengthWithWork_spec arcBits
  obtain ⟨scaledValue,scaledLength,scaledCost⟩ := mulBinaryWordsWithWork_spec arcBits arcWidth.1
  obtain ⟨fuelValue,fuelLength,fuelCost⟩ := addBinaryWordsWithWork_spec scaled.1 [] true
  have powLength : scaled.1.length ≤ (a+1)*(a+2) :=
    scaledLength.trans (Nat.mul_le_mul_right _ arcLength)
  have scaleWork : scaled.2 ≤ 3+(a+1)*(20*((a+1)*(a+2))+12) := by
    change scaled.2 ≤ 3+arcWidth.1.length*(20*(arcWidth.1.length*(a+2))+12) at scaledCost
    exact scaledCost.trans (by gcongr)
  have fuelWork : fuel.2 ≤ 20*((a+1)*(a+2))+5 := by
    change fuel.2 ≤ 20*(scaled.1.length+0)+5 at fuelCost
    have fits : scaled.1.length+0 ≤ (a+1)*(a+2) := by simpa only [Nat.add_zero] using powLength
    exact fuelCost.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 20 fits) 5)
  change binaryWordValue fuel.1 = _ ∧ binaryWordValue (false::false::vertexWidth.1) = _ ∧
    fuel.1.length ≤ (a+1)*(a+2)+1 ∧ vertexWidth.1.length+2 ≤ vertexBits.length+3 ∧
    vertexWidth.2+arcWidth.2+scaled.2+fuel.2+9 ≤ thinReplayControlsBitBudget vertexBits.length a
  change binaryWordValue fuel.1 = binaryWordValue scaled.1+0+1 at fuelValue
  change binaryWordValue scaled.1 = binaryWordValue arcBits*binaryWordValue arcWidth.1 at scaledValue
  change binaryWordValue arcWidth.1 = _ at arcValue
  change binaryWordValue vertexWidth.1 = _ at vertexValue
  change vertexWidth.1.length ≤ vertexBits.length+1 at vertexLength
  change fuel.1.length ≤ scaled.1.length+0+1 at fuelLength
  refine ⟨by rw [fuelValue,scaledValue,arcValue,Nat.add_zero],?_,by omega,by omega,?_⟩
  · change 0+2*(0+2*binaryWordValue vertexWidth.1) = _
    rw [vertexValue]
    omega
  · exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add vertexCost arcCost) scaleWork) fuelWork) _

/-- On canonical binary inputs these are the two parameters used by the
measured complete replay, with a separate bit-work allowance. -/
theorem thinReplayControlsWithBinaryWork_refines {vertexBits arcBits : List Bool}
    (vertices : CanonicalBinaryWord vertexBits) (arcs : CanonicalBinaryWord arcBits) :
    let out := thinReplayControlsWithBinaryWork vertexBits arcBits
    let reference := finThinReplayControlsWithWordWork (binaryWordValue vertexBits) (binaryWordValue arcBits)
    binaryWordValue out.1.1 = reference.fuel ∧ binaryWordValue out.1.2 = reference.roundingOffset ∧
      out.2 ≤ thinReplayControlsBitBudget vertexBits.length arcBits.length := by
  let reference := finThinReplayControlsWithWordWork (binaryWordValue vertexBits) (binaryWordValue arcBits)
  obtain ⟨fuel,offset,_,_,work⟩ := thinReplayControlsWithBinaryWork_spec vertexBits arcBits
  have vertexWidth : max 1 vertexBits.length = (binaryWordValue vertexBits).log2+1 := by
    rw [← binaryWordValue_size_eq_length vertices,max_size_eq_log2_add_one]
  have arcWidth : max 1 arcBits.length = (binaryWordValue arcBits).log2+1 := by
    rw [← binaryWordValue_size_eq_length arcs,max_size_eq_log2_add_one]
  refine ⟨?_,?_,work⟩
  · rw [reference.fuel_eq]
    simpa only [arcWidth] using fuel
  · rw [reference.roundingOffset_eq]
    simpa only [vertexWidth] using offset

end OnlineReachabilityPreservers
