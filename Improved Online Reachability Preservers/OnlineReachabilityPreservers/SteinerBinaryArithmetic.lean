import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring

/-! Count bit operations in concrete least-significant-bit-first arithmetic. -/

namespace OnlineReachabilityPreservers

private def bitDigit (b : Bool) : ℕ := if b then 1 else 0

/-- Decode a least-significant-bit-first word. High zero bits are allowed. -/
def binaryWordValue : List Bool → ℕ
  | [] => 0
  | b::tail => bitDigit b+2*binaryWordValue tail

private theorem binaryWordValue_head_tail (word : List Bool) :
    binaryWordValue word = bitDigit (word.headD false)+2*binaryWordValue word.tail := by
  cases word <;> rfl

private def sumBit (x y carry : Bool) : Bool := Bool.xor (Bool.xor x y) carry

private def carryBit (x y carry : Bool) : Bool := (x && y) || ((x || y) && carry)

private theorem fullAdder_value (x y carry : Bool) :
    bitDigit (sumBit x y carry)+2*bitDigit (carryBit x y carry) = bitDigit x+bitDigit y+bitDigit carry := by
  cases x <;> cases y <;> cases carry <;> decide

private theorem binaryWord_shorter {x y : List Bool} (empty : ¬ (x = [] ∧ y = [])) :
    x.tail.length+y.tail.length < x.length+y.length := by
  cases x <;> cases y <;> simp_all
  omega

/-- Add binary words with a carry. The tally charges the emptiness tests,
local Boolean operations, and construction of one output bit at each step. -/
def addBinaryWordsWithWork (x y : List Bool) (carry : Bool) : List Bool × ℕ :=
  if empty : x = [] ∧ y = [] then
    (if carry then [true] else [],5)
  else
    let first := x.headD false
    let second := y.headD false
    let rest := addBinaryWordsWithWork x.tail y.tail (carryBit first second carry)
    (sumBit first second carry::rest.1,rest.2+20)
termination_by x.length+y.length
decreasing_by exact binaryWord_shorter empty

theorem addBinaryWordsWithWork_spec (x y : List Bool) (carry : Bool) :
    let out := addBinaryWordsWithWork x y carry
    binaryWordValue out.1 = binaryWordValue x+binaryWordValue y+bitDigit carry ∧
      out.1.length ≤ x.length+y.length+1 ∧ out.2 ≤ 20*(x.length+y.length)+5 := by
  induction size : x.length+y.length using Nat.strong_induction_on generalizing x y carry with
  | h n previous =>
    by_cases empty : x = [] ∧ y = []
    · obtain ⟨rfl,rfl⟩ := empty
      cases carry <;> simp [addBinaryWordsWithWork,binaryWordValue,bitDigit]
    rw [addBinaryWordsWithWork,dite_eq_right empty]
    let first := x.headD false
    let second := y.headD false
    let extra := carryBit first second carry
    let tail := addBinaryWordsWithWork x.tail y.tail extra
    have less := binaryWord_shorter empty
    obtain ⟨value,length,work⟩ := previous (x.tail.length+y.tail.length) (by rwa [← size])
      x.tail y.tail extra rfl
    rw [← size]
    change binaryWordValue (sumBit first second carry::tail.1) = _ ∧
      tail.1.length+1 ≤ x.length+y.length+1 ∧ tail.2+20 ≤ 20*(x.length+y.length)+5
    change binaryWordValue tail.1 = _ at value
    change tail.1.length ≤ x.tail.length+y.tail.length+1 at length
    change tail.2 ≤ 20*(x.tail.length+y.tail.length)+5 at work
    refine ⟨?_,by omega,by omega⟩
    rw [binaryWordValue,value]
    have digit := fullAdder_value first second carry
    have vx := binaryWordValue_head_tail x
    have vy := binaryWordValue_head_tail y
    change binaryWordValue x = bitDigit first+2*binaryWordValue x.tail at vx
    change binaryWordValue y = bitDigit second+2*binaryWordValue y.tail at vy
    change bitDigit (sumBit first second carry)+2*bitDigit extra = _ at digit
    omega

/-- Multiply by shift and addition, scanning the second word one bit at a time. -/
def mulBinaryWordsWithWork (x : List Bool) : List Bool → List Bool × ℕ
  | [] => ([],3)
  | b::tail =>
    let lower := mulBinaryWordsWithWork x tail
    let shifted := false::lower.1
    if b then
      let added := addBinaryWordsWithWork x shifted false
      (added.1,lower.2+added.2+7)
    else (shifted,lower.2+7)

private def binaryMulStepBudget (x y : ℕ) : ℕ := 20*(y*(x+2))+12

/-- An upper bound for the shift-and-add loop at the supplied word lengths. -/
def binaryMultiplicationWorkBudget (x y : ℕ) : ℕ := 3+y*binaryMulStepBudget x y

theorem binaryMultiplicationWorkBudget_le {x x' y y' : ℕ}
    (left : x ≤ x') (right : y ≤ y') :
    binaryMultiplicationWorkBudget x y ≤ binaryMultiplicationWorkBudget x' y' := by
  unfold binaryMultiplicationWorkBudget binaryMulStepBudget
  gcongr

theorem mulBinaryWordsWithWork_spec (x y : List Bool) :
    let out := mulBinaryWordsWithWork x y
    binaryWordValue out.1 = binaryWordValue x*binaryWordValue y ∧
      out.1.length ≤ y.length*(x.length+2) ∧ out.2 ≤ 3+y.length*binaryMulStepBudget x.length y.length := by
  induction y with
  | nil => simp [mulBinaryWordsWithWork,binaryWordValue]
  | cons b tail ih =>
    let lower := mulBinaryWordsWithWork x tail
    let shifted := false::lower.1
    let width := tail.length*(x.length+2)
    let nextWidth := (tail.length+1)*(x.length+2)
    let oldCap := binaryMulStepBudget x.length tail.length
    let newCap := binaryMulStepBudget x.length (tail.length+1)
    obtain ⟨value,length,work⟩ := ih
    change binaryWordValue lower.1 = _ at value
    change lower.1.length ≤ width at length
    change lower.2 ≤ 3+tail.length*oldCap at work
    have shiftedValue : binaryWordValue shifted = 2*(binaryWordValue x*binaryWordValue tail) := by
      change 0+2*binaryWordValue lower.1 = _
      rw [value,Nat.zero_add]
    have wider : nextWidth = width+(x.length+2) := by unfold nextWidth width; rw [Nat.add_mul,Nat.one_mul]
    have monotone : oldCap ≤ newCap := by
      unfold oldCap newCap binaryMulStepBudget
      gcongr
      exact Nat.le_add_right _ _
    have enough : lower.2 ≤ 3+tail.length*newCap :=
      work.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ monotone) _)
    cases b with
    | false =>
      change binaryWordValue shifted = _ ∧ lower.1.length+1 ≤ nextWidth ∧
        lower.2+7 ≤ 3+(tail.length+1)*newCap
      refine ⟨?_,by omega,?_⟩
      · rw [shiftedValue,binaryWordValue]
        simp [bitDigit]
        ring
      · have space : 7 ≤ newCap := by unfold newCap binaryMulStepBudget; omega
        rw [Nat.add_mul,Nat.one_mul]
        omega
    | true =>
      let added := addBinaryWordsWithWork x shifted false
      obtain ⟨same,short,cost⟩ := addBinaryWordsWithWork_spec x shifted false
      change binaryWordValue added.1 = _ at same
      change added.1.length ≤ x.length+(lower.1.length+1)+1 at short
      change added.2 ≤ 20*(x.length+(lower.1.length+1))+5 at cost
      change binaryWordValue added.1 = _ ∧ added.1.length ≤ nextWidth ∧
        lower.2+added.2+7 ≤ 3+(tail.length+1)*newCap
      refine ⟨?_,by omega,?_⟩
      · rw [same,shiftedValue,binaryWordValue]
        simp [bitDigit]
        ring
      · have localWork : added.2+7 ≤ newCap := by
          change _ ≤ 20*nextWidth+12
          omega
        rw [Nat.add_mul,Nat.one_mul]
        omega

/-- Store the number of input bits as a binary word, incrementing once
for each input cell. -/
def binaryWordLengthWithWork : List Bool → List Bool × ℕ
  | [] => ([],3)
  | _::tail =>
    let width := binaryWordLengthWithWork tail
    let next := addBinaryWordsWithWork width.1 [] true
    (next.1,width.2+next.2+4)

theorem binaryWordLengthWithWork_spec (word : List Bool) :
    let out := binaryWordLengthWithWork word
    binaryWordValue out.1 = word.length ∧ out.1.length ≤ word.length ∧
      out.2 ≤ 3+word.length*(20*word.length+9) := by
  induction word with
  | nil => simp [binaryWordLengthWithWork,binaryWordValue]
  | cons bit tail ih =>
    let base := binaryWordLengthWithWork tail
    let out := addBinaryWordsWithWork base.1 [] true
    obtain ⟨value,short,work⟩ := ih
    obtain ⟨added,length,cost⟩ := addBinaryWordsWithWork_spec base.1 [] true
    change binaryWordValue base.1 = _ at value
    change base.1.length ≤ tail.length at short
    change base.2 ≤ 3+tail.length*(20*tail.length+9) at work
    change binaryWordValue out.1 = tail.length+1 ∧ out.1.length ≤ tail.length+1 ∧
      base.2+out.2+4 ≤ 3+(tail.length+1)*(20*(tail.length+1)+9)
    change binaryWordValue out.1 = binaryWordValue base.1+binaryWordValue []+bitDigit true at added
    change out.1.length ≤ base.1.length+0+1 at length
    change out.2 ≤ 20*(base.1.length+0)+5 at cost
    have after : base.2 ≤ 3+tail.length*(20*(tail.length+1)+9) := by
      apply work.trans
      gcongr
      exact Nat.le_add_right _ _
    refine ⟨by simpa only [value,binaryWordValue,Nat.add_zero,bitDigit,ite_true] using added,
      by omega,?_⟩
    rw [Nat.add_mul,Nat.one_mul]
    omega

/-- The empty word encodes zero. A nonempty canonical word ends in one. -/
def CanonicalBinaryWord (word : List Bool) : Prop := word = [] ∨ word.getLast? = some true

private theorem binaryWordValue_lt_pow (word : List Bool) : binaryWordValue word < 2^word.length := by
  induction word with
  | nil => decide
  | cons bit tail inside =>
    rw [binaryWordValue,List.length_cons,pow_succ]
    cases bit <;> simp only [bitDigit,Bool.false_eq_true,ite_false,ite_true] <;> omega

private theorem binaryWordValue_pow_le_of_last {word : List Bool} (last : word.getLast? = some true) :
    2^(word.length-1) ≤ binaryWordValue word := by
  induction word with
  | nil => simp at last
  | cons bit tail ih =>
    cases tail with
    | nil =>
      have on : bit = true := by simpa using last
      subst bit
      decide
    | cons b bs =>
      have suffix : (b::bs).getLast? = some true := by simpa using last
      have lower := ih suffix
      rw [binaryWordValue,List.length_cons,Nat.add_sub_cancel]
      rw [List.length_cons] at lower ⊢
      rw [Nat.add_sub_cancel] at lower
      rw [pow_succ]
      omega

/-- Canonical input length agrees with the bit length of its value. -/
theorem binaryWordValue_size_eq_length {word : List Bool} (canonical : CanonicalBinaryWord word) :
    (binaryWordValue word).size = word.length := by
  rcases canonical with rfl | last
  · decide
  have nonempty : word ≠ [] := by intro nil; simp [nil] at last
  have positive : 0 < word.length := by cases word <;> simp_all
  have upper := Nat.size_le.mpr (binaryWordValue_lt_pow word)
  have lower := Nat.lt_size.mpr (binaryWordValue_pow_le_of_last last)
  omega

/-- Return the binary encoding of the input length, with a minimum of one. -/
def positiveBinaryLengthWithWork (bits : List Bool) : List Bool × ℕ :=
  if bits.isEmpty then ([true],4) else
    let width := binaryWordLengthWithWork bits
    (width.1,width.2+2)

theorem positiveBinaryLengthWithWork_spec (bits : List Bool) :
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

/-- Test whether every supplied bit is zero, stopping at the first one. -/
def binaryZeroWithWork : List Bool → Bool × ℕ
  | [] => (true,3)
  | bit::tail =>
    if bit then (false,4)
    else
      let out := binaryZeroWithWork tail
      (out.1,out.2+4)

theorem binaryZeroWithWork_spec (bits : List Bool) :
    let out := binaryZeroWithWork bits
    out.1 = decide (binaryWordValue bits = 0) ∧ out.2 ≤ 4*bits.length+3 := by
  induction bits with
  | nil => decide
  | cons bit tail ih =>
    cases bit with
    | true =>
      change false = decide (1+2*binaryWordValue tail = 0) ∧ 4 ≤ 4*(tail.length+1)+3
      exact ⟨(decide_eq_false (by omega)).symm,by omega⟩
    | false =>
      let out := binaryZeroWithWork tail
      obtain ⟨equal,work⟩ := ih
      change out.1 = decide (0+2*binaryWordValue tail = 0) ∧ out.2+4 ≤ 4*(tail.length+1)+3
      change out.2 ≤ 4*tail.length+3 at work
      exact ⟨by simpa using equal,by omega⟩

/-- Decrement a fixed-width word, letting a borrow wrap at the end. -/
def binaryDecrementWithWork : List Bool → List Bool × ℕ
  | [] => ([],3)
  | bit::tail =>
    if bit then (false::tail,4)
    else
      let out := binaryDecrementWithWork tail
      (true::out.1,out.2+5)

theorem binaryDecrementWithWork_spec (bits : List Bool) :
    let out := binaryDecrementWithWork bits
    out.1.length = bits.length ∧ out.2 ≤ 5*bits.length+3 ∧
      (0 < binaryWordValue bits → binaryWordValue out.1+1 = binaryWordValue bits) := by
  induction bits with
  | nil => decide
  | cons bit tail ih =>
    cases bit with
    | true =>
      change tail.length+1 = tail.length+1 ∧ 4 ≤ 5*(tail.length+1)+3 ∧
        (0 < 1+2*binaryWordValue tail → 0+2*binaryWordValue tail+1 = 1+2*binaryWordValue tail)
      exact ⟨rfl,by omega,fun _ => by omega⟩
    | false =>
      let out := binaryDecrementWithWork tail
      obtain ⟨size,work,value⟩ := ih
      change out.1.length = tail.length at size
      change out.2 ≤ 5*tail.length+3 at work
      change out.1.length+1 = tail.length+1 ∧ out.2+5 ≤ 5*(tail.length+1)+3 ∧
        (0 < 0+2*binaryWordValue tail → 1+2*binaryWordValue out.1+1 = 0+2*binaryWordValue tail)
      refine ⟨congrArg (·+1) size,by omega,fun positive => ?_⟩
      have lower := value (by omega)
      change binaryWordValue out.1+1 = binaryWordValue tail at lower
      omega

private def nextBinaryBorrow (left right borrow : Bool) : Bool :=
  if left == right then borrow else !left

private theorem binaryBorrow_digit (left right borrow : Bool) :
    nextBinaryBorrow left right borrow = decide (bitDigit left < bitDigit right+bitDigit borrow) := by
  cases left <;> cases right <;> cases borrow <;> decide

/-- Compare the two words by scanning the borrow in binary subtraction. -/
def binaryLessWithWork (left right : List Bool) (borrow : Bool) : Bool × ℕ :=
  if empty : left = [] ∧ right = [] then (borrow,4) else
    let next := nextBinaryBorrow (left.headD false) (right.headD false) borrow
    let result := binaryLessWithWork left.tail right.tail next
    (result.1,result.2+14)
termination_by left.length+right.length
decreasing_by exact binaryWord_shorter empty

theorem binaryLessWithWork_spec (left right : List Bool) (borrow : Bool) :
    let out := binaryLessWithWork left right borrow
    out.1 = decide (binaryWordValue left < binaryWordValue right+bitDigit borrow) ∧
      out.2 ≤ 14*(left.length+right.length)+4 := by
  induction total : left.length+right.length using Nat.strong_induction_on generalizing left right borrow with
  | h steps previous =>
    by_cases empty : left = [] ∧ right = []
    · obtain ⟨rfl,rfl⟩ := empty
      cases borrow <;> simp [binaryLessWithWork,binaryWordValue,bitDigit]
    rw [binaryLessWithWork,dite_eq_right empty]
    let x := left.headD false
    let y := right.headD false
    let extra := nextBinaryBorrow x y borrow
    let result := binaryLessWithWork left.tail right.tail extra
    have shorter := binaryWord_shorter empty
    obtain ⟨value,work⟩ := previous (left.tail.length+right.tail.length) (by rwa [← total])
      left.tail right.tail extra rfl
    rw [← total]
    change result.1 = decide (binaryWordValue left < binaryWordValue right+bitDigit borrow) ∧
      result.2+14 ≤ 14*(left.length+right.length)+4
    change result.1 = _ at value
    change result.2 ≤ 14*(left.tail.length+right.tail.length)+4 at work
    refine ⟨?_,by omega⟩
    rw [value,binaryWordValue_head_tail left,binaryWordValue_head_tail right]
    change decide (binaryWordValue left.tail < binaryWordValue right.tail+bitDigit extra) =
      decide (bitDigit x+2*binaryWordValue left.tail < bitDigit y+2*binaryWordValue right.tail+bitDigit borrow)
    rw [decide_eq_decide]
    have digit := binaryBorrow_digit x y borrow
    change extra = _ at digit
    have bit : ∀ b : Bool, bitDigit b ≤ 1 := by intro b; cases b <;> decide
    have leftBit := bit x
    have rightBit := bit y
    have borrowBit := bit borrow
    by_cases below : bitDigit x < bitDigit y+bitDigit borrow
    · rw [decide_eq_true below] at digit
      rw [digit]
      change binaryWordValue left.tail < binaryWordValue right.tail+1 ↔ _
      omega
    · rw [decide_eq_false below] at digit
      rw [digit]
      change binaryWordValue left.tail < binaryWordValue right.tail+0 ↔ _
      omega

/-- Compare two binary words, allowing different lengths and high zero padding. -/
theorem binaryLessWithWork_noBorrow_spec (left right : List Bool) :
    let out := binaryLessWithWork left right false
    out.1 = decide (binaryWordValue left < binaryWordValue right) ∧
      out.2 ≤ 14*(left.length+right.length)+4 := by
  simpa only [bitDigit,Bool.false_eq_true,ite_false,Nat.add_zero] using binaryLessWithWork_spec left right false

end OnlineReachabilityPreservers
