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

end OnlineReachabilityPreservers
