import Mathlib

/-!
# Unreduced nonnegative rational arithmetic

The executable representation stores a natural numerator and a positive natural
denominator. Arithmetic deliberately does not reduce by gcd. The semantic map
to `ℚ≥0` is used only in proofs; executable arithmetic, comparisons and ceilings
operate on the stored natural numbers. Thus the intermediate size estimates
below cover the actual representation, rather than only a canonical rational.

The charged model counts natural arithmetic, comparisons, branches and record
allocation as word operations. It is an explicit mathematical operation model,
not a claim about every instruction executed by Lean's runtime. Result pairs
carrying ghost operation counters are instrumentation and are not charged;
the executable rational records and their stored fields are charged.
-/

namespace DirectedFlowCutGap.RawNonnegativeRational

open scoped NNRat NNReal

structure Code where
  num : ℕ
  den : ℕ
  positive_den : 0 < den
  deriving DecidableEq

namespace Code

def zero : Code := ⟨0,1,by decide⟩
def one : Code := ⟨1,1,by decide⟩
def ofNat (n : ℕ) : Code := ⟨n,1,by decide⟩
def ofNNRat (q : ℚ≥0) : Code := ⟨q.num,q.den,q.den_pos⟩

def value (q : Code) : ℚ≥0 := (q.num : ℚ≥0) / q.den
noncomputable def realValue (q : Code) : ℝ≥0 := (q.value : ℝ≥0)

@[simp] theorem value_zero : zero.value = 0 := by simp [value,zero]
@[simp] theorem value_one : one.value = 1 := by simp [value,one]
@[simp] theorem value_ofNat (n : ℕ) : (ofNat n).value = n := by simp [value,ofNat]
@[simp] theorem value_ofNNRat (q : ℚ≥0) : (ofNNRat q).value = q := NNRat.num_div_den q

@[simp] theorem value_eq_zero (q : Code) : q.value = 0 ↔ q.num = 0 := by
  simp [value,ne_of_gt q.positive_den]

theorem value_pos (q : Code) : 0 < q.value ↔ 0 < q.num := by
  simp only [pos_iff_ne_zero,ne_eq,value_eq_zero]

def add (a b : Code) : Code :=
  ⟨a.num*b.den+b.num*a.den,a.den*b.den,Nat.mul_pos a.positive_den b.positive_den⟩

def mul (a b : Code) : Code :=
  ⟨a.num*b.num,a.den*b.den,Nat.mul_pos a.positive_den b.positive_den⟩

/-- Total division, with the field convention `a / 0 = 0`. The normalization
caller checks the objective first, so its positive arm never uses this fallback. -/
def div (a b : Code) : Code :=
  if h : b.num = 0 then zero else
    ⟨a.num*b.den,a.den*b.num,Nat.mul_pos a.positive_den (Nat.pos_of_ne_zero h)⟩

def le (a b : Code) : Bool := decide (a.num*b.den ≤ b.num*a.den)

/-- Actual natural division; no rational normalization or real arithmetic. -/
def ceil (a : Code) : ℕ := (a.num+a.den-1)/a.den

@[simp] theorem value_add (a b : Code) : (a.add b).value = a.value+b.value := by
  dsimp [add,value]
  push_cast
  simpa only [mul_comm] using (div_add_div (a.num : ℚ≥0) (b.num : ℚ≥0)
    (show (a.den : ℚ≥0) ≠ 0 by exact_mod_cast ne_of_gt a.positive_den)
    (show (b.den : ℚ≥0) ≠ 0 by exact_mod_cast ne_of_gt b.positive_den)).symm

@[simp] theorem value_mul (a b : Code) : (a.mul b).value = a.value*b.value := by
  simp only [mul,value,Nat.cast_mul]
  exact (div_mul_div_comm ..).symm

@[simp] theorem value_div (a b : Code) : (a.div b).value = a.value/b.value := by
  unfold div
  split_ifs with h
  · simp [value,h,zero]
  · simp only [value,Nat.cast_mul]
    exact (div_div_div_eq ..).symm

@[simp] theorem le_eq_true (a b : Code) : a.le b = true ↔ a.value ≤ b.value := by
  rw [le,decide_eq_true_eq,value,value,div_le_div_iff₀]
  · norm_cast
  · exact_mod_cast a.positive_den
  · exact_mod_cast b.positive_den

@[simp] theorem ceil_eq (a : Code) : a.ceil = ⌈a.value⌉₊ := by
  apply eq_of_forall_ge_iff
  intro n
  change a.num ⌈/⌉ a.den ≤ n ↔ ⌈a.value⌉₊ ≤ n
  rw [ceilDiv_le_iff_le_mul a.positive_den,Nat.ceil_le,value,div_le_iff₀]
  · norm_cast
    simp [Nat.mul_comm]
  · exact_mod_cast a.positive_den

/-- Seven word operations: three multiplications, addition, two stored fields
and result allocation. Proof fields are erased. -/
def addWithCost (a b : Code) : Code × ℕ := (a.add b,7)
def mulWithCost (a b : Code) : Code × ℕ := (a.mul b,5)

/-- Zero comparison, branch, at most two multiplications, and allocation. -/
def divWithCost (a b : Code) : Code × ℕ := (a.div b,7)
def leWithCost (a b : Code) : Bool × ℕ := (a.le b,4)
def ceilWithCost (a : Code) : ℕ × ℕ := (a.ceil,4)

/-- Inclusive power-of-two bounds make zero-width constants convenient. -/
def Bounded (q : Code) (b : ℕ) : Prop := q.num ≤ 2^b ∧ q.den ≤ 2^b

theorem bounded_zero : zero.Bounded 0 := by norm_num [Bounded,zero]
theorem bounded_one : one.Bounded 0 := by norm_num [Bounded,one]

theorem bounded_mono {q : Code} {a b : ℕ} (h : q.Bounded a) (hab : a ≤ b) :
    q.Bounded b := by
  have hp : 2^a ≤ (2:ℕ)^b := Nat.pow_le_pow_right (by decide) hab
  exact ⟨h.1.trans hp,h.2.trans hp⟩

theorem bounded_add {q r : Code} {a b : ℕ} (hq : q.Bounded a) (hr : r.Bounded b) :
    (q.add r).Bounded (a+b+1) := by
  have h₁ := Nat.mul_le_mul hq.1 hr.2
  have h₂ := Nat.mul_le_mul hr.1 hq.2
  have hd := Nat.mul_le_mul hq.2 hr.2
  have hp : (2:ℕ)^(a+b+1) = 2^a*2^b*2 := by rw [pow_add,pow_add]; norm_num
  rw [Bounded,add,hp]
  constructor <;> dsimp only
  · nlinarith
  · nlinarith

theorem bounded_mul {q r : Code} {a b : ℕ} (hq : q.Bounded a) (hr : r.Bounded b) :
    (q.mul r).Bounded (a+b) := by
  rw [Bounded,mul,pow_add]
  exact ⟨Nat.mul_le_mul hq.1 hr.1,Nat.mul_le_mul hq.2 hr.2⟩

theorem bounded_div {q r : Code} {a b : ℕ} (hq : q.Bounded a) (hr : r.Bounded b) :
    (q.div r).Bounded (a+b) := by
  unfold div
  split_ifs
  · exact bounded_mono bounded_zero (by omega)
  · rw [Bounded,pow_add]
    exact ⟨Nat.mul_le_mul hq.1 hr.2,Nat.mul_le_mul hq.2 hr.1⟩

/-- The cross-products used by comparison are bounded before comparison. -/
theorem comparison_intermediates {q r : Code} {a b : ℕ}
    (hq : q.Bounded a) (hr : r.Bounded b) :
    q.num*r.den ≤ 2^(a+b) ∧ r.num*q.den ≤ 2^(a+b) := by
  rw [pow_add]
  exact ⟨Nat.mul_le_mul hq.1 hr.2,by nlinarith [Nat.mul_le_mul hr.1 hq.2]⟩

/-- The ceiling's addition is bounded before subtraction and division. -/
theorem ceiling_intermediate {q : Code} {b : ℕ} (h : q.Bounded b) :
    q.num+q.den ≤ 2^(b+1) := by
  rcases h with ⟨hn,hd⟩
  rw [pow_succ]
  omega

theorem bounded_bits {q : Code} {b : ℕ} (h : q.Bounded b) :
    Nat.size q.num ≤ b+1 ∧ Nat.size q.den ≤ b+1 := by
  exact ⟨(Nat.size_le_size h.1).trans_eq Nat.size_pow,
    (Nat.size_le_size h.2).trans_eq Nat.size_pow⟩

end Code

end DirectedFlowCutGap.RawNonnegativeRational
