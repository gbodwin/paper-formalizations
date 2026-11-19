import DirectedFlowCutGap.BinaryEuclidean
import DirectedFlowCutGap.BinaryRawRational

/-! Exact coprime rational fields via binary Euclid and measured division. -/

namespace DirectedFlowCutGap.BinaryRationalNormalize

open scoped NNRat
open BinaryArithmetic BinaryRational BinaryDivision RawNonnegativeRational

def reduce (q : Fraction) : Fraction × ℕ :=
  let g := BinaryEuclidean.gcd q.num q.den
  let a := divide q.num g.1
  let b := divide q.den g.1
  (⟨a.quotient,b.quotient,by
    rw [(divide_spec q.den g.1).1,BinaryEuclidean.gcd_value]
    exact Nat.div_gcd_pos_of_pos_right _ q.den_pos⟩,g.2+a.steps+b.steps+8)

theorem reduce_fields (q : Fraction) :
    value (reduce q).1.num = value q.num/(value q.num).gcd (value q.den) ∧
      value (reduce q).1.den = value q.den/(value q.num).gcd (value q.den) := by
  constructor <;>
    simp only [reduce,(divide_spec _ _).1,BinaryEuclidean.gcd_value]

private theorem normalized_fields (c : Code) :
    c.value.num=c.num/c.num.gcd c.den ∧ c.value.den=c.den/c.num.gcd c.den := by
  have normalized : (c.value : ℚ)=Rat.normalize (Int.ofNat c.num) c.den c.positive_den.ne' := by
    calc
      (c.value : ℚ) = (c.num : ℚ)/c.den := by simp [Code.value]
      _ = mkRat (Int.ofNat c.num) c.den := (Rat.mkRat_eq_div _ _).symm
      _ = _ := (Rat.normalize_eq_mkRat c.positive_den.ne').symm
  constructor
  · rw [← NNRat.natAbs_num_coe,normalized,Rat.num_normalize,Int.natAbs_ofNat']
    change ((c.num : ℤ) / ((c.num.gcd c.den : ℕ) : ℤ)).natAbs = _
    rw [← Int.natCast_ediv,Int.natAbs_natCast]
  · change (c.value : ℚ).den=_
    rw [normalized,Rat.den_normalize,Int.natAbs_ofNat']

private theorem equal_code {a b : Code} (num : a.num=b.num) (den : a.den=b.den) : a=b := by
  cases a
  cases b
  simp_all

theorem reduce_value (q : Fraction) : BinaryRational.decode (reduce q).1=Code.ofNNRat (BinaryRational.decode q).value := by
  have h := normalized_fields (BinaryRational.decode q)
  obtain ⟨a,b⟩ := reduce_fields q
  have num : (BinaryRational.decode (reduce q).1).num=(Code.ofNNRat (BinaryRational.decode q).value).num :=
    a.trans h.1.symm
  have den : (BinaryRational.decode (reduce q).1).den=(Code.ofNNRat (BinaryRational.decode q).value).den :=
    b.trans h.2.symm
  exact equal_code num den

theorem reduce_width {q : Fraction} {B : ℕ} (fits : StoredBounded q B) :
    StoredBounded (reduce q).1 B := by
  unfold StoredBounded reduce
  dsimp only
  constructor
  · rw [(divide_spec _ _).2.2.1]
    exact (Nat.size_le_size (Nat.div_le_self _ _)).trans ((Nat.size_le.mpr (value_lt q.num)).trans fits.1)
  · rw [(divide_spec _ _).2.2.1]
    exact (Nat.size_le_size (Nat.div_le_self _ _)).trans ((Nat.size_le.mpr (value_lt q.den)).trans fits.2)

def budgetBits {R : Type*} [Semiring R] (B : R) : R :=
  B*BinaryEuclidean.stepBudget B+2048*(B+1)^2+9

theorem reduce_paid {q : Fraction} {B : ℕ} (fits : StoredBounded q B) :
    (reduce q).2 ≤ budgetBits B := by
  let g := BinaryEuclidean.gcd q.num q.den
  obtain ⟨wid,paid⟩ := BinaryEuclidean.gcd_paid fits.1 fits.2
  have a := divide_charge_bound fits.1 wid
  have b := divide_charge_bound fits.2 wid
  change g.2 ≤ _ at paid
  change (divide q.num g.1).steps ≤ _ at a
  change (divide q.den g.1).steps ≤ _ at b
  change g.2+(divide q.num g.1).steps+(divide q.den g.1).steps+8 ≤ _
  unfold budgetBits
  omega

def normalize (q : Code) : Code × ℕ :=
  let source := BinaryRawRational.encode q
  let reduced := reduce source.1
  let result := BinaryRawRational.decode reduced.1
  (result.1,source.2+reduced.2+result.2+4)

@[simp] theorem normalize_value (q : Code) : (normalize q).1=Code.ofNNRat q.value := by
  simp only [normalize,BinaryRawRational.decode_value,reduce_value,BinaryRawRational.encode_value]

theorem normalize_width {q : Code} {B : ℕ} (fits : q.Bounded B) : (normalize q).1.Bounded B := by
  rw [normalize_value]
  obtain ⟨a,b⟩ := normalized_fields q
  change q.value.num ≤ 2^B ∧ q.value.den ≤ 2^B
  rw [a,b]
  exact ⟨(Nat.div_le_self _ _).trans fits.1,(Nat.div_le_self _ _).trans fits.2⟩

def budget {R : Type*} [Semiring R] (B : R) : R := 80*(B+2)^2+budgetBits (B+1)+4

theorem normalize_paid {q : Code} {B : ℕ} (fits : q.Bounded B) : (normalize q).2 ≤ budget B := by
  have a := BinaryRawRational.encode_paid fits
  have b := reduce_paid (BinaryRawRational.encode_width fits)
  have c := BinaryRawRational.decode_paid (reduce_width (BinaryRawRational.encode_width fits))
  unfold normalize budget
  dsimp only
  change (BinaryRawRational.decode (reduce (BinaryRawRational.encode q).1).1).2 ≤ 40*(B+2)^2 at c
  omega

end DirectedFlowCutGap.BinaryRationalNormalize
