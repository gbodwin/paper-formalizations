import DirectedFlowCutGap.BinaryEdgeFamilyArithmetic

/-! Compute the subunit test and the exact horizon from the measured mass.
The loops depend on the bit length of the ceiling of the magnitude. -/

namespace DirectedFlowCutGap.BinaryEdgeFamilyControls

open scoped NNRat
open BinaryArithmetic RawNonnegativeRational

structure Controls where
  small : Bool
  horizon : ℕ
  paid : ℕ

private def magnitude (n : ℕ) (mass : Code) : Code × ℕ :=
  let doubled := BinaryRawRational.mul (Code.ofNat 2) mass
  let shifted := BinaryRawRational.add doubled.1 (Code.ofNat n)
  let q := BinaryRawRational.mul (Code.ofNat n) shifted.1
  (q.1,doubled.2+shifted.2+q.2)

private def roundCounter (n k : ℕ) : ℕ × ℕ :=
  let word := BinaryNaturalView.encode k
  let T := BinaryRawRational.mul (Code.ofNat (2*n)) (Code.ofNat word.1.length)
  let next := BinaryRawRational.add T.1 Code.one
  (next.1.num,word.2+T.2+next.2+16*(word.1.length+1)^2+16*(n+1)^2)

def compute (n : ℕ) (mass : Code) : Controls :=
  let gate := BinaryRawRational.le Code.one mass
  let q := magnitude n mass
  let ceil := BinaryRawRational.ceil q.1
  let count := roundCounter n ceil.1
  ⟨!gate.1,count.1,gate.2+q.2+ceil.2+count.2+24⟩

theorem compute_small (n : ℕ) (mass : Code) : (compute n mass).small=true ↔ mass.value < 1 := by
  simp only [compute,Bool.not_eq_true',← Bool.not_eq_true,BinaryRawRational.le_value,Code.le_eq_true,Code.value_one,
    not_le]

private theorem magnitude_value (n : ℕ) (mass : Code) :
    (magnitude n mass).1.value=RationalWeakFamily.edgeMagnitude n mass.value := by
  simp only [magnitude,BinaryRawRational.mul_value,BinaryRawRational.add_value,Code.value_mul,Code.value_add,
    Code.value_ofNat,Nat.cast_ofNat,RationalWeakFamily.edgeMagnitude]

private theorem roundCounter_value (n k : ℕ) : (roundCounter n k).1=2*n*k.size+1 := by
  simp only [roundCounter,BinaryRawRational.add_value,BinaryRawRational.mul_value,BinaryNaturalView.encode_bits,
    Nat.size_eq_bits_len,Code.add,Code.mul,Code.ofNat,Code.one,Nat.mul_one]

theorem compute_horizon (n : ℕ) (mass : Code) : (compute n mass).horizon=RationalWeakFamily.edgeRounds n mass.value := by
  simp only [compute,roundCounter_value,BinaryRawRational.ceil_value,Code.ceil_eq,magnitude_value,
    RationalWeakFamily.edgeRounds]

def budget {R : Type*} [Semiring R] (n B : R) : R :=
  let W := B+4*n+5
  7*BinaryRawRational.budget W+32*(W+1)^2+16*(n+1)^2+24

set_option maxHeartbeats 1200000 in
theorem compute_paid {n B : ℕ} (q : Code) (hq : q.Bounded B) :
    (compute n q).paid ≤ budget n B := by
  let W := B+4*n+5
  let gate := BinaryRawRational.le Code.one q
  let a := BinaryRawRational.mul (Code.ofNat 2) q
  let b := BinaryRawRational.add a.1 (Code.ofNat n)
  let c := BinaryRawRational.mul (Code.ofNat n) b.1
  let ceil := BinaryRawRational.ceil c.1
  let word := BinaryNaturalView.encode ceil.1
  let T := BinaryRawRational.mul (Code.ofNat (2*n)) (Code.ofNat word.1.length)
  let next := BinaryRawRational.add T.1 Code.one
  have natFit (m : ℕ) : (Code.ofNat m).Bounded m := ⟨m.lt_two_pow_self.le,Nat.one_le_two_pow⟩
  have twoFit : (Code.ofNat 2).Bounded 1 := ⟨by decide,by decide⟩
  have aFit : a.1.Bounded (1+B) := by
    change (BinaryRawRational.mul (Code.ofNat 2) q).1.Bounded _
    rw [BinaryRawRational.mul_value]
    exact Code.bounded_mul twoFit hq
  have bFit : b.1.Bounded (1+B+n+1) := by
    change (BinaryRawRational.add a.1 (Code.ofNat n)).1.Bounded _
    rw [BinaryRawRational.add_value]
    exact Code.bounded_add aFit (natFit n)
  have cFit : c.1.Bounded (n+(1+B+n+1)) := by
    change (BinaryRawRational.mul (Code.ofNat n) b.1).1.Bounded _
    rw [BinaryRawRational.mul_value]
    exact Code.bounded_mul (natFit n) bFit
  have bitLength : ceil.1.size ≤ n+(1+B+n+1)+2 := by
    change (BinaryRawRational.ceil c.1).1.size ≤ _
    rw [BinaryRawRational.ceil_value]
    exact (Nat.size_le_size (((Nat.div_le_self ..).trans (Nat.sub_le ..)).trans (Code.ceiling_intermediate cFit))).trans_eq
      Nat.size_pow
  have len : word.1.length ≤ n+(1+B+n+1)+2 := by
    rw [show word.1=ceil.1.bits from BinaryNaturalView.encode_bits ceil.1,Nat.size_eq_bits_len]
    exact bitLength
  have tFit : T.1.Bounded (2*n+word.1.length) := by
    change (BinaryRawRational.mul (Code.ofNat (2*n)) (Code.ofNat word.1.length)).1.Bounded _
    rw [BinaryRawRational.mul_value]
    exact Code.bounded_mul (natFit _) (natFit _)
  have oneW := Code.bounded_mono Code.bounded_one (Nat.zero_le W)
  have qW := Code.bounded_mono hq (show B ≤ W by unfold W; omega)
  have twoW := Code.bounded_mono twoFit (show 1 ≤ W by unfold W; omega)
  have nW := Code.bounded_mono (natFit n) (show n ≤ W by unfold W; omega)
  have g : gate.2 ≤ BinaryRawRational.budget W := BinaryRawRational.le_paid oneW qW
  have pa : a.2 ≤ BinaryRawRational.budget W := BinaryRawRational.mul_paid twoW qW
  have pb : b.2 ≤ BinaryRawRational.budget W := BinaryRawRational.add_paid
    (Code.bounded_mono aFit (show 1+B ≤ W by unfold W; omega)) nW
  have pc : c.2 ≤ BinaryRawRational.budget W := BinaryRawRational.mul_paid nW
    (Code.bounded_mono bFit (show 1+B+n+1 ≤ W by unfold W; omega))
  have pd : ceil.2 ≤ BinaryRawRational.budget W := BinaryRawRational.ceil_paid
    (Code.bounded_mono cFit (show n+(1+B+n+1) ≤ W by unfold W; omega))
  have pe : T.2 ≤ BinaryRawRational.budget W := BinaryRawRational.mul_paid
    (Code.bounded_mono (natFit (2*n)) (show 2*n ≤ W by unfold W; omega))
    (Code.bounded_mono (natFit word.1.length) (show word.1.length ≤ W by unfold W; omega))
  have pf : next.2 ≤ BinaryRawRational.budget W := BinaryRawRational.add_paid
    (Code.bounded_mono tFit (show 2*n+word.1.length ≤ W by unfold W; omega)) oneW
  have encoded : word.2 ≤ 16*(W+1)^2 :=
    (BinaryNaturalView.encode_paid ceil.1).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by unfold W; omega) 2))
  have copied : 16*(word.1.length+1)^2 ≤ 16*(W+1)^2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by unfold W; omega) 2)
  change gate.2+(a.2+b.2+c.2)+ceil.2+(word.2+T.2+next.2+16*(word.1.length+1)^2+16*(n+1)^2)+24 ≤
    7*BinaryRawRational.budget W+32*(W+1)^2+16*(n+1)^2+24
  omega

end DirectedFlowCutGap.BinaryEdgeFamilyControls
