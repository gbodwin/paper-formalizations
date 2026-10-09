import DirectedFlowCutGap.BinaryArithmetic

/-!
# Binary input widths and bounded shifts

The width routine returns an actual binary counter built by Boolean carry
propagation. It does not compute the input's natural denotation. The shift
routine has a bound polynomial in its numerical exponent; callers must bound
that exponent (as the raw solver's lambda grid does), rather than claim a bound
polynomial in the exponent's shorter binary encoding.
-/
namespace DirectedFlowCutGap.BinaryCounters
open BinaryArithmetic

/-- Count list cells using the verified binary increment operation. -/
def lengthBits : Bits → Bits × ℕ
  | [] => ([],1)
  | _::xs =>
      let r := lengthBits xs
      let a := increment true r.1
      (a.1,r.2+a.2+8)

theorem lengthBits_spec (xs : Bits) :
    value (lengthBits xs).1=xs.length ∧
    (lengthBits xs).1.length≤xs.length+1 ∧
    (lengthBits xs).2≤16*(xs.length+1)^2 := by
  induction xs with
  | nil => simp [lengthBits,value]
  | cons x xs ih =>
      have ha := increment_spec true (lengthBits xs).1
      simp only [lengthBits,List.length_cons]
      refine ⟨?_,?_,?_⟩
      · simpa only [Bool.toNat_true,ih.1] using ha.1
      · omega
      · nlinarith [ha.2.2,ih.2.2]

/-- Actual Nat.size realization: trim redundant high zeroes, then binary-count. -/
def sizeBits (xs : Bits) : Bits × ℕ :=
  let t := trim xs
  let r := lengthBits t.1
  (r.1,t.2+r.2+8)

theorem sizeBits_spec (xs : Bits) :
    value (sizeBits xs).1=Nat.size (value xs) ∧
    (sizeBits xs).2≤32*(xs.length+1)^2 := by
  have ht := trim_spec xs
  have hl := lengthBits_spec (trim xs).1
  simp only [sizeBits]
  constructor
  · rw [hl.1,trim_length]
  · nlinarith [ht.2.2.1,ht.2.2.2,hl.2.2]

/-- Emit the power-of-two bitstring. The counter allowance is deliberately
quadratic in the numerical output exponent, so binary control is not free. -/
def powerOfTwo : ℕ → Bits × ℕ
  | 0 => ([true],1)
  | k+1 => let r := powerOfTwo k; (false::r.1,r.2+32*(k+2))

theorem powerOfTwo_spec (k : ℕ) :
    value (powerOfTwo k).1=2^k ∧
    (powerOfTwo k).1.length=k+1 ∧
    (powerOfTwo k).2≤32*(k+1)^2 := by
  induction k with
  | zero => simp [powerOfTwo,value]
  | succ k ih =>
      simp only [powerOfTwo,value,Bool.toNat_false,zero_add,List.length_cons]
      refine ⟨?_,?_,?_⟩
      · rw [ih.1,pow_succ];omega
      · omega
      · nlinarith [ih.2.2]

/-- A binary-controlled version of the shift loop. The natural denotation is
used only as an erased termination measure, never as executable loop fuel. -/
def powerOfTwoBinary (xs : Bits) : Bits × ℕ :=
  let z := isZero xs
  if hz : z.1=true then ([true],z.2+4) else
    let p := predecessor xs
    let r := powerOfTwoBinary p.1
    (false::r.1,z.2+p.2+r.2+8)
termination_by value xs
decreasing_by
  have hzero := (isZero_spec xs).1
  have hp := (predecessor_spec xs).1
  have hv : 0<value xs := Nat.pos_of_ne_zero (fun h => hz (hzero.mpr h))
  simp only [hp]
  omega

/-- Cost is polynomial in the numerical exponent and its supplied bit length.
This is suitable for the bounded lambda-grid exponents; it is not polynomial
in the binary exponent length alone, since the output itself has that many bits. -/
theorem powerOfTwoBinary_spec (xs : Bits) :
    value (powerOfTwoBinary xs).1=2^(value xs) ∧
    (powerOfTwoBinary xs).1.length=value xs+1 ∧
    (powerOfTwoBinary xs).2≤64*(value xs+1)*(xs.length+1) := by
  have aux : ∀ n, ∀ ys : Bits, value ys=n →
      value (powerOfTwoBinary ys).1=2^(value ys) ∧
      (powerOfTwoBinary ys).1.length=value ys+1 ∧
      (powerOfTwoBinary ys).2≤64*(value ys+1)*(ys.length+1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro ys hy
      have hz := isZero_spec ys
      have hp := predecessor_spec ys
      rw [powerOfTwoBinary]
      split_ifs with hzero
      · have hv : value ys=0 := hz.1.mp hzero
        simp only [value,Bool.toNat_true,List.length_cons,List.length_nil,hv,
          pow_zero,mul_zero,add_zero]
        refine ⟨by simp,by simp,?_⟩
        nlinarith [hz.2]
      · have hv : 0<value ys := Nat.pos_of_ne_zero (fun h => hzero (hz.1.mpr h))
        have hh := ih (value (predecessor ys).1) (by rw [hp.1,← hy];omega)
          (predecessor ys).1 rfl
        have hw : (predecessor ys).1.length≤ys.length := by
          rw [hp.2.1]
          exact (Nat.size_le_size (Nat.sub_le _ _)).trans (Nat.size_le.mpr (value_lt ys))
        have hc : (powerOfTwoBinary (predecessor ys).1).2≤
            64*(value ys)*(ys.length+1) := by
          calc
            _ ≤ 64*(value (predecessor ys).1+1)*((predecessor ys).1.length+1) := hh.2.2
            _ ≤ 64*(value ys)*(ys.length+1) := by rw [hp.1];gcongr;omega
        simp only [value,Bool.toNat_false,zero_add,List.length_cons]
        refine ⟨?_,?_,?_⟩
        · rw [hh.1,hp.1]
          have he : value ys=value ys-1+1 := by omega
          conv_rhs => rw [he,pow_succ]
          omega
        · rw [hh.2.1,hp.1];omega
        · nlinarith [hz.2,hp.2.2]
  exact aux (value xs) xs rfl

end DirectedFlowCutGap.BinaryCounters
