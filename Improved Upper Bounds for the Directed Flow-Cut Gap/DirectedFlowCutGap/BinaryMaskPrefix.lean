import DirectedFlowCutGap.BinaryNaturalView

/-! Copy a cut-mask word to its declared dimension. The input may be shorter
or arbitrarily longer than the requested mask. The copy inspects only the
reached input bits and uses a binary counter for the dimension. -/
namespace DirectedFlowCutGap.BinaryMaskPrefix

open BinaryArithmetic

def padded : ℕ → Bits → Bits
  | 0,_ => []
  | n+1,word => word.headD false::padded n word.tail

def copy (fuel word : Bits) : Bits × ℕ :=
  let zero := isZero fuel
  if empty : zero.1=true then ([],zero.2+4)
  else
    let previous := predCore fuel
    let tail := copy previous.1 word.tail
    (word.headD false::tail.1,zero.2+previous.2+tail.2+12)
termination_by value fuel
decreasing_by
  have positive := Nat.pos_of_ne_zero (fun h => empty ((isZero_spec fuel).1.mpr h))
  have smaller := (predCore_spec fuel).1 positive
  change value (predCore fuel).1 < value fuel
  omega

theorem copy_spec (fuel word : Bits) :
    (copy fuel word).1=padded (value fuel) word ∧
      (copy fuel word).2≤24*(value fuel+1)*(fuel.length+1) := by
  induction hv : value fuel using Nat.strong_induction_on generalizing fuel word with
  | h n ih =>
      rw [← hv,copy]
      have zero := isZero_spec fuel
      by_cases empty : (isZero fuel).1=true
      · have none := zero.1.mp empty
        simp only [dite_eq_left empty,none,padded,Nat.zero_add,true_and]
        omega
      · have pos := Nat.pos_of_ne_zero (fun h => empty (zero.1.mpr h))
        obtain ⟨pred,short,cost⟩ := predCore_spec fuel
        have next : value fuel=value (predCore fuel).1+1 := (pred pos).symm
        have rest := ih (value (predCore fuel).1) (by omega) (predCore fuel).1 word.tail rfl
        rw [dite_eq_right empty,next,padded]
        simp only [rest.1,true_and]
        have narrow := rest.2.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right short 1))
        have split : 24*(value (predCore fuel).1+1+1)*(fuel.length+1)=
            24*(value (predCore fuel).1+1)*(fuel.length+1)+24*(fuel.length+1) := by ring
        rw [split]
        omega

theorem padded_length (n : ℕ) (word : Bits) : (padded n word).length=n := by
  induction n generalizing word with
  | zero => rfl
  | succ n ih => simp only [padded,List.length_cons,ih]

theorem padded_lookup (n : ℕ) (word : Bits) (i : ℕ) (valid : i<n) :
    (padded n word)[i]?.getD false=word[i]?.getD false := by
  induction n generalizing word i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => cases word <;> rfl
      | succ i =>
          have fits : i<n := by omega
          change (padded n word.tail)[i]?.getD false=word[i+1]?.getD false
          rw [ih word.tail i fits]
          cases word <;> rfl

def mask (n : ℕ) (word : Bits) : Bits × ℕ :=
  let count := BinaryNaturalView.encode n
  let out := copy count.1 word
  (out.1,count.2+out.2)

theorem mask_spec (n : ℕ) (word : Bits) :
    (mask n word).1=padded n word ∧ (mask n word).2≤40*(n+1)^2 := by
  let count := BinaryNaturalView.encode n
  have charge : (BinaryNaturalView.encode n).2≤16*(n.size+1)^2 := BinaryNaturalView.encode_paid n
  obtain ⟨shape,paid⟩ := copy_spec count.1 word
  rw [show value count.1=n from BinaryNaturalView.encode_value _] at shape paid
  have width : count.1.length=n.size := by rw [show count.1=n.bits from BinaryNaturalView.encode_bits _,Nat.size_eq_bits_len]
  have cap : n.size≤n := Nat.size_le.mpr Nat.lt_two_pow_self
  have input := charge.trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right cap 1) 2))
  have output : (copy count.1 word).2≤24*(n+1)^2 := by
    rw [width] at paid
    simpa only [pow_two,Nat.mul_assoc] using (paid.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right cap 1)))
  refine ⟨shape,?_⟩
  change (BinaryNaturalView.encode n).2+(copy count.1 word).2≤_
  omega

theorem mask_zero_paid (word : Bits) : (mask 0 word).2=6 := by
  change (BinaryNaturalView.encode 0).2+(copy [] word).2=6
  rw [copy]
  rfl

theorem mask_one_paid (word : Bits) : (mask 1 word).2=46 := by
  change (BinaryNaturalView.encode 1).2+(copy [true] word).2=46
  rw [copy]
  simp only [isZero,predCore,Bool.false_eq_true]
  rw [copy]
  rfl

end DirectedFlowCutGap.BinaryMaskPrefix
