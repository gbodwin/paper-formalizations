import DirectedFlowCutGap.EncodedEdgeLabels
import DirectedFlowCutGap.BinaryRational

/-! Compute and charge the dyadic comparisons on binary numerator and
denominator words. The scan constructs each power directly as a bit list. -/

namespace DirectedFlowCutGap.ChargedEdgeDyadicLabels

open BinaryArithmetic BinaryRational RawNonnegativeRational
open EncodedEdgeLabels (dyadicCode cutoffCode ceilIndex)

private def powerWord (k : ℕ) : Bits := List.replicate k false ++ [true]

private theorem power_value (k : ℕ) : value (powerWord k)=2^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change false.toNat+2*value (powerWord k)=2^(k+1)
    rw [ih,Nat.pow_succ,Nat.mul_comm 2]
    simp [Bool.toNat]

private theorem code_equal {a b : Code} (num : a.num=b.num) (den : a.den=b.den) : a=b := by
  cases a
  cases b
  simp_all

def powerFraction (k : ℕ) : Fraction := ⟨[true],powerWord k,by rw [power_value]; positivity⟩

theorem decode_power (k : ℕ) : decode (powerFraction k)=dyadicCode k := by
  apply code_equal
  · change value [true]=(Code.one.div (Code.ofNat (2^k))).num
    simp [Code.div,Code.one,Code.ofNat,value]
  · change value (powerWord k)=(Code.one.div (Code.ofNat (2^k))).den
    rw [power_value]
    simp [Code.div,Code.one,Code.ofNat]

theorem power_width (k : ℕ) : StoredBounded (powerFraction k) (k+1) := by
  simp [StoredBounded,powerFraction,powerWord]

private def twiceCount (n : ℕ) (h : 0<n) : Fraction :=
  ⟨[true],false::n.bits,by simp [value,value_bits,h]⟩

private theorem decode_twice (n : ℕ) (h : 0<n) : decode (twiceCount n h)=cutoffCode n := by
  apply code_equal
  · have nonzero : 2*n ≠ 0 := by omega
    simp [decode,twiceCount,cutoffCode,Code.div,Code.one,Code.ofNat,nonzero,value]
  · have nonzero : 2*n ≠ 0 := by omega
    simp [decode,twiceCount,cutoffCode,Code.div,Code.one,Code.ofNat,nonzero,value,value_bits]

private theorem twice_width (n : ℕ) (h : 0<n) : StoredBounded (twiceCount n h) (n+1) := by
  have size : n.bits.length ≤ n := by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr n.lt_two_pow_self
  unfold StoredBounded twiceCount
  simp only [List.length_cons,List.length_nil,Nat.zero_add]
  omega

private theorem one_width {B : ℕ} (h : 1 ≤ B) : StoredBounded BinaryRational.one B := by
  simp [StoredBounded,BinaryRational.one,h]

private def search (w : Fraction) : ℕ → ℕ × ℕ
  | 0 => (0,1)
  | k+1 =>
    let cmp := BinaryRational.le w (powerFraction (k+1))
    let charge := cmp.2+8*(k+2)+10
    if cmp.1 then (k+1,charge) else
      let prev := search w k
      (prev.1,prev.2+charge)

private theorem search_value (w : Fraction) (k : ℕ) : (search w k).1=ceilIndex (decode w) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have together : (BinaryRational.le w (powerFraction (k+1))).1 = (decode w).le (dyadicCode (k+1)) := by
      rw [le_decode,decode_power]
    by_cases choose : (decode w).le (dyadicCode (k+1))=true
    · simp only [search,ceilIndex,together,ite_eq_left choose]
    · simp only [search,ceilIndex,together,ite_eq_right choose,ih]

private theorem search_index_le (w : Fraction) (k : ℕ) : (search w k).1 ≤ k := by
  rw [search_value,EncodedEdgeLabels.ceilIndex_value]
  exact DyadicEdgeWeights.ceilIndex_le _ _

def checkBudget {R : Type*} [Semiring R] (k B : R) : R := 2048*(B+k+3)^2+8*(k+2)+10

private theorem checks_mono {a b : ℕ} (B : ℕ) (h : a≤b) : checkBudget a B ≤ checkBudget b B := by
  unfold checkBudget
  gcongr

private theorem search_paid {B : ℕ} (w : Fraction) (fits : StoredBounded w B) (k : ℕ) :
    (search w k).2 ≤ k*checkBudget k B+1 := by
  induction k with
  | zero => simp [search]
  | succ k ih =>
    let cmp := BinaryRational.le w (powerFraction (k+1))
    have hw : StoredBounded w (B+k+2) := ⟨fits.1.trans (by omega),fits.2.trans (by omega)⟩
    have hp : StoredBounded (powerFraction (k+1)) (B+k+2) := by
      have base := power_width (k+1)
      exact ⟨base.1.trans (by omega),base.2.trans (by omega)⟩
    have paid : cmp.2+8*(k+2)+10 ≤ checkBudget (k+1) B := by
      have h := le_charge hw hp
      change cmp.2 ≤ _ at h
      have h' : cmp.2 ≤ 2048*(B+(k+1)+3)^2 := h.trans (Nat.mul_le_mul_left 2048
        (Nat.pow_le_pow_left (by omega) 2))
      unfold checkBudget
      omega
    have mono := checks_mono B (Nat.le_succ k)
    have tail : (search w k).2 ≤ k*checkBudget (k+1) B+1 :=
      ih.trans (Nat.add_le_add_right (Nat.mul_le_mul_left k mono) 1)
    change (if cmp.1 then (k+1,cmp.2+8*(k+2)+10) else
      ((search w k).1,(search w k).2+(cmp.2+8*(k+2)+10))).2 ≤ (k+1)*checkBudget (k+1) B+1
    rw [Nat.add_mul,Nat.one_mul]
    split <;> dsimp only <;> omega

def label (n : ℕ) (w : Fraction) : DyadicEdgeWeights.Label n × ℕ :=
  if h : 0<n then
    let cut := BinaryRational.le w (twiceCount n h)
    let used := cut.2+16*(n+1)^2+8
    if cut.1 then (none,used) else
      let full := BinaryRational.le one w
      if full.1 then (DyadicEdgeWeights.oneLabel n,used+full.2+5) else
        let ans := search w (DyadicEdgeWeights.depth n)
        (some ⟨ans.1,Nat.lt_succ_of_le (search_index_le w _)⟩,used+full.2+ans.2+8)
  else (none,4)

theorem label_value (n : ℕ) (w : Fraction) : (label n w).1=EncodedEdgeLabels.label n (decode w) := by
  by_cases h : 0<n
  · simp only [label,EncodedEdgeLabels.label,dite_eq_left h,ite_eq_right h.ne',le_decode,decode_twice,
      show decode one=Code.one from rfl]
    split <;> try rfl
    split
    · rfl
    · simp only [search_value]
  · have z : n=0 := by omega
    subst n
    rfl

def labelBudget {R : Type*} [Semiring R] (n B : R) : R :=
  2*(2048*(B+n+2)^2)+16*(n+1)^2+17+(n+1)*checkBudget (n+1) B

theorem label_paid {B : ℕ} (n : ℕ) (w : Fraction) (fits : StoredBounded w B) : (label n w).2 ≤ labelBudget n B := by
  by_cases h : 0<n
  · let cut := BinaryRational.le w (twiceCount n h)
    let full := BinaryRational.le one w
    let k := DyadicEdgeWeights.depth n
    have hw : StoredBounded w (B+n+1) := ⟨fits.1.trans (by omega),fits.2.trans (by omega)⟩
    have ct : StoredBounded (twiceCount n h) (B+n+1) := by
      have ht := twice_width n h
      exact ⟨ht.1.trans (by omega),ht.2.trans (by omega)⟩
    have cp : cut.2 ≤ 2048*(B+n+2)^2 := le_charge hw ct
    have fp : full.2 ≤ 2048*(B+n+2)^2 := le_charge (one_width (by omega)) hw
    have depth : k ≤ n+1 := Nat.add_le_add_right (Nat.log_le_self 2 n) 1
    have mono := checks_mono B depth
    have ss := (search_paid w fits k).trans (Nat.add_le_add_right (Nat.mul_le_mul depth mono) 1)
    simp only [label,dite_eq_left h]
    let head := cut.2+16*(n+1)^2+8
    let ans := search w k
    change (if cut.1 then (none,head) else if full.1 then (DyadicEdgeWeights.oneLabel n,head+full.2+5) else
      (some ⟨ans.1,Nat.lt_succ_of_le (search_index_le w _)⟩,head+full.2+ans.2+8)).2 ≤ _
    unfold labelBudget
    dsimp only [head] at *
    split <;> (try dsimp only)
    · omega
    · split <;> (try dsimp only [ans]) <;> omega
  · simp only [label,dite_eq_right h]
    unfold labelBudget
    omega

end DirectedFlowCutGap.ChargedEdgeDyadicLabels
