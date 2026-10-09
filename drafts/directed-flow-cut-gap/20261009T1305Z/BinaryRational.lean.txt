import DirectedFlowCutGap.BinaryArithmetic
import DirectedFlowCutGap.RawNonnegativeRational

/-!
# Binary realization of unreduced rational primitives

Both stored fields are actual little-endian Boolean lists. Addition,
multiplication, division and comparison compute their bit fields using the
binary algorithms, without natural denotation, native natural arithmetic, or
GCD normalization. The denominator-positivity certificate and decoding function
are semantic only. Padded input fields are allowed; newly computed arithmetic
fields have canonical length.

The returned charges instrument the persistent-list Boolean-operation model
of `BinaryArithmetic`. They exclude ghost counter arithmetic. List/record
charges count instructions; a bit or logarithmic-cost RAM interpretation must
also pay heap-address widths and account for input/storage cells. These bounds
still need composition with a program trace and its operand/storage bounds;
they are not a whole-solver or native-machine runtime theorem.
-/
namespace DirectedFlowCutGap.BinaryRational
open BinaryArithmetic
abbrev RawCode := RawNonnegativeRational.Code

structure Fraction where
  num : Bits
  den : Bits
  den_pos : 0 < value den

/-- Proof-side exact natural-field interpretation. -/
def decode (a : Fraction) : RawCode := ⟨value a.num,value a.den,a.den_pos⟩

def zero : Fraction := ⟨[],[true],by decide⟩
def one : Fraction := ⟨[true],[true],by decide⟩

@[simp] theorem decode_zero : decode zero = RawNonnegativeRational.Code.zero := rfl
@[simp] theorem decode_one : decode one = RawNonnegativeRational.Code.one := rfl

private theorem raw_ext {a b : RawCode} (hn : a.num=b.num) (hd : a.den=b.den) : a=b := by
  cases a
  cases b
  simp_all

/-- Validate the denominator by scanning supplied bits; no positivity proof
is required from the caller of this data entry point. -/
def fromBits (num den : Bits) : Option Fraction × ℕ :=
  let z := BinaryArithmetic.isZero den
  if hz : z.1=true then (none,z.2+4) else
    (some ⟨num,den,Nat.pos_of_ne_zero (fun h => hz ((isZero_spec den).1.mpr h))⟩,z.2+8)

theorem fromBits_none (num den : Bits) : (fromBits num den).1=none ↔ value den=0 := by
  unfold fromBits
  dsimp only
  split
  · rename_i hz
    exact ⟨fun _ => (isZero_spec den).1.mp hz,fun _ => rfl⟩
  · rename_i hz
    constructor
    · intro h; cases h
    · intro h; exact False.elim (hz ((isZero_spec den).1.mpr h))

theorem fromBits_fields (num den : Bits) {q : Fraction}
    (h : (fromBits num den).1=some q) : q.num=num ∧ q.den=den := by
  unfold fromBits at h
  dsimp only at h
  split at h
  · cases h
  · cases h
    exact ⟨rfl,rfl⟩

theorem fromBits_charge (num den : Bits) : (fromBits num den).2≤12*(den.length+1) := by
  have h := (isZero_spec den).2
  unfold fromBits
  dsimp only
  split <;> dsimp only <;> omega

/-- Canonicalize input padding without reducing the rational fraction. -/
def canonicalize (a : Fraction) : Fraction × ℕ :=
  let n := trim a.num
  let d := trim a.den
  (⟨n.1,d.1,by
    change 0 < value (trim a.den).1
    rw [(trim_spec a.den).2.1]
    exact a.den_pos⟩,n.2+d.2+8)

@[simp] theorem canonicalize_decode (a : Fraction) : decode (canonicalize a).1=decode a := by
  apply raw_ext
  · exact (trim_spec a.num).2.1
  · exact (trim_spec a.den).2.1

theorem canonicalize_lengths (a : Fraction) :
    (canonicalize a).1.num.length=Nat.size (decode a).num ∧
    (canonicalize a).1.den.length=Nat.size (decode a).den := by
  exact ⟨trim_length a.num,trim_length a.den⟩

/-- Three schoolbook products and one ripple-carry sum. -/
def add (a b : Fraction) : Fraction × ℕ :=
  let p := mulCanonical a.num b.den
  let q := mulCanonical b.num a.den
  let d := mulCanonical a.den b.den
  let n := addCanonical p.1 q.1
  (⟨n.1,d.1,by
    change 0 < value (mulCanonical a.den b.den).1
    rw [(canonical_values a.den b.den).2.1]
    exact Nat.mul_pos a.den_pos b.den_pos⟩,p.2+q.2+d.2+n.2+16)

/-- Exactly two schoolbook products. -/
def mul (a b : Fraction) : Fraction × ℕ :=
  let n := mulCanonical a.num b.num
  let d := mulCanonical a.den b.den
  (⟨n.1,d.1,by
    change 0 < value (mulCanonical a.den b.den).1
    rw [(canonical_values a.den b.den).2.1]
    exact Nat.mul_pos a.den_pos b.den_pos⟩,n.2+d.2+8)

/-- Division uses an actual binary zero test and reciprocal cross-products.
It requires no integer quotient, remainder, or GCD primitive. -/
def div (a b : Fraction) : Fraction × ℕ :=
  let z := BinaryArithmetic.isZero b.num
  if hz : z.1 then (zero,z.2+4) else
    let n := mulCanonical a.num b.den
    let d := mulCanonical a.den b.num
    (⟨n.1,d.1,by
      change 0 < value (mulCanonical a.den b.num).1
      rw [(canonical_values a.den b.num).2.1]
      apply Nat.mul_pos a.den_pos
      exact Nat.pos_of_ne_zero (fun h => hz ((isZero_spec b.num).1.mpr h))⟩,
      z.2+n.2+d.2+12)

def isZero (a : Fraction) : Bool × ℕ := BinaryArithmetic.isZero a.num

/-- Comparison computes both actual binary cross-products. -/
def le (a b : Fraction) : Bool × ℕ :=
  let p := mulCanonical a.num b.den
  let q := mulCanonical b.num a.den
  let r := lessEqual p.1 q.1
  (r.1,p.2+q.2+r.2+8)

@[simp] theorem add_decode (a b : Fraction) : decode (add a b).1=(decode a).add (decode b) := by
  apply raw_ext
  · change value (addCanonical (mulCanonical a.num b.den).1
      (mulCanonical b.num a.den).1).1 = value a.num*value b.den+value b.num*value a.den
    rw [(canonical_values _ _).1,(canonical_values a.num b.den).2.1,
      (canonical_values b.num a.den).2.1]
  · exact (canonical_values a.den b.den).2.1

@[simp] theorem mul_decode (a b : Fraction) : decode (mul a b).1=(decode a).mul (decode b) := by
  apply raw_ext
  · exact (canonical_values a.num b.num).2.1
  · exact (canonical_values a.den b.den).2.1

@[simp] theorem div_decode (a b : Fraction) : decode (div a b).1=(decode a).div (decode b) := by
  unfold div RawNonnegativeRational.Code.div
  by_cases hz : (BinaryArithmetic.isZero b.num).1=true
  · have hn : (decode b).num=0 := (isZero_spec b.num).1.mp hz
    simp [hz,hn]
  · have hn : (decode b).num≠0 := fun h => hz ((isZero_spec b.num).1.mpr h)
    simp only [hz,hn]
    apply raw_ext
    · exact (canonical_values a.num b.den).2.1
    · exact (canonical_values a.den b.num).2.1

@[simp] theorem isZero_decode (a : Fraction) :
    (isZero a).1=true ↔ (decode a).num=0 := (isZero_spec a.num).1

@[simp] theorem le_decode (a b : Fraction) : (le a b).1=(decode a).le (decode b) := by
  apply Bool.eq_iff_iff.mpr
  change (lessEqual (mulCanonical a.num b.den).1 (mulCanonical b.num a.den).1).1=true ↔ _
  rw [(lessEqual_spec _ _).1]
  simp only [RawNonnegativeRational.Code.le,decode,
    (canonical_values a.num b.den).2.1,(canonical_values b.num a.den).2.1]
  exact ⟨decide_eq_true,of_decide_eq_true⟩

/-- Every newly computed arithmetic field has its exact natural binary size. -/
theorem add_lengths (a b : Fraction) :
    (add a b).1.num.length=Nat.size ((decode a).add (decode b)).num ∧
    (add a b).1.den.length=Nat.size ((decode a).add (decode b)).den := by
  change (addCanonical (mulCanonical a.num b.den).1 (mulCanonical b.num a.den).1).1.length = _ ∧
    (mulCanonical a.den b.den).1.length = _
  rw [(canonical_values _ _).2.2.1,(canonical_values a.den b.den).2.2.2]
  simp [decode,RawNonnegativeRational.Code.add,
    (canonical_values a.num b.den).2.1,(canonical_values b.num a.den).2.1]

theorem mul_lengths (a b : Fraction) :
    (mul a b).1.num.length=Nat.size ((decode a).mul (decode b)).num ∧
    (mul a b).1.den.length=Nat.size ((decode a).mul (decode b)).den := by
  exact ⟨(canonical_values a.num b.num).2.2.2,(canonical_values a.den b.den).2.2.2⟩

theorem div_lengths (a b : Fraction) :
    (div a b).1.num.length=Nat.size ((decode a).div (decode b)).num ∧
    (div a b).1.den.length=Nat.size ((decode a).div (decode b)).den := by
  unfold div RawNonnegativeRational.Code.div
  by_cases hz : (BinaryArithmetic.isZero b.num).1=true
  · have hn : (decode b).num=0 := (isZero_spec b.num).1.mp hz
    simp [hz,hn,zero,RawNonnegativeRational.Code.zero]
  · have hn : (decode b).num≠0 := fun h => hz ((isZero_spec b.num).1.mpr h)
    simp only [hz,hn]
    exact ⟨(canonical_values a.num b.den).2.2.2,(canonical_values a.den b.num).2.2.2⟩

/-- Bounds refer to actual input list lengths, including padding. -/
def StoredBounded (a : Fraction) (B : ℕ) : Prop := a.num.length≤B ∧ a.den.length≤B

private theorem product_length {xs ys : Bits} {B : ℕ}
    (hx : xs.length≤B) (hy : ys.length≤B) : (mulCanonical xs ys).1.length≤3*B+1 := by
  have ht := (trim_spec (BinaryArithmetic.mul xs ys).1).2.2.1
  have hm := (mul_spec xs ys).2.1
  change (trim (BinaryArithmetic.mul xs ys).1).1.length ≤ _
  omega

theorem canonicalize_charge {a : Fraction} {B : ℕ} (ha : StoredBounded a B) :
    (canonicalize a).2≤24*(B+1) := by
  rcases ha with ⟨haNum,haDen⟩
  have hn := (trim_spec a.num).2.2.2
  have hd := (trim_spec a.den).2.2.2
  simp only [canonicalize]
  omega

theorem add_charge {a b : Fraction} {B : ℕ}
    (ha : StoredBounded a B) (hb : StoredBounded b B) :
    (add a b).2≤2048*(B+1)^2 := by
  have hp := (canonical_charges ha.1 hb.2).2
  have hq := (canonical_charges hb.1 ha.2).2
  have hd := (canonical_charges ha.2 hb.2).2
  have hn := (canonical_charges (product_length ha.1 hb.2) (product_length hb.1 ha.2)).1
  simp only [add]
  nlinarith

theorem mul_charge {a b : Fraction} {B : ℕ}
    (ha : StoredBounded a B) (hb : StoredBounded b B) :
    (mul a b).2≤2048*(B+1)^2 := by
  have hn := (canonical_charges ha.1 hb.1).2
  have hd := (canonical_charges ha.2 hb.2).2
  have hB := Nat.one_le_pow 2 (B+1) (Nat.succ_pos B)
  simp only [mul]
  omega

theorem div_charge {a b : Fraction} {B : ℕ}
    (ha : StoredBounded a B) (hb : StoredBounded b B) :
    (div a b).2≤2048*(B+1)^2 := by
  have hz := (isZero_spec b.num).2
  have hn := (canonical_charges ha.1 hb.2).2
  have hd := (canonical_charges ha.2 hb.1).2
  have hB := Nat.one_le_pow 2 (B+1) (Nat.succ_pos B)
  have hlin : B+1≤(B+1)^2 := Nat.le_self_pow (by decide) _
  have hnum := hb.1
  unfold div
  dsimp only
  split <;> dsimp only <;> omega

theorem isZero_charge {a : Fraction} {B : ℕ} (ha : StoredBounded a B) :
    (isZero a).2≤4*(B+1) :=
  (isZero_spec a.num).2.trans (Nat.mul_le_mul_left 4 (Nat.add_le_add_right ha.1 1))

theorem le_charge {a b : Fraction} {B : ℕ}
    (ha : StoredBounded a B) (hb : StoredBounded b B) :
    (le a b).2≤2048*(B+1)^2 := by
  have hp := (canonical_charges ha.1 hb.2).2
  have hq := (canonical_charges hb.1 ha.2).2
  have hl := (lessEqual_spec (mulCanonical a.num b.den).1 (mulCanonical b.num a.den).1).2
  have hh : max (mulCanonical a.num b.den).1.length (mulCanonical b.num a.den).1.length≤3*B+1 :=
    max_le (product_length ha.1 hb.2) (product_length hb.1 ha.2)
  simp only [le]
  nlinarith

/-- Join any raw stored-field bound to the arithmetic outputs' actual lengths. -/
theorem add_stored_bounded {a b : Fraction} {A B : ℕ}
    (ha : (decode a).Bounded A) (hb : (decode b).Bounded B) :
    StoredBounded (add a b).1 (A+B+2) := by
  have h := RawNonnegativeRational.Code.bounded_bits (RawNonnegativeRational.Code.bounded_add ha hb)
  rw [StoredBounded,(add_lengths a b).1,(add_lengths a b).2]
  simpa only [Nat.add_assoc] using h

theorem mul_stored_bounded {a b : Fraction} {A B : ℕ}
    (ha : (decode a).Bounded A) (hb : (decode b).Bounded B) :
    StoredBounded (mul a b).1 (A+B+1) := by
  have h := RawNonnegativeRational.Code.bounded_bits (RawNonnegativeRational.Code.bounded_mul ha hb)
  rw [StoredBounded,(mul_lengths a b).1,(mul_lengths a b).2]
  exact h

theorem div_stored_bounded {a b : Fraction} {A B : ℕ}
    (ha : (decode a).Bounded A) (hb : (decode b).Bounded B) :
    StoredBounded (div a b).1 (A+B+1) := by
  have h := RawNonnegativeRational.Code.bounded_bits (RawNonnegativeRational.Code.bounded_div ha hb)
  rw [StoredBounded,(div_lengths a b).1,(div_lengths a b).2]
  exact h

end DirectedFlowCutGap.BinaryRational
