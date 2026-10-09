import DirectedFlowCutGap.BinaryDivision

/-!
# Signed scalar operations on retained binary magnitudes

All executable data are a Boolean sign and a Boolean-list magnitude. The
normalizer gives zero a positive sign and trims padding. Addition selects
actual binary addition or subtraction by sign and a binary comparison. Integer
denotation is used only in statements and proofs. These are scalar/list
instruction charges; heap allocation and address traffic are composed later.
-/
namespace DirectedFlowCutGap.BinarySigned
open BinaryArithmetic

structure Signed where
  negative : Bool
  magnitude : Bits
  deriving DecidableEq

def decode (a : Signed) : ℤ :=
  if a.negative then -(value a.magnitude : ℤ) else (value a.magnitude : ℤ)

def Canonical (a : Signed) : Prop :=
  a.magnitude.length = Nat.size (value a.magnitude) ∧
  (value a.magnitude = 0 → a.negative = false)

theorem canonical_length (a : Signed) (ha : Canonical a) :
    a.magnitude.length = (decode a).natAbs.size := by
  rw [ha.1]
  cases h : a.negative <;> simp [decode,h]

/-- The sign decision scans the trimmed stored bits. -/
def normalize (negative : Bool) (xs : Bits) : Signed × ℕ :=
  let t := trim xs
  let z := isZero t.1
  (⟨negative && !z.1,t.1⟩,t.2+z.2+8)

theorem normalize_decode (negative : Bool) (xs : Bits) :
    decode (normalize negative xs).1 =
      if negative then -(value xs : ℤ) else (value xs : ℤ) := by
  have ht := (trim_spec xs).2.1
  have hz := (isZero_spec (trim xs).1).1
  cases negative <;> cases he : (isZero (trim xs).1).1 <;>
    simp_all [normalize,decode]

theorem normalize_canonical (negative : Bool) (xs : Bits) :
    Canonical (normalize negative xs).1 := by
  have ht := trim_spec xs
  have hz := (isZero_spec (trim xs).1).1
  constructor
  · change (trim xs).1.length=Nat.size (value (trim xs).1)
    rw [trim_length,ht.2.1]
  · intro h
    have he : (isZero (trim xs).1).1=true := hz.mpr h
    simp [normalize,he]

theorem normalize_bounds (negative : Bool) (xs : Bits) :
    (normalize negative xs).1.magnitude.length ≤ xs.length ∧
    (normalize negative xs).2 ≤ 32*(xs.length+1) := by
  have ht := trim_spec xs
  have hz := (isZero_spec (trim xs).1).2
  simp only [normalize]
  exact ⟨ht.2.2.1,by omega⟩

def ofNat (xs : Bits) : Signed × ℕ := normalize false xs

theorem ofNat_decode (xs : Bits) : decode (ofNat xs).1=(value xs : ℤ) := by
  simpa only [ofNat,Bool.false_eq_true,ite_false] using normalize_decode false xs

theorem ofNat_canonical (xs : Bits) : Canonical (ofNat xs).1 :=
  normalize_canonical false xs

def negate (a : Signed) : Signed × ℕ := normalize (!a.negative) a.magnitude

theorem negate_decode (a : Signed) : decode (negate a).1 = -decode a := by
  rw [negate,normalize_decode]
  cases h : a.negative <;> simp [decode,h]

theorem negate_canonical (a : Signed) : Canonical (negate a).1 :=
  normalize_canonical (!a.negative) a.magnitude

/-- Every result is normalized, including opposite equal magnitudes. -/
def add (a b : Signed) : Signed × ℕ :=
  if a.negative == b.negative then
    let s := addCanonical a.magnitude b.magnitude
    let r := normalize a.negative s.1
    (r.1,s.2+r.2+8)
  else
    let c := BinaryArithmetic.compare a.magnitude b.magnitude
    if c.less then
      let s := BinaryDivision.sub b.magnitude a.magnitude
      let r := normalize b.negative s.1
      (r.1,c.steps+s.2+r.2+12)
    else
      let s := BinaryDivision.sub a.magnitude b.magnitude
      let r := normalize a.negative s.1
      (r.1,c.steps+s.2+r.2+12)

theorem add_decode (a b : Signed) : decode (add a b).1=decode a+decode b := by
  have hc := (compare_spec a.magnitude b.magnitude).1
  have hab := (BinaryDivision.sub_spec a.magnitude b.magnitude).1
  have hba := (BinaryDivision.sub_spec b.magnitude a.magnitude).1
  have hs := (canonical_values a.magnitude b.magnitude).1
  unfold add
  split
  next hsame =>
    rw [normalize_decode,hs]
    cases ha : a.negative <;> cases hb : b.negative
    all_goals simp_all [decode]
    all_goals omega
  next hdifferent =>
    dsimp only
    split
    next hless =>
      have hle : value a.magnitude≤value b.magnitude := (hc.mp hless).le
      rw [normalize_decode,hba,Int.natCast_sub hle]
      cases ha : a.negative <;> cases hb : b.negative <;> simp_all [decode] <;> omega
    next hnotless =>
      have hle : value b.magnitude≤value a.magnitude :=
        Nat.le_of_not_gt (fun h => hnotless (hc.mpr h))
      rw [normalize_decode,hab,Int.natCast_sub hle]
      cases ha : a.negative <;> cases hb : b.negative <;> simp_all [decode] <;> omega

theorem add_canonical (a b : Signed) : Canonical (add a b).1 := by
  unfold add
  split
  · exact normalize_canonical _ _
  · dsimp only
    split <;> exact normalize_canonical _ _

def sub (a b : Signed) : Signed × ℕ :=
  let b' := negate b
  let r := add a b'.1
  (r.1,b'.2+r.2+4)

theorem sub_decode (a b : Signed) : decode (sub a b).1=decode a-decode b := by
  simp only [sub,add_decode,negate_decode,sub_eq_add_neg]

theorem sub_canonical (a b : Signed) : Canonical (sub a b).1 :=
  add_canonical a (negate b).1

def magnitude (a : Signed) : Bits × ℕ := trim a.magnitude

theorem magnitude_decode (a : Signed) : value (magnitude a).1=(decode a).natAbs := by
  rw [magnitude,(trim_spec a.magnitude).2.1]
  cases h : a.negative <;> simp [decode,h]

def toNat (a : Signed) : Bits × ℕ :=
  if a.negative then ([],4) else
    let t := trim a.magnitude
    (t.1,t.2+4)

theorem toNat_decode (a : Signed) : value (toNat a).1=(decode a).toNat := by
  cases h : a.negative <;> simp [toNat,h,decode,(trim_spec a.magnitude).2.1,value]

/-- Strict signed comparison uses the normalized difference's actual sign. -/
def less (a b : Signed) : Bool × ℕ :=
  let d := sub a b
  (d.1.negative,d.2+4)

private theorem negative_iff (a : Signed) (ha : Canonical a) :
    a.negative=true ↔ decode a<0 := by
  cases h : a.negative
  · simp [decode,h]
  · have hn : value a.magnitude≠0 := by
      intro hz
      have := ha.2 hz
      simp [h] at this
    simp [decode,h]
    omega

theorem less_decode (a b : Signed) : (less a b).1=true ↔ decode a<decode b := by
  have h := negative_iff (sub a b).1 (sub_canonical a b)
  rw [sub_decode] at h
  simpa only [less,sub_neg] using h

private theorem add_magnitude_length {xs ys : Bits} {B : ℕ}
    (hx : xs.length ≤ B) (hy : ys.length ≤ B) :
    (addCanonical xs ys).1.length ≤ B+1 := by
  have h := (add_spec false xs ys).2.1
  have ht := (trim_spec (BinaryArithmetic.add false xs ys).1).2.2.1
  change (trim (BinaryArithmetic.add false xs ys).1).1.length ≤ B+1
  have hm := max_le hx hy
  omega

private theorem sub_magnitude_length {xs ys : Bits} {B : ℕ}
    (hx : xs.length ≤ B) : (BinaryDivision.sub xs ys).1.length ≤ B := by
  rw [(BinaryDivision.sub_spec xs ys).2.1]
  exact (Nat.size_le_size (Nat.sub_le _ _)).trans
    ((Nat.size_le.mpr (value_lt xs)).trans hx)

/-- Actual stored magnitude widths, rather than just decoded-value widths. -/
theorem add_bounds {a b : Signed} {B : ℕ}
    (ha : a.magnitude.length ≤ B) (hb : b.magnitude.length ≤ B) :
    (add a b).1.magnitude.length ≤ B+1 ∧ (add a b).2 ≤ 256*(B+2) := by
  have hslen := add_magnitude_length ha hb
  have hscost := (canonical_charges ha hb).1
  have hs := normalize_bounds a.negative (addCanonical a.magnitude b.magnitude).1
  have hc := (compare_spec a.magnitude b.magnitude).2.2
  have hm := max_le ha hb
  have hablen := sub_magnitude_length (ys := b.magnitude) ha
  have hbalen := sub_magnitude_length (ys := a.magnitude) hb
  have habcost := (BinaryDivision.sub_spec a.magnitude b.magnitude).2.2
  have hbacost := (BinaryDivision.sub_spec b.magnitude a.magnitude).2.2
  have hab := normalize_bounds a.negative (BinaryDivision.sub a.magnitude b.magnitude).1
  have hba := normalize_bounds b.negative (BinaryDivision.sub b.magnitude a.magnitude).1
  unfold add
  split
  · dsimp only
    constructor <;> omega
  · dsimp only
    split <;> dsimp only <;> constructor <;> omega

theorem negate_bounds {a : Signed} {B : ℕ} (ha : a.magnitude.length ≤ B) :
    (negate a).1.magnitude.length ≤ B ∧ (negate a).2 ≤ 32*(B+1) := by
  have h := normalize_bounds (!a.negative) a.magnitude
  unfold negate
  constructor <;> omega

theorem sub_bounds {a b : Signed} {B : ℕ}
    (ha : a.magnitude.length ≤ B) (hb : b.magnitude.length ≤ B) :
    (sub a b).1.magnitude.length ≤ B+1 ∧ (sub a b).2 ≤ 512*(B+2) := by
  have hn := negate_bounds hb
  have hs := add_bounds ha hn.1
  dsimp only [sub]
  constructor <;> omega

theorem less_charge {a b : Signed} {B : ℕ}
    (ha : a.magnitude.length ≤ B) (hb : b.magnitude.length ≤ B) :
    (less a b).2 ≤ 1024*(B+2) := by
  have h := (sub_bounds ha hb).2
  dsimp only [less]
  omega

theorem magnitude_bounds {a : Signed} {B : ℕ} (ha : a.magnitude.length ≤ B) :
    (magnitude a).1.length ≤ B ∧ (magnitude a).2 ≤ 32*(B+1) := by
  have h := trim_spec a.magnitude
  unfold magnitude
  constructor <;> omega

theorem toNat_bounds {a : Signed} {B : ℕ} (ha : a.magnitude.length ≤ B) :
    (toNat a).1.length ≤ B ∧ (toNat a).2 ≤ 32*(B+1) := by
  have h := trim_spec a.magnitude
  unfold toNat
  split
  · simp only [List.length_nil]
    constructor <;> omega
  · dsimp only
    constructor <;> omega

end DirectedFlowCutGap.BinarySigned
