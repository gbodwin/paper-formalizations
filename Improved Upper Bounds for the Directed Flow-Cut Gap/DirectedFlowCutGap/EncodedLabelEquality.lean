import DirectedFlowCutGap.BinaryArithmetic
import DirectedFlowCutGap.CandidateEnumeration

/-!
# Concrete binary equality for the retained candidate-network labels

The executed comparator inspects fixed constructor tags and compares the stored
vertex and level bit lists. It accepts padded encodings, including padded zero.
No arbitrary equality dictionary or direct-position table lookup is a primitive.
The fixed Boolean/list allowance is the same local model as BinaryArithmetic;
full-value sequence copying is a separate structural charge at the caller.

`meaning`, `labelMeaning`, and `canonicalEncoding` describe representations.
They are not called by `equal`. In particular, the use of Nat.bits below is an
input/specification map, not an unpriced runtime conversion. Callers must retain
represented labels and justify the actual stored lengths. Charge arithmetic is
mathematical instrumentation of the fixed comparator, not a claim of free
native execution of a returned Nat field.
-/
namespace DirectedFlowCutGap.EncodedLabelEquality
open BinaryArithmetic

inductive PortTag where
  | internal
  | source
  | sink
  deriving DecidableEq, Repr

/-- Fixed-depth tag comparison, implemented by constructor cases. -/
def tagEqual : PortTag → PortTag → Bool
  | .internal, .internal => true
  | .source, .source => true
  | .sink, .sink => true
  | _, _ => false

@[simp] theorem tagEqual_spec (a b : PortTag) : tagEqual a b = true ↔ a = b := by
  cases a <;> cases b <;> decide

/-- Four retained fields for an internal node; outer terminals have one bit. -/
inductive Key where
  | terminal (side : Bool)
  | core (tag : PortTag) (vertex : Bits) (side : Bool) (level : Bits)
  deriving Repr

inductive Meaning where
  | terminal (side : Bool)
  | core (tag : PortTag) (vertex : ℕ) (side : Bool) (level : ℕ)
  deriving DecidableEq, Repr

def meaning : Key → Meaning
  | .terminal b => .terminal b
  | .core t v b k => .core t (value v) b (value k)

def labelMeaning {n L : ℕ} : CandidateEnumeration.Network n L → Meaning
  | .inl ((.inl v,b),k) => .core .internal v.val b k.val
  | .inl ((.inr (.inl v),b),k) => .core .source v.val b k.val
  | .inl ((.inr (.inr v),b),k) => .core .sink v.val b k.val
  | .inr b => .terminal b

/-- These numeric observers appear only in the injectivity proof. -/
def tagOffset (n : ℕ) : PortTag → ℕ
  | .internal => 0
  | .source => n
  | .sink => 2*n

def Meaning.index (n L : ℕ) : Meaning → ℕ
  | .terminal b => 6*n*(L+1)+(if b then 1 else 0)
  | .core t v b k => (2*(tagOffset n t+v)+(if b then 1 else 0))*(L+1)+k

theorem labelMeaning_index {n L : ℕ} (x : CandidateEnumeration.Network n L) :
    (labelMeaning x).index n L = CandidateEnumeration.networkIndex x := by
  rcases x with ⟨⟨p,b⟩,k⟩ | b
  · rcases p with v | v | v <;>
      simp only [labelMeaning,Meaning.index,tagOffset,CandidateEnumeration.networkIndex,
        CandidateEnumeration.nodeIndex,CandidateEnumeration.pointIndex,
        CandidateEnumeration.portIndex,zero_add]
  · rfl

theorem labelMeaning_injective {n L : ℕ} :
    Function.Injective (@labelMeaning n L) := by
  intro x y h
  apply CandidateEnumeration.networkIndex_injective
  simpa only [labelMeaning_index] using congrArg (Meaning.index n L) h

def Represents {n L : ℕ} (a : Key) (x : CandidateEnumeration.Network n L) : Prop :=
  meaning a = labelMeaning x

/-- Every core/core comparison executes both scalar comparisons exactly once.
The result therefore also specifies tag and equality ties without relying on a
host-language structural equality implementation. -/
def equal : Key → Key → Bool × ℕ
  | .terminal a, .terminal b => (a == b,4)
  | .core ta va sa ka, .core tb vb sb kb =>
      let v := BinaryArithmetic.compare va vb
      let k := BinaryArithmetic.compare ka kb
      (tagEqual ta tb && v.equal && (sa == sb) && k.equal,v.steps+k.steps+12)
  | _, _ => (false,2)

theorem equal_spec (a b : Key) : (equal a b).1 = true ↔ meaning a = meaning b := by
  cases a with
  | terminal a => cases b <;> simp [equal,meaning]
  | core ta va sa ka =>
    cases b with
    | terminal b => simp [equal,meaning]
    | core tb vb sb kb =>
      simp [equal,meaning,(BinaryArithmetic.compare_spec va vb).2.1,
        (BinaryArithmetic.compare_spec ka kb).2.1,and_assoc]

theorem equal_refines {n L : ℕ} {a b : Key}
    {x y : CandidateEnumeration.Network n L}
    (ha : Represents a x) (hb : Represents b y) :
    (equal a b).1 = true ↔ x = y := by
  rw [equal_spec,ha,hb]
  exact labelMeaning_injective.eq_iff

/-- An optional typed dictionary adapter branches on the actual comparator.
The proof components are erased; they do not run a second equality procedure. -/
def decideEqual {n L : ℕ} (a b : Key) {x y : CandidateEnumeration.Network n L}
    (ha : Represents a x) (hb : Represents b y) : Decidable (x = y) × ℕ :=
  let r := equal a b
  if h : r.1 = true then
    (isTrue ((equal_refines ha hb).mp h),r.2+2)
  else
    (isFalse (fun hxy => h ((equal_refines ha hb).mpr hxy)),r.2+2)

@[simp] theorem decideEqual_work {n L : ℕ} (a b : Key)
    {x y : CandidateEnumeration.Network n L} (ha : Represents a x) (hb : Represents b y) :
    (decideEqual a b ha hb).2 = (equal a b).2+2 := by
  dsimp only [decideEqual]
  split <;> rfl

/-- The bound applies to actual stored lengths, allowing arbitrary padding. -/
def StoredBounded : Key → ℕ → Prop
  | .terminal _, _ => True
  | .core _ v _ k, B => v.length ≤ B ∧ k.length ≤ B

/-- A conservative encoded-value size, including all fixed-depth fields. -/
def representationSize : Key → ℕ
  | .terminal _ => 2
  | .core _ v _ k => 8+v.length+k.length

theorem representationSize_bound {a : Key} {B : ℕ} (h : StoredBounded a B) :
    representationSize a ≤ 2*B+8 := by
  cases a <;> simp only [StoredBounded,representationSize] at h ⊢ <;> omega

theorem equal_bound {a b : Key} {B : ℕ}
    (ha : StoredBounded a B) (hb : StoredBounded b B) :
    (equal a b).2 ≤ 32*(B+1)+12 := by
  cases a with
  | terminal a => cases b <;> simp [equal]
  | core ta va sa ka =>
    cases b with
    | terminal b => simp [equal]
    | core tb vb sb kb =>
      rcases ha with ⟨hva,hka⟩
      rcases hb with ⟨hvb,hkb⟩
      have hv := (BinaryArithmetic.compare_spec va vb).2.2
      have hk := (BinaryArithmetic.compare_spec ka kb).2.2
      have hvm := max_le hva hvb
      have hkm := max_le hka hkb
      change (BinaryArithmetic.compare va vb).steps+
        (BinaryArithmetic.compare ka kb).steps+12 ≤ _
      omega

/-- Pair keys are the actual keys used by the retained flow/capacity tables. -/
def pairEqual (a b : Key × Key) : Bool × ℕ :=
  let left := equal a.1 b.1
  let right := equal a.2 b.2
  (left.1 && right.1,left.2+right.2+4)

theorem pairEqual_spec (a b : Key × Key) :
    (pairEqual a b).1 = true ↔ (meaning a.1,meaning a.2) = (meaning b.1,meaning b.2) := by
  simp [pairEqual,equal_spec]

theorem pairEqual_refines {n L : ℕ} {a b : Key × Key}
    {x y : CandidateEnumeration.Network n L × CandidateEnumeration.Network n L}
    (ha₁ : Represents a.1 x.1) (ha₂ : Represents a.2 x.2)
    (hb₁ : Represents b.1 y.1) (hb₂ : Represents b.2 y.2) :
    (pairEqual a b).1 = true ↔ x = y := by
  simp only [pairEqual,Bool.and_eq_true_iff]
  rw [equal_refines ha₁ hb₁,equal_refines ha₂ hb₂]
  exact Prod.ext_iff.symm

theorem pairEqual_bound {a b : Key × Key} {B : ℕ}
    (ha₁ : StoredBounded a.1 B) (ha₂ : StoredBounded a.2 B)
    (hb₁ : StoredBounded b.1 B) (hb₂ : StoredBounded b.2 B) :
    (pairEqual a b).2 ≤ 64*(B+1)+28 := by
  have h₁ := equal_bound ha₁ hb₁
  have h₂ := equal_bound ha₂ hb₂
  change (equal a.1 b.1).2+(equal a.2 b.2).2+4 ≤ _
  omega

/-- Specification-level input encoding. The executable comparator above never
uses this map; the factory-body certificate must pay for constructing keys. -/
def canonicalEncoding {n L : ℕ} : CandidateEnumeration.Network n L → Key
  | .inl ((.inl v,b),k) => .core .internal v.val.bits b k.val.bits
  | .inl ((.inr (.inl v),b),k) => .core .source v.val.bits b k.val.bits
  | .inl ((.inr (.inr v),b),k) => .core .sink v.val.bits b k.val.bits
  | .inr b => .terminal b

@[simp] theorem canonicalEncoding_represents {n L : ℕ}
    (x : CandidateEnumeration.Network n L) : Represents (canonicalEncoding x) x := by
  rcases x with ⟨⟨p,b⟩,k⟩ | b
  · rcases p with v | v | v <;>
      simp [Represents,canonicalEncoding,meaning,labelMeaning,value_bits]
  · rfl

theorem canonicalEncoding_bounded {n L : ℕ} (x : CandidateEnumeration.Network n L) :
    StoredBounded (canonicalEncoding x) (CandidateEnumeration.labelBits n L) := by
  rcases x with ⟨⟨p,b⟩,k⟩ | b
  · rcases p with v | v | v <;>
      simp only [canonicalEncoding,StoredBounded,Nat.size_eq_bits_len] <;>
      exact ⟨CandidateEnumeration.base_scalar_bits v L,
        CandidateEnumeration.level_scalar_bits k n⟩
  · trivial

end DirectedFlowCutGap.EncodedLabelEquality
