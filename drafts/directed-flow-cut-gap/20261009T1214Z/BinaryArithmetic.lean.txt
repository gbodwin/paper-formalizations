import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-!
# Explicit binary-list addition and multiplication

Inputs and outputs are little-endian Boolean lists; leading zeroes are allowed.
The executed routines use Boolean gates, list constructors and list cases.
Their natural denotation occurs only in specifications. The returned charge
counts a conservative fixed allowance per Boolean/list arm. A bit or
logarithmic-cost RAM interpretation must additionally charge heap-address widths
and initial/storage cells; list pointers are not unit-cost bits. This is not a
claim about native Lean compiler performance.
Charge fields are ghost instrumentation, as in RawNonnegativeRational; their
natural arithmetic is not part of computing the returned binary value.
The primitive realization must still be joined to the program's operation and
operand bounds before claiming a whole-program bit-runtime theorem.
-/
namespace DirectedFlowCutGap.BinaryArithmetic

abbrev Bits := List Bool

/-- Mathematical denotation, absent from the arithmetic implementations. -/
def value : Bits → ℕ
  | [] => 0
  | b::bs => b.toNat+2*value bs

theorem value_lt (bs : Bits) : value bs < 2^bs.length := by
  induction bs with
  | nil => simp [value]
  | cons b bs ih =>
      cases b <;> simp only [value,Bool.toNat_false,Bool.toNat_true,List.length_cons]
        <;> rw [pow_succ] <;> omega

theorem value_bits (n : ℕ) : value n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [value]
  | bit b n h ih =>
      rw [Nat.bits_append_bit n b h]
      cases b <;> simp [value,ih,Nat.bit,Nat.add_comm]

/-- A one-bit full adder: low output bit and carry bit. -/
def fullAdder (a b c : Bool) : Bool × Bool :=
  (xor (xor a b) c, (a && b) || (a && c) || (b && c))

theorem fullAdder_value (a b c : Bool) :
    (fullAdder a b c).1.toNat+2*(fullAdder a b c).2.toNat =
      a.toNat+b.toNat+c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

/-- Carry propagation reuses the untouched suffix when the carry is false. -/
def increment : Bool → Bits → Bits × ℕ
  | false, xs => (xs,1)
  | true, [] => ([true],1)
  | true, false::xs => (true::xs,4)
  | true, true::xs =>
      let r := increment true xs
      (false::r.1,r.2+8)

theorem increment_spec (c : Bool) (xs : Bits) :
    value (increment c xs).1 = value xs+c.toNat ∧
    (increment c xs).1.length ≤ xs.length+1 ∧
    (increment c xs).2 ≤ 8*(xs.length+1) := by
  induction xs generalizing c with
  | nil => cases c <;> simp [increment,value]
  | cons a xs ih =>
      cases c with
      | false => simp [increment,value]; omega
      | true =>
          cases a with
          | false => simp [increment,value]; omega
          | true =>
              have h := ih true
              simp only [increment,value,Bool.toNat_false,Bool.toNat_true,
                List.length_cons,zero_add] at h ⊢
              omega

/-- The actual ripple-carry algorithm; no natural addition computes its result. -/
def add : Bool → Bits → Bits → Bits × ℕ
  | c, [], ys => increment c ys
  | c, x::xs, [] => increment c (x::xs)
  | c, x::xs, y::ys =>
      let a := fullAdder x y c
      let r := add a.2 xs ys
      (a.1::r.1,r.2+16)

theorem add_spec (c : Bool) (xs ys : Bits) :
    value (add c xs ys).1 = value xs+value ys+c.toNat ∧
    (add c xs ys).1.length ≤ max xs.length ys.length+1 ∧
    (add c xs ys).2 ≤ 16*(max xs.length ys.length+1) := by
  induction xs generalizing ys c with
  | nil =>
      have h := increment_spec c ys
      simpa only [add,value,List.length_nil,max_eq_right (Nat.zero_le _),zero_add]
        using ⟨h.1,h.2.1,h.2.2.trans (by omega)⟩
  | cons x xs ih =>
      cases ys with
      | nil =>
          have h := increment_spec c (x::xs)
          simp only [List.length_cons] at h
          simpa only [add,value,List.length_nil,List.length_cons,
            max_eq_left (Nat.zero_le _),add_zero] using
            ⟨h.1,h.2.1,h.2.2.trans (by omega)⟩
      | cons y ys =>
          have h := ih (fullAdder x y c).2 ys
          have ha := fullAdder_value x y c
          simp only [add,value,List.length_cons]
          have hm : max (xs.length+1) (ys.length+1) = max xs.length ys.length+1 := by omega
          rw [hm]
          constructor
          · omega
          constructor <;> omega

/-- Schoolbook multiplication scans one bit and performs at most one addition. -/
def mul : Bits → Bits → Bits × ℕ
  | [], _ => ([],1)
  | x::xs, ys =>
      let r := mul xs ys
      if x then
        let a := add false ys (false::r.1)
        (a.1,r.2+a.2+16)
      else (false::r.1,r.2+4)

theorem mul_spec (xs ys : Bits) :
    value (mul xs ys).1 = value xs*value ys ∧
    (mul xs ys).1.length ≤ 2*xs.length+ys.length+1 ∧
    (mul xs ys).2 ≤ 64*(xs.length+1)*(xs.length+ys.length+2) := by
  induction xs with
  | nil => simp [mul,value]; omega
  | cons x xs ih =>
      have ha := add_spec false ys (false::(mul xs ys).1)
      have hm : max ys.length ((mul xs ys).1.length+1) ≤
          2*xs.length+ys.length+2 := by omega
      cases x with
      | false =>
          simp only [mul,Bool.false_eq_true,ite_false,value,Bool.toNat_false,zero_add,
            List.length_cons]
          refine ⟨?_,?_,?_⟩
          · rw [ih.1]; ring
          · omega
          · nlinarith [ih.2.2]
      | true =>
          simp only [mul,ite_true,value,Bool.toNat_true,List.length_cons]
          simp only [value,Bool.toNat_false,zero_add,List.length_cons,add_zero] at ha
          refine ⟨?_,?_,?_⟩
          · rw [ha.1,ih.1]; ring
          · omega
          · nlinarith [ha.2.2,ih.2.2]

/-- A binary-width bound is about actual representation length, including any
leading zeroes, rather than a favorable reduced encoding. -/
theorem arithmetic_charge_bound {xs ys : Bits} {B : ℕ}
    (hx : xs.length ≤ B) (hy : ys.length ≤ B) :
    (add false xs ys).2 ≤ 16*(B+1) ∧
    (mul xs ys).2 ≤ 128*(B+1)^2 := by
  have ha := (add_spec false xs ys).2.2
  have hm := (mul_spec xs ys).2.2
  constructor
  · have hh : max xs.length ys.length ≤ B := max_le hx hy
    nlinarith
  · calc
      _ ≤ 64*(xs.length+1)*(xs.length+ys.length+2) := hm
      _ ≤ 64*(B+1)*(B+B+2) := by gcongr
      _ = 128*(B+1)^2 := by ring

/-- Zero testing scans bits and stops at the first one. -/
def isZero : Bits → Bool × ℕ
  | [] => (true,1)
  | false::xs => let r := isZero xs; (r.1,r.2+4)
  | true::_ => (false,4)

theorem isZero_spec (xs : Bits) :
    ((isZero xs).1=true ↔ value xs=0) ∧ (isZero xs).2 ≤ 4*(xs.length+1) := by
  induction xs with
  | nil => simp [isZero,value]
  | cons x xs ih =>
      cases x with
      | false =>
          constructor
          · simp only [isZero,value,Bool.toNat_false,zero_add]
            rw [ih.1]
            omega
          · change (isZero xs).2+4≤4*(xs.length+1+1)
            omega
      | true => simp [isZero,value]

structure Comparison where
  less : Bool
  equal : Bool
  steps : ℕ

/-- More significant bits decide first; this also handles noncanonical zeroes. -/
def compare : Bits → Bits → Comparison
  | [], ys => let z := isZero ys; ⟨!z.1,z.1,z.2+4⟩
  | x::xs, [] => let z := isZero (x::xs); ⟨false,z.1,z.2+4⟩
  | x::xs, y::ys =>
      let r := compare xs ys
      ⟨r.less || (r.equal && !x && y), r.equal && (x==y),r.steps+16⟩

theorem compare_spec (xs ys : Bits) :
    ((compare xs ys).less=true ↔ value xs<value ys) ∧
    ((compare xs ys).equal=true ↔ value xs=value ys) ∧
    (compare xs ys).steps ≤ 16*(max xs.length ys.length+1) := by
  induction xs generalizing ys with
  | nil =>
      have h := isZero_spec ys
      simp only [compare,value,List.length_nil,max_eq_right (Nat.zero_le _)]
      cases hz : (isZero ys).1 <;> simp [hz] at h ⊢ <;> omega
  | cons x xs ih =>
      cases ys with
      | nil =>
          have h := isZero_spec (x::xs)
          simp only [List.length_cons] at h
          simp only [compare,List.length_nil,max_eq_left (Nat.zero_le _),value,List.length_cons]
          refine ⟨by simp,?_,?_⟩
          · simpa only [value] using h.1
          · omega
      | cons y ys =>
          have h := ih ys
          have hm : max (xs.length+1) (ys.length+1) = max xs.length ys.length+1 := by omega
          simp only [compare,value,List.length_cons,hm]
          cases hl : (compare xs ys).less <;> cases he : (compare xs ys).equal <;>
            cases x <;> cases y <;> simp [hl,he] at h ⊢ <;> omega

/-- Exact comparison used by raw-rational cross products. -/
def lessEqual (xs ys : Bits) : Bool × ℕ :=
  let r := compare xs ys
  (r.less || r.equal,r.steps+1)

theorem lessEqual_spec (xs ys : Bits) :
    ((lessEqual xs ys).1=true ↔ value xs≤value ys) ∧
    (lessEqual xs ys).2 ≤ 17*(max xs.length ys.length+1) := by
  have h := compare_spec xs ys
  simp only [lessEqual,Bool.or_eq_true]
  constructor
  · rw [h.1,h.2.1]
    omega
  · omega

/-- Canonical binary representations have no most-significant zero. -/
inductive Normal : Bits → Prop where
  | nil : Normal []
  | digit {b : Bool} {xs : Bits} (tail : Normal xs) (last : xs=[] → b=true) : Normal (b::xs)

theorem normal_zero {xs : Bits} (h : Normal xs) : value xs=0 ↔ xs=[] := by
  induction h with
  | nil => simp [value]
  | @digit b xs ht last ih =>
      cases b <;> simp [value] at *
      all_goals aesop

theorem normal_bits {xs : Bits} (h : Normal xs) : (value xs).bits=xs := by
  induction h with
  | nil => simp [value]
  | @digit b xs ht last ih =>
      have hz : value xs=0 → b=true := fun hzero => last ((normal_zero ht).mp hzero)
      have hb : value (b::xs) = Nat.bit b (value xs) := by cases b <;> simp [value,Nat.bit,Nat.add_comm]
      rw [hb,Nat.bits_append_bit _ _ hz,ih]

/-- Remove only leading zero bits; no rational GCD normalization is involved. -/
def trim : Bits → Bits × ℕ
  | [] => ([],1)
  | b::xs =>
      let r := trim xs
      if r.1.isEmpty && !b then ([],r.2+8) else (b::r.1,r.2+8)

theorem trim_spec (xs : Bits) : Normal (trim xs).1 ∧
    value (trim xs).1=value xs ∧ (trim xs).1.length≤xs.length ∧
    (trim xs).2=8*xs.length+1 := by
  induction xs with
  | nil => exact ⟨.nil,rfl,le_rfl,by rfl⟩
  | cons b xs ih =>
      by_cases hz : (trim xs).1=[]
      · cases b with
        | false =>
            have hv : value xs=0 := by rw [← ih.2.1,hz]; rfl
            simp only [trim,hz,List.isEmpty_nil,Bool.not_false,Bool.and_self,ite_true,
              value,Bool.toNat_false,zero_add,List.length_nil,List.length_cons]
            exact ⟨.nil,by omega,Nat.zero_le _,by rw [ih.2.2.2];ring⟩
        | true =>
            simp only [trim,hz,List.isEmpty_nil,Bool.not_true,Bool.and_false,Bool.false_eq_true,ite_false]
            refine ⟨.digit .nil (by intro _;rfl),?_,?_,?_⟩
            · simp only [value,Bool.toNat_true]
              rw [← ih.2.1,hz]
              rfl
            · simp
            · rw [ih.2.2.2];simp only [List.length_cons];ring
      · have he : (trim xs).1.isEmpty=false := by cases h : (trim xs).1 <;> simp_all
        simp only [trim,he,Bool.false_and,Bool.false_eq_true,ite_false]
        refine ⟨.digit ih.1 (fun h => (hz h).elim),?_,?_,?_⟩
        · simp only [value,ih.2.1]
        · simpa only [List.length_cons] using Nat.add_le_add_right ih.2.2.1 1
        · rw [ih.2.2.2];simp only [List.length_cons];ring

theorem trim_length (xs : Bits) : (trim xs).1.length = Nat.size (value xs) := by
  have ht := trim_spec xs
  have hb := normal_bits ht.1
  have h := Nat.size_eq_bits_len (value (trim xs).1)
  rw [hb,ht.2.1] at h
  exact h

/-- Canonicalization prevents repeated products from accumulating redundant bits. -/
def addCanonical (xs ys : Bits) : Bits × ℕ :=
  let r := add false xs ys
  let t := trim r.1
  (t.1,r.2+t.2+4)

def mulCanonical (xs ys : Bits) : Bits × ℕ :=
  let r := mul xs ys
  let t := trim r.1
  (t.1,r.2+t.2+4)

theorem canonical_values (xs ys : Bits) :
    value (addCanonical xs ys).1=value xs+value ys ∧
    value (mulCanonical xs ys).1=value xs*value ys ∧
    (addCanonical xs ys).1.length=Nat.size (value xs+value ys) ∧
    (mulCanonical xs ys).1.length=Nat.size (value xs*value ys) := by
  have ha := (add_spec false xs ys).1
  have hm := (mul_spec xs ys).1
  simp only [Bool.toNat_false,add_zero] at ha
  simp only [addCanonical,mulCanonical,(trim_spec _).2.1,trim_length,ha,hm]
  trivial

theorem canonical_charges {xs ys : Bits} {B : ℕ}
    (hx : xs.length≤B) (hy : ys.length≤B) :
    (addCanonical xs ys).2≤32*(B+2) ∧
    (mulCanonical xs ys).2≤512*(B+1)^2 := by
  have ha := add_spec false xs ys
  have hm := mul_spec xs ys
  have hcost := arithmetic_charge_bound hx hy
  have htA := (trim_spec (add false xs ys).1).2.2.2
  have htM := (trim_spec (mul xs ys).1).2.2.2
  have hmax : max xs.length ys.length≤B := max_le hx hy
  simp only [addCanonical,mulCanonical]
  constructor <;> nlinarith [ha.2.1,hm.2.1]

/-- Borrow propagation; the public predecessor first excludes the all-zero case. -/
def predCore : Bits → Bits × ℕ
  | [] => ([],1)
  | true::xs => (false::xs,4)
  | false::xs => let r := predCore xs; (true::r.1,r.2+8)

theorem predCore_spec (xs : Bits) :
    (0<value xs → value (predCore xs).1+1=value xs) ∧
    (predCore xs).1.length≤xs.length ∧
    (predCore xs).2≤8*(xs.length+1) := by
  induction xs with
  | nil => simp [predCore,value]
  | cons x xs ih =>
      cases x with
      | true => simp [predCore,value];omega
      | false =>
          simp only [predCore,value,Bool.toNat_false,Bool.toNat_true,zero_add,List.length_cons]
          refine ⟨?_,?_,?_⟩
          · intro h
            have hh := ih.1 (by omega)
            omega
          · omega
          · omega

/-- Natural predecessor, including zero and noncanonical input representations. -/
def predecessor (xs : Bits) : Bits × ℕ :=
  let z := isZero xs
  if z.1 then ([],z.2+4) else
    let r := predCore xs
    let t := trim r.1
    (t.1,z.2+r.2+t.2+8)

theorem predecessor_spec (xs : Bits) :
    value (predecessor xs).1=value xs-1 ∧
    (predecessor xs).1.length=Nat.size (value xs-1) ∧
    (predecessor xs).2≤32*(xs.length+1) := by
  have hz := isZero_spec xs
  have hp := predCore_spec xs
  have ht := trim_spec (predCore xs).1
  by_cases hzero : (isZero xs).1=true
  · have hv := hz.1.mp hzero
    simp only [predecessor,hzero,ite_true,value,List.length_nil,hv,Nat.zero_sub,Nat.size_zero]
    exact ⟨trivial,trivial,by omega⟩
  · have hb : (isZero xs).1=false := by cases h : (isZero xs).1 <;> simp_all
    have hv : 0<value xs := Nat.pos_of_ne_zero (fun h => hzero (hz.1.mpr h))
    have hpv := hp.1 hv
    simp only [predecessor,hb,Bool.false_eq_true,ite_false,ht.2.1,trim_length]
    refine ⟨by omega,?_,?_⟩
    · congr 1;omega
    · nlinarith [ht.2.2.2,hp.2.1,hp.2.2,hz.2]

end DirectedFlowCutGap.BinaryArithmetic
