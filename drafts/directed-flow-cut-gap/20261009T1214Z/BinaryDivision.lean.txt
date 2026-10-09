import DirectedFlowCutGap.BinaryArithmetic

/-!
# Boolean-list subtraction and long division

The executed value computations use only Boolean gates, list cases and list
constructors. Natural subtraction, division, remainder and denotation occur
only in specifications; no quotient is computed by a natural-number primitive.
Leading zeroes are allowed on both inputs. Division by zero returns quotient
zero and the canonicalized numerator as remainder, matching `Nat.div`/`Nat.mod`.

The conservative charge uses the persistent-list bit model of BinaryArithmetic.
Returned charge fields and their arithmetic are ghost instrumentation. The
allowances include Boolean gates, list cases/constructors and result records;
they do not purport to count a particular Lean compiler's machine instructions.
This standalone count treats list/record pointer operations as instructions.
A whole-program bit/RAM bound must separately charge bounded heap addresses
and join these primitive bounds to the actual program trace and operand widths.
-/
namespace DirectedFlowCutGap.BinaryDivision

open BinaryArithmetic

/-- One-bit subtraction: difference digit and borrow into the next digit. -/
def fullSubtractor (a b c : Bool) : Bool × Bool :=
  (xor (xor a b) c, (!a && (b || c)) || (b && c))

theorem fullSubtractor_value (a b c : Bool) :
    a.toNat+2*(fullSubtractor a b c).2.toNat =
      (fullSubtractor a b c).1.toNat+b.toNat+c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

/-- Fixed-width borrow propagation. Its denotation theorem requires enough
minuend; the public `sub` tests this condition using Boolean comparison. -/
def subtractCore : Bool → Bits → Bits → Bits × ℕ
  | _, [], _ => ([],1)
  | c, x::xs, [] =>
      let a := fullSubtractor x false c
      let r := subtractCore a.2 xs []
      (a.1::r.1,r.2+24)
  | c, x::xs, y::ys =>
      let a := fullSubtractor x y c
      let r := subtractCore a.2 xs ys
      (a.1::r.1,r.2+24)

theorem subtractCore_bounds (c : Bool) (xs ys : Bits) :
    (subtractCore c xs ys).1.length=xs.length ∧
    (subtractCore c xs ys).2=24*xs.length+1 := by
  induction xs generalizing c ys with
  | nil => simp [subtractCore]
  | cons x xs ih =>
      cases ys with
      | nil =>
          have h := ih (fullSubtractor x false c).2 []
          simp only [subtractCore,List.length_cons,h.1,h.2]
          exact ⟨trivial,by omega⟩
      | cons y ys =>
          have h := ih (fullSubtractor x y c).2 ys
          simp only [subtractCore,List.length_cons,h.1,h.2]
          exact ⟨trivial,by omega⟩

theorem subtractCore_value (c : Bool) (xs ys : Bits)
    (h : value ys+c.toNat≤value xs) :
    value (subtractCore c xs ys).1+value ys+c.toNat=value xs := by
  induction xs generalizing c ys with
  | nil => simp only [subtractCore,value] at h ⊢; omega
  | cons x xs ih =>
      cases ys with
      | nil =>
          have ha := fullSubtractor_value x false c
          simp only [Bool.toNat_false] at ha
          have hbit : (fullSubtractor x false c).1.toNat≤1 := by
            cases (fullSubtractor x false c).1 <;> decide
          have ht : value ([] : Bits)+(fullSubtractor x false c).2.toNat≤value xs := by
            simp only [value] at h ⊢
            omega
          have hr := ih (fullSubtractor x false c).2 [] ht
          simp only [subtractCore,value] at hr ⊢
          omega
      | cons y ys =>
          have ha := fullSubtractor_value x y c
          have hbit : (fullSubtractor x y c).1.toNat≤1 := by
            cases (fullSubtractor x y c).1 <;> decide
          have ht : value ys+(fullSubtractor x y c).2.toNat≤value xs := by
            simp only [value] at h
            omega
          have hr := ih (fullSubtractor x y c).2 ys ht
          simp only [subtractCore,value]
          omega

/-- Canonical saturating natural subtraction, including noncanonical inputs. -/
def sub (xs ys : Bits) : Bits × ℕ :=
  let c := BinaryArithmetic.compare xs ys
  if c.less then ([],c.steps+4) else
    let r := subtractCore false xs ys
    let t := trim r.1
    (t.1,c.steps+r.2+t.2+8)

theorem sub_spec (xs ys : Bits) :
    value (sub xs ys).1=value xs-value ys ∧
    (sub xs ys).1.length=Nat.size (value xs-value ys) ∧
    (sub xs ys).2≤64*(xs.length+ys.length+1) := by
  have hc := compare_spec xs ys
  have hb := subtractCore_bounds false xs ys
  have ht := trim_spec (subtractCore false xs ys).1
  by_cases hl : (BinaryArithmetic.compare xs ys).less=true
  · have hv := hc.1.mp hl
    simp only [sub,hl,ite_true,value,List.length_nil,Nat.sub_eq_zero_of_le hv.le,Nat.size_zero]
    have hm : max xs.length ys.length≤xs.length+ys.length := by omega
    exact ⟨trivial,trivial,by omega⟩
  · have hf : (BinaryArithmetic.compare xs ys).less=false := by cases h : (BinaryArithmetic.compare xs ys).less <;> simp_all
    have hv : value ys≤value xs := le_of_not_gt (fun h => hl (hc.1.mpr h))
    have hr := subtractCore_value false xs ys (by simpa using hv)
    simp only [Bool.toNat_false,add_zero] at hr
    have he : value (subtractCore false xs ys).1=value xs-value ys := by omega
    simp only [sub,hf,Bool.false_eq_true,ite_false,ht.2.1,trim_length,he]
    have hm : max xs.length ys.length≤xs.length+ys.length := by omega
    exact ⟨trivial,trivial,by omega⟩

structure Division where
  quotient : Bits
  remainder : Bits
  steps : ℕ

/-- Binary long division visits the most significant suffix first. At each
step the trial remainder is `2*r+b`, so at most one subtraction is needed.
The 64-instruction local allowance covers calls, record projections/wrappers,
the comparison branch and both trial/quotient list constructors. -/
def divideCore : Bits → Bits → Division
  | [], _ => ⟨[],[],1⟩
  | b::bs, ys =>
      let r := divideCore bs ys
      let trial := b::r.remainder
      let c := BinaryArithmetic.compare trial ys
      if c.less then
        ⟨false::r.quotient,trial,r.steps+c.steps+64⟩
      else
        let s := subtractCore false trial ys
        ⟨true::r.quotient,s.1,r.steps+c.steps+s.2+64⟩

theorem divideCore_value (xs ys : Bits) (hy : 0<value ys) :
    value (divideCore xs ys).quotient*value ys+
      value (divideCore xs ys).remainder=value xs ∧
    value (divideCore xs ys).remainder<value ys := by
  induction xs with
  | nil => simp [divideCore,value,hy]
  | cons b bs ih =>
      have hc := compare_spec (b::(divideCore bs ys).remainder) ys
      have hbit : b.toNat≤1 := by cases b <;> decide
      by_cases hl : (BinaryArithmetic.compare (b::(divideCore bs ys).remainder) ys).less=true
      · have hv := hc.1.mp hl
        simp only [divideCore,hl,ite_true,value,Bool.toNat_false,zero_add]
        simp only [value] at hv
        constructor
        · nlinarith [ih.1]
        · exact hv
      · have hf : (BinaryArithmetic.compare (b::(divideCore bs ys).remainder) ys).less=false := by
          cases h : (BinaryArithmetic.compare (b::(divideCore bs ys).remainder) ys).less <;> simp_all
        have hv : value ys≤value (b::(divideCore bs ys).remainder) := by
          exact le_of_not_gt (fun h => hl (hc.1.mpr h))
        have hs := subtractCore_value false (b::(divideCore bs ys).remainder) ys
          (by simpa using hv)
        simp only [Bool.toNat_false,add_zero,value] at hs
        simp only [divideCore,hf,Bool.false_eq_true,ite_false,value,Bool.toNat_true]
        constructor
        · nlinarith [ih.1]
        · omega

theorem divideCore_bounds (xs ys : Bits) :
    (divideCore xs ys).quotient.length=xs.length ∧
    (divideCore xs ys).remainder.length≤xs.length ∧
    (divideCore xs ys).steps≤128*(xs.length+1)*(xs.length+ys.length+2) := by
  induction xs with
  | nil => simp [divideCore]; omega
  | cons b bs ih =>
      have hc := (compare_spec (b::(divideCore bs ys).remainder) ys).2.2
      have hs := subtractCore_bounds false (b::(divideCore bs ys).remainder) ys
      have hm : max (b::(divideCore bs ys).remainder).length ys.length≤
          bs.length+ys.length+1 := by simp only [List.length_cons]; omega
      simp only [List.length_cons] at hs hc hm
      by_cases hl : (BinaryArithmetic.compare (b::(divideCore bs ys).remainder) ys).less=true
      · simp only [divideCore,hl,ite_true,List.length_cons]
        refine ⟨by omega,by omega,?_⟩
        nlinarith [ih.2.2]
      · have hf : (BinaryArithmetic.compare (b::(divideCore bs ys).remainder) ys).less=false := by
          cases h : (BinaryArithmetic.compare (b::(divideCore bs ys).remainder) ys).less <;> simp_all
        simp only [divideCore,hf,Bool.false_eq_true,ite_false,List.length_cons]
        refine ⟨by omega,by omega,?_⟩
        nlinarith [ih.2.2]

/-- Total division with canonical quotient/remainder and an explicit zero test.
The zero denominator branch returns `(0,numerator)`. -/
def divide (xs ys : Bits) : Division :=
  let z := isZero ys
  if z.1 then
    let t := trim xs
    ⟨[],t.1,z.2+t.2+16⟩
  else
    let r := divideCore xs ys
    let q := trim r.quotient
    let s := trim r.remainder
    ⟨q.1,s.1,z.2+r.steps+q.2+s.2+32⟩

theorem divide_spec (xs ys : Bits) :
    value (divide xs ys).quotient=value xs/value ys ∧
    value (divide xs ys).remainder=value xs%value ys ∧
    (divide xs ys).quotient.length=Nat.size (value xs/value ys) ∧
    (divide xs ys).remainder.length=Nat.size (value xs%value ys) := by
  have hz := isZero_spec ys
  by_cases hzero : (isZero ys).1=true
  · have hv := hz.1.mp hzero
    simp [divide,hzero,hv,value,(trim_spec xs).2.1,trim_length]
  · have hf : (isZero ys).1=false := by cases h : (isZero ys).1 <;> simp_all
    have hy : 0<value ys := Nat.pos_of_ne_zero (fun h => hzero (hz.1.mpr h))
    have hr := divideCore_value xs ys hy
    have hq : value (divideCore xs ys).quotient=value xs/value ys := by
      symm
      apply Nat.div_eq_of_lt_le <;> nlinarith [hr.1,hr.2]
    have hs : value (divideCore xs ys).remainder=value xs%value ys := by
      have he := Nat.div_add_mod' (value xs) (value ys)
      rw [← hq] at he
      omega
    simp only [divide,hf,Bool.false_eq_true,ite_false,(trim_spec _).2.1,trim_length,hq,hs]
    trivial

theorem divide_charge (xs ys : Bits) :
    (divide xs ys).steps≤256*(xs.length+ys.length+2)^2 := by
  have hz := (isZero_spec ys).2
  have hr := divideCore_bounds xs ys
  have htx := (trim_spec xs).2.2.2
  have htq := (trim_spec (divideCore xs ys).quotient).2.2.2
  have htr := (trim_spec (divideCore xs ys).remainder).2.2.2
  by_cases hzero : (isZero ys).1=true
  · simp only [divide,hzero,ite_true]
    nlinarith [Nat.zero_le (xs.length*xs.length),Nat.zero_le (ys.length*ys.length),
      Nat.zero_le (xs.length*ys.length)]
  · have hf : (isZero ys).1=false := by cases h : (isZero ys).1 <;> simp_all
    simp only [divide,hf,Bool.false_eq_true,ite_false]
    nlinarith [hr.2.2,Nat.zero_le (ys.length*ys.length)]

/-- An input-width-only polynomial bound, including leading zeroes. -/
theorem divide_charge_bound {xs ys : Bits} {B : ℕ}
    (hx : xs.length≤B) (hy : ys.length≤B) :
    (divide xs ys).steps≤1024*(B+1)^2 := by
  calc
    _ ≤ 256*(xs.length+ys.length+2)^2 := divide_charge xs ys
    _ ≤ 256*(B+B+2)^2 := by gcongr
    _ = 1024*(B+1)^2 := by ring

/-- The public total convention satisfies the division equation even at zero. -/
theorem divide_equation (xs ys : Bits) :
    value (divide xs ys).quotient*value ys+value (divide xs ys).remainder=value xs := by
  have h := divide_spec xs ys
  rw [h.1,h.2.1]
  exact Nat.div_add_mod' _ _

theorem divide_remainder_lt (xs ys : Bits) (hy : 0<value ys) :
    value (divide xs ys).remainder<value ys := by
  rw [(divide_spec xs ys).2.1]
  exact Nat.mod_lt _ hy

theorem divide_zero (xs ys : Bits) (hy : value ys=0) :
    (divide xs ys).quotient=[] ∧ (divide xs ys).remainder=(trim xs).1 := by
  have hz := (isZero_spec ys).1.mpr hy
  simp [divide,hz]

end DirectedFlowCutGap.BinaryDivision
