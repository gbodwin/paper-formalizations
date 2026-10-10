import DirectedFlowCutGap.BinaryArithmetic

/-! Literal binary arithmetic for the fixed packing-prefix budget. The
expression is static; natural denotation and coefficient arithmetic occur
only in specifications and ghost charges. This accounts for Boolean/list
primitive annotations, before instruction-language storage compilation. -/
namespace DirectedFlowCutGap.BinaryBudgetExpression
open BinaryArithmetic

def copy : Bits → Bits × ℕ
  | [] => ([],1)
  | b :: bs => let r := copy bs; (b :: r.1,r.2+2)

theorem copy_spec (xs : Bits) : (copy xs).1 = xs ∧ (copy xs).2 = 2*xs.length+1 := by
  induction xs with
  | nil => exact ⟨rfl,rfl⟩
  | cons b bs ih => simp [copy,ih.1,ih.2]; omega

inductive Expr where
  | input : Fin 3 → Expr
  | literal : Bits → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr

def evaluate (inputs : Fin 3 → Bits) : Expr → Bits × ℕ
  | .input i => copy (inputs i)
  | .literal xs => copy xs
  | .plus a b =>
      let x := evaluate inputs a
      let y := evaluate inputs b
      let z := add false x.1 y.1
      (z.1,x.2+y.2+z.2+4)
  | .times a b =>
      let x := evaluate inputs a
      let y := evaluate inputs b
      let z := mul x.1 y.1
      (z.1,x.2+y.2+z.2+4)

def denote (inputs : Fin 3 → ℕ) : Expr → ℕ
  | .input i => inputs i
  | .literal xs => value xs
  | .plus a b => denote inputs a + denote inputs b
  | .times a b => denote inputs a * denote inputs b

theorem evaluate_value (inputs : Fin 3 → Bits) (e : Expr) :
    value (evaluate inputs e).1 = denote (fun i => value (inputs i)) e := by
  induction e with
  | input i => simp [evaluate,denote,(copy_spec _).1]
  | literal xs => simp [evaluate,denote,(copy_spec _).1]
  | plus a b ha hb =>
      simpa [evaluate,denote,ha,hb] using (add_spec false
        (evaluate inputs a).1 (evaluate inputs b).1).1
  | times a b ha hb =>
      simpa [evaluate,denote,ha,hb] using (mul_spec
        (evaluate inputs a).1 (evaluate inputs b).1).1

def widthCoefficient : Expr → ℕ
  | .input _ => 1
  | .literal xs => xs.length+1
  | .plus a b => max (widthCoefficient a) (widthCoefficient b)+1
  | .times a b => 2*widthCoefficient a+widthCoefficient b+1

def costCoefficient : Expr → ℕ
  | .input _ => 3
  | .literal xs => 2*xs.length+1
  | .plus a b => costCoefficient a+costCoefficient b+
      16*(max (widthCoefficient a) (widthCoefficient b)+1)+4
  | .times a b => costCoefficient a+costCoefficient b+
      64*(widthCoefficient a+1)*(widthCoefficient a+widthCoefficient b+2)+4

theorem evaluate_bounds (inputs : Fin 3 → Bits) (e : Expr) (L : ℕ)
    (h : ∀ i, (inputs i).length ≤ L) :
    (evaluate inputs e).1.length ≤ widthCoefficient e*(L+1) ∧
    (evaluate inputs e).2 ≤ costCoefficient e*(L+1)^2 := by
  have hX : 1 ≤ L+1 := by omega
  have hXX : L+1 ≤ (L+1)^2 := by nlinarith
  induction e with
  | input i =>
      simp only [evaluate,widthCoefficient,costCoefficient,(copy_spec _).1,
        (copy_spec _).2,one_mul]
      have hi := h i
      constructor <;> nlinarith
  | literal xs =>
      simp only [evaluate,widthCoefficient,costCoefficient,(copy_spec _).1,(copy_spec _).2]
      constructor <;> nlinarith
  | plus a b ha hb =>
      have hs := add_spec false (evaluate inputs a).1 (evaluate inputs b).1
      have hm : max (evaluate inputs a).1.length (evaluate inputs b).1.length ≤
          max (widthCoefficient a) (widthCoefficient b)*(L+1) :=
        max_le (ha.1.trans (Nat.mul_le_mul_right _ (le_max_left _ _)))
          (hb.1.trans (Nat.mul_le_mul_right _ (le_max_right _ _)))
      simp only [evaluate,widthCoefficient,costCoefficient]
      constructor
      · nlinarith [hs.2.1]
      · have hc : (add false (evaluate inputs a).1 (evaluate inputs b).1).2 ≤
            16*(max (widthCoefficient a) (widthCoefficient b)+1)*(L+1)^2 := by
          apply hs.2.2.trans
          calc
            _ ≤ 16*(max (widthCoefficient a) (widthCoefficient b)+1)*(L+1) := by nlinarith
            _ ≤ _ := Nat.mul_le_mul_left _ hXX
        nlinarith [ha.2,hb.2]
  | times a b ha hb =>
      have hs := mul_spec (evaluate inputs a).1 (evaluate inputs b).1
      simp only [evaluate,widthCoefficient,costCoefficient]
      constructor
      · nlinarith [hs.2.1,ha.1,hb.1]
      · have hc : (mul (evaluate inputs a).1 (evaluate inputs b).1).2 ≤
            64*(widthCoefficient a+1)*(widthCoefficient a+widthCoefficient b+2)*(L+1)^2 := by
          apply hs.2.2.trans
          calc
            _ ≤ 64*((widthCoefficient a+1)*(L+1))*
                ((widthCoefficient a+widthCoefficient b+2)*(L+1)) := by
              gcongr <;> nlinarith [ha.1,hb.1]
            _ = _ := by ring
        nlinarith [ha.2,hb.2]

end DirectedFlowCutGap.BinaryBudgetExpression
