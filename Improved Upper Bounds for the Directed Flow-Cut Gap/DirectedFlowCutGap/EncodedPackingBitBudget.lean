import DirectedFlowCutGap.BinaryBudgetExpression
import DirectedFlowCutGap.QueryBudgetArithmetic

/-! A closed binary add/multiply/copy program computes the explicit packing
prefix polynomial. Every literal is a supplied fixed Boolean word; no
natural-to-binary conversion or decoded-natural branch computes the output.
The cost is the underlying Boolean/list annotation, prior to heap compilation. -/
namespace DirectedFlowCutGap.EncodedPackingBitBudget
open BinaryArithmetic BinaryBudgetExpression

private def one : Expr := .literal [true]
private def two : Expr := .literal [false,true]
private def three : Expr := .literal [true,true]
private def twentyFour : Expr := .literal [false,false,false,true,true]
private def sq (x : Expr) : Expr := .times x x
private def cube (x : Expr) : Expr := .times (sq x) x

def query (x : Expr) : Expr :=
  .times (.times (.times (.plus (cube x) two) (sq x))
    (.plus (.times (.plus (cube x) two) (.times (.times two x) x)) three))
    (.plus (.plus (sq x) x) two)

def body : Expr :=
  let n := Expr.input 0
  let b := Expr.input 1
  let s := Expr.input 2
  let calls := Expr.plus (.times three (sq n)) one
  let exponent := Expr.plus (.plus (.plus (.times three (sq n)) (.times two b)) n) three
  let repeated := Expr.plus (.times three exponent) one
  let ticketFuel := Expr.plus (.plus (.times two b) n) three
  let ticketWidth := Expr.plus (.times (.times three (sq n)) (.plus s one)) two
  .plus (.times calls (.times repeated (query (.times twentyFour (sq n)))))
    (.times ticketFuel ticketWidth)

def run (n b s : Bits) : Bits × ℕ := evaluate ![n,b,s] body

theorem query_value (inputs : Fin 3 → ℕ) (x : Expr) :
    denote inputs (query x) = QueryBudgetArithmetic.polynomial (denote inputs x) := by
  simp only [query,denote,two,three,sq,cube,
    BinaryArithmetic.value,Bool.toNat_false,Bool.toNat_true]
  unfold QueryBudgetArithmetic.polynomial
  ring

/-- The fixed expression has precisely the already specified polynomial value. -/
theorem run_value (n b s : Bits) :
    value (run n b s).1 =
      (3*(value n)^2+1)*((3*(3*(value n)^2+2*value b+value n+3)+1)*
        QueryBudgetArithmetic.polynomial (24*(value n)^2))+
          (2*value b+value n+3)*(3*(value n)^2*(value s+1)+2) := by
  rw [run,evaluate_value]
  simp only [body,denote,query_value,one,two,three,twentyFour,sq,
    BinaryArithmetic.value,Bool.toNat_false,Bool.toNat_true,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons]
  congr 2 <;> ring

/-- Constants depend only on the displayed fixed arithmetic expression. -/
theorem run_bounds (n b s : Bits) (L : ℕ)
    (hn : n.length ≤ L) (hb : b.length ≤ L) (hs : s.length ≤ L) :
    (run n b s).1.length ≤ widthCoefficient body*(L+1) ∧
    (run n b s).2 ≤ costCoefficient body*(L+1)^2 := by
  apply evaluate_bounds
  intro i
  fin_cases i <;> simp_all

end DirectedFlowCutGap.EncodedPackingBitBudget
