import DirectedFlowCutGap.ConcreteExpressionProgram

/-! Static expression-dependent coefficients bound the concrete compiler's
output width, actual successful instruction count and actual heap growth. -/
namespace DirectedFlowCutGap.ConcreteExpressionBounds
open BinaryArithmetic ConcreteExpressionProgram ImmutableReferenceSimulation ImmutableReferenceTerminal

def width : Term → ℕ
  | .input _ => 1
  | .nil => 1
  | .cons _ t => width t+1
  | .binary _ a b => 2*width a+width b+1

def cost : Term → ℕ
  | .input _ => 1
  | .nil => 2
  | .cons _ t => cost t+4
  | .binary _ a b => cost a+cost b+100*(width a+1)*(width a+width b+2)+6

theorem arithmetic_bounds (m : Bool) (xs ys : Bits) :
    (arithmeticWord m xs ys).length ≤ 2*xs.length+ys.length+1 ∧
    arithmeticSteps m xs ys ≤ 100*(xs.length+1)*(xs.length+ys.length+2) ∧
    arithmeticCells m xs ys ≤ 100*(xs.length+1)*(xs.length+ys.length+2) := by
  cases m with
  | false =>
      have ha := add_spec false xs ys
      have hs := BinaryAdditionProgram.steps_bound false xs ys
      have hc := BinaryAdditionProgram.cells_bound false xs ys
      simp only [arithmeticWord,arithmeticSteps,arithmeticCells,Bool.false_eq_true,ite_false]
      have hm : max xs.length ys.length ≤ xs.length+ys.length := max_le (by omega) (by omega)
      constructor
      · omega
      · constructor <;> nlinarith
  | true =>
      have ha := mul_spec xs ys
      have hs := BinaryMultiplicationProgram.steps_bound xs ys
      have hc := BinaryMultiplicationProgram.cells_bound xs ys
      simp only [arithmeticWord,arithmeticSteps,arithmeticCells,ite_true]
      exact ⟨ha.2.1,by nlinarith,by nlinarith⟩

theorem evaluate_bounds (inputs : Fin 3 → Bits) (t : Term) (L : ℕ)
    (h : ∀ i, (inputs i).length ≤ L) :
    (evaluate inputs t).length ≤ width t*(L+1) ∧
    runSteps inputs t ≤ cost t*(L+1)^2 ∧ runCells inputs t ≤ cost t*(L+1)^2 := by
  have hX : 1 ≤ L+1 := by omega
  have hXX : L+1 ≤ (L+1)^2 := by nlinarith
  induction t with
  | input i =>
      simp only [evaluate,width,cost,runSteps,runCells,one_mul]
      exact ⟨by have := h i;omega,by nlinarith,by omega⟩
  | nil =>
      simp only [evaluate,width,cost,runSteps,runCells,List.length_nil,one_mul]
      exact ⟨Nat.zero_le _,by nlinarith,by nlinarith⟩
  | cons b t ih =>
      simp only [evaluate,width,cost,runSteps,runCells,List.length_cons]
      constructor
      · nlinarith [ih.1]
      · constructor <;> nlinarith [ih.2.1,ih.2.2]
  | binary m a b ha hb =>
      have hs := arithmetic_bounds m (evaluate inputs a) (evaluate inputs b)
      have hc : 100*((evaluate inputs a).length+1)*
          ((evaluate inputs a).length+(evaluate inputs b).length+2) ≤
          100*(width a+1)*(width a+width b+2)*(L+1)^2 := by
        calc
          _ ≤ 100*((width a+1)*(L+1))*((width a+width b+2)*(L+1)) := by
            gcongr <;> nlinarith [ha.1,hb.1]
          _ = _ := by ring
      change (arithmeticWord m (evaluate inputs a) (evaluate inputs b)).length ≤ _ ∧ _
      simp only [width,cost,runSteps,runCells]
      constructor
      · nlinarith [hs.1,ha.1,hb.1]
      · constructor <;> nlinarith [hs.2.1.trans hc,hs.2.2.trans hc,ha.2.1,ha.2.2,hb.2.1,hb.2.2]

/-- A static coefficient for the final binary-reference interpreter cost.
It includes the actual last halt, not just successful instructions. -/
def terminalCoefficient (C K : ℕ) : ℕ := (C+144)*(K*(2*K+3)^2+(K+2)^2)

theorem complete_polynomial (C H B t Z K : ℕ) (hZ : 1 ≤ Z)
    (hH : H ≤ Z) (hB : B ≤ Z) (ht : t ≤ K*Z^2) :
    completeBound C H B t ≤ terminalCoefficient C K*Z^6 := by
  have hZZ : Z ≤ Z^2 := by nlinarith
  have h1 : H+B+2*t+1 ≤ (2*K+3)*Z^2 := by nlinarith
  have h2 : H+t+1 ≤ (K+2)*Z^2 := by nlinarith
  have h3 : B+t+1 ≤ (K+2)*Z^2 := by nlinarith
  have h46 : Z^4 ≤ Z^6 := Nat.pow_le_pow_right hZ (by omega)
  unfold completeBound runBound stepBound controlCost
  calc
    _ ≤ (C+16+128)*(K*Z^2)*((2*K+3)*Z^2)^2+
        (C+16+128)*((K+2)*Z^2)*((K+2)*Z^2) := by gcongr
    _ = (C+144)*(K*(2*K+3)^2*Z^6+(K+2)^2*Z^4) := by ring
    _ ≤ terminalCoefficient C K*Z^6 := by
      unfold terminalCoefficient
      calc
        _ ≤ (C+144)*(K*(2*K+3)^2*Z^6+(K+2)^2*Z^6) := by gcongr
        _ = _ := by ring

theorem total_bound (inputs : Fin 3 → Bits) (t : Term) (L H B : ℕ)
    (h : ∀ i, (inputs i).length ≤ L) :
    completeBound (capacity t) H B (runSteps inputs t+1) ≤
      terminalCoefficient (capacity t) (cost t+1)*(H+B+L+1)^6 := by
  have hb := (evaluate_bounds inputs t L h).2.1
  have hp : 1 ≤ (L+1)^2 := Nat.one_le_pow _ _ (by omega)
  apply complete_polynomial <;> try omega
  calc
    runSteps inputs t+1 ≤ (cost t+1)*(L+1)^2 := by
      calc
        _ ≤ cost t*(L+1)^2+(L+1)^2 := Nat.add_le_add hb hp
        _ = _ := by ring
    _ ≤ (cost t+1)*(H+B+L+1)^2 := by gcongr;omega

end DirectedFlowCutGap.ConcreteExpressionBounds
