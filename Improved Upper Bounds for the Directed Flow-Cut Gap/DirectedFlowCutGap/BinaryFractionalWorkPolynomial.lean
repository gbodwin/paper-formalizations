import DirectedFlowCutGap.BinaryFractionalGuessesBounds

namespace DirectedFlowCutGap.BinaryFractionalWorkPolynomial

open Polynomial

private inductive Expression where
  | parameter (coordinate : Fin 3)
  | constant (n : ℕ)
  | add (left right : Expression)
  | mul (left right : Expression)
  | pow (base : Expression) (power : ℕ)

private instance (n : ℕ) : OfNat Expression n := ⟨.constant n⟩
private instance : Add Expression := ⟨Expression.add⟩
private instance : Mul Expression := ⟨Expression.mul⟩
private instance : Pow Expression ℕ := ⟨Expression.pow⟩

private def format (valuation : Fin 3 → ℕ) : Expression → ℕ
  | .parameter i => valuation i
  | .constant n => n
  | .add a b => format valuation a+format valuation b
  | .mul a b => format valuation a*format valuation b
  | .pow a k => (format valuation a)^k

private noncomputable def compile : Expression → Polynomial ℕ
  | .parameter _ => X
  | .constant n => C n
  | .add a b => compile a+compile b
  | .mul a b => compile a*compile b
  | .pow a k => (compile a)^k

private theorem compile_eval (e : Expression) (x : ℕ) :
    (compile e).eval x=format (fun _ => x) e := by
  induction e with
  | parameter i => simp only [compile,format,eval_X]
  | constant n => simp only [compile,format,eval_C]
  | add a b ha hb => simp only [compile,format,eval_add,ha,hb]
  | mul a b ha hb => simp only [compile,format,eval_mul,ha,hb]
  | pow a k ha => simp only [compile,format,eval_pow,ha]

private theorem eval_mono {u v : Fin 3 → ℕ} (h : ∀ i, u i≤v i) (e : Expression) :
    format u e≤format v e := by
  induction e with
  | parameter i => exact h i
  | constant n => exact le_rfl
  | add _ _ ha hb => exact Nat.add_le_add ha hb
  | mul _ _ ha hb => exact Nat.mul_le_mul ha hb
  | pow _ k ha => exact Nat.pow_le_pow_left ha k


private theorem formatAdd (v : Fin 3 → ℕ) (a b : Expression) :
    format v (a+b)=format v a+format v b := rfl

private theorem formatMul (v : Fin 3 → ℕ) (a b : Expression) :
    format v (a*b)=format v a*format v b := rfl

private theorem formatPow (v : Fin 3 → ℕ) (a : Expression) (b : ℕ) :
    format v (a^b)=(format v a)^b := rfl


private def widthListBoundExpr (m B : Expression) : Expression :=
  m*((.constant 128)*(B+(.constant 2))^2+(.constant 17)*(B+(.constant 2))+(.constant 10))+(.constant 1)

private theorem widthListBound_format (v : Fin 3 → ℕ) (m B : Expression) :
    format v (widthListBoundExpr m B)=BinaryFractionalGuessesBounds.widthListBound (format v m) (format v B) := by
  simp only [widthListBoundExpr,BinaryFractionalGuessesBounds.widthListBound,formatAdd, formatPow, format]

private def inputWidthBoundExpr (m B : Expression) : Expression :=
  widthListBoundExpr m B+(.constant 2)*m+(.constant 4)

private theorem inputWidthBound_format (v : Fin 3 → ℕ) (m B : Expression) :
    format v (inputWidthBoundExpr m B)=BinaryFractionalGuessesBounds.inputWidthBound (format v m) (format v B) := by
  simp only [inputWidthBoundExpr,BinaryFractionalGuessesBounds.inputWidthBound,formatAdd, format, widthListBound_format]

private def arrayBoundExpr (m : Expression) : Expression :=
  m^2+(.constant 15)*m+(.constant 2)

private theorem arrayBound_format (v : Fin 3 → ℕ) (m : Expression) :
    format v (arrayBoundExpr m)=EncodedRoundingInput.arrayBound (format v m) := by
  simp only [arrayBoundExpr,EncodedRoundingInput.arrayBound,formatAdd, formatPow, format]

private def keptAdjacencyBoundExpr (n : Expression) : Expression :=
  n*((.constant 52)*n+arrayBoundExpr n)+arrayBoundExpr n

private theorem keptAdjacencyBound_format (v : Fin 3 → ℕ) (n : Expression) :
    format v (keptAdjacencyBoundExpr n)=BinaryFractionalDispatchBounds.keptAdjacencyBound (format v n) := by
  simp only [keptAdjacencyBoundExpr,BinaryFractionalDispatchBounds.keptAdjacencyBound,formatAdd, format, arrayBound_format]

private def relaxBoundExpr (W B C : Expression) : Expression :=
  C+(.constant 4096)*(W+B+(.constant 3))^2+(.constant 64)

private theorem relaxBound_format (v : Fin 3 → ℕ) (W B C : Expression) :
    format v (relaxBoundExpr W B C)=BinaryFractionalWalkBounds.relaxBound (format v W) (format v B) (format v C) := by
  simp only [relaxBoundExpr,BinaryFractionalWalkBounds.relaxBound,formatAdd, formatPow, format]

private def passBoundExpr (N W B C : Expression) : Expression :=
  N*((N+(.constant 1))*relaxBoundExpr W B C+(.constant 17))+(.constant 1)

private theorem passBound_format (v : Fin 3 → ℕ) (N W B C : Expression) :
    format v (passBoundExpr N W B C)=BinaryFractionalWalkBounds.passBound (format v N) (format v W) (format v B) (format v C) := by
  simp only [passBoundExpr,BinaryFractionalWalkBounds.passBound,formatAdd, format, relaxBound_format]

private def roundsBoundExpr (N W B C K : Expression) : Expression :=
  K*(passBoundExpr N W B C+(.constant 6))+(.constant 8)

private theorem roundsBound_format (v : Fin 3 → ℕ) (N W B C K : Expression) :
    format v (roundsBoundExpr N W B C K)=BinaryFractionalWalkBounds.roundsBound (format v N) (format v W) (format v B) (format v C) (format v K) := by
  simp only [roundsBoundExpr,BinaryFractionalWalkBounds.roundsBound,formatAdd, format, passBound_format]

private def minimizeBoundExpr (N B C : Expression) : Expression :=
  roundsBoundExpr N (N*(B+(.constant 2))+(.constant 1)) B C N+(N+(.constant 1))*((.constant 2048)*(N*(B+(.constant 2))+(.constant 2))^2+(.constant 12))+(.constant 8)*N+(.constant 9)

private theorem minimizeBound_format (v : Fin 3 → ℕ) (N B C : Expression) :
    format v (minimizeBoundExpr N B C)=BinaryFractionalWalkBounds.minimizeBound (format v N) (format v B) (format v C) := by
  simp only [minimizeBoundExpr,BinaryFractionalWalkBounds.minimizeBound,formatAdd, formatPow, format, roundsBound_format]

private def visitBoundExpr (N C : Expression) : Expression :=
  N*(C+(.constant 32))+(.constant 32)

private theorem visitBound_format (v : Fin 3 → ℕ) (N C : Expression) :
    format v (visitBoundExpr N C)=IntegralNetworkFlow.Tabulated.RetainedPathSearch.visitBound (format v N) (format v C) := by
  simp only [visitBoundExpr,IntegralNetworkFlow.Tabulated.RetainedPathSearch.visitBound,formatAdd, format]

private def searchBoundExpr (N C : Expression) : Expression :=
  N*(N*(visitBoundExpr N C+(.constant 4))+(.constant 5))+(.constant 25)*N+(.constant 37)

private theorem searchBound_format (v : Fin 3 → ℕ) (N C : Expression) :
    format v (searchBoundExpr N C)=IntegralNetworkFlow.Tabulated.RetainedPathSearch.searchBound (format v N) (format v C) := by
  simp only [searchBoundExpr,IntegralNetworkFlow.Tabulated.RetainedPathSearch.searchBound,formatAdd, format, visitBound_format]

private def sumBoundExpr (n B : Expression) : Expression :=
  n*((.constant 2048)*((n+(.constant 1))*(B+(.constant 1))+(.constant 1))^2+(.constant 4))+(.constant 1)

private theorem sumBound_format (v : Fin 3 → ℕ) (n B : Expression) :
    format v (sumBoundExpr n B)=BinaryFractionalRows.sumBound (format v n) (format v B) := by
  simp only [sumBoundExpr,BinaryFractionalRows.sumBound,formatAdd, formatPow, format]

private def recoverBoundExpr (n L B C : Expression) : Expression :=
  searchBoundExpr n ((.constant 8)*L+(.constant 27))+n*(C+(.constant 6))+sumBoundExpr n B+(.constant 9)

private theorem recoverBound_format (v : Fin 3 → ℕ) (n L B C : Expression) :
    format v (recoverBoundExpr n L B C)=BinaryFractionalWalkBounds.recoverBound (format v n) (format v L) (format v B) (format v C) := by
  simp only [recoverBoundExpr,BinaryFractionalWalkBounds.recoverBound,formatAdd, format, searchBound_format, sumBound_format]

private def shortestBoundExpr (n B C : Expression) : Expression :=
  minimizeBoundExpr n B C+recoverBoundExpr n n B C+(.constant 6)

private theorem shortestBound_format (v : Fin 3 → ℕ) (n B C : Expression) :
    format v (shortestBoundExpr n B C)=BinaryFractionalWalkBounds.shortestBound (format v n) (format v B) (format v C) := by
  simp only [shortestBoundExpr,BinaryFractionalWalkBounds.shortestBound,formatAdd, format, minimizeBound_format, recoverBound_format]

private def findAvoidingBoundExpr (n D : Expression) : Expression :=
  D*(keptAdjacencyBoundExpr n+shortestBoundExpr n (.constant 1) (.constant 1)+(.constant 8))+(.constant 1)

private theorem findAvoidingBound_format (v : Fin 3 → ℕ) (n D : Expression) :
    format v (findAvoidingBoundExpr n D)=BinaryFractionalDispatchBounds.findAvoidingBound (format v n) (format v D) := by
  simp only [findAvoidingBoundExpr,BinaryFractionalDispatchBounds.findAvoidingBound,formatAdd, format, keptAdjacencyBound_format, shortestBound_format]

private def zeroMaskBoundExpr (m B : Expression) : Expression :=
  m*((.constant 4)*(B+(.constant 1))+(.constant 11))+arrayBoundExpr m

private theorem zeroMaskBound_format (v : Fin 3 → ℕ) (m B : Expression) :
    format v (zeroMaskBoundExpr m B)=BinaryFractionalDispatchBounds.zeroMaskBound (format v m) (format v B) := by
  simp only [zeroMaskBoundExpr,BinaryFractionalDispatchBounds.zeroMaskBound,formatAdd, format, arrayBound_format]

private def dispatchBoundExpr (n D B : Expression) : Expression :=
  (.constant 26)*D+zeroMaskBoundExpr n B+findAvoidingBoundExpr n D+(.constant 9)

private theorem dispatchBound_format (v : Fin 3 → ℕ) (n D B : Expression) :
    format v (dispatchBoundExpr n D B)=BinaryFractionalDispatchBounds.dispatchBound (format v n) (format v D) (format v B) := by
  simp only [dispatchBoundExpr,BinaryFractionalDispatchBounds.dispatchBound,formatAdd, format, findAvoidingBound_format, zeroMaskBound_format]

private def lambdaWidthExpr (n B K : Expression) : Expression :=
  B+n+K+(.constant 4)

private theorem lambdaWidth_format (v : Fin 3 → ℕ) (n B K : Expression) :
    format v (lambdaWidthExpr n B K)=BinaryFractionalGuessesBounds.lambdaWidth (format v n) (format v B) (format v K) := by
  simp only [lambdaWidthExpr,BinaryFractionalGuessesBounds.lambdaWidth,formatAdd, format]

private def lambdaBoundExpr (n B K E : Expression) : Expression :=
  (.constant 4096)*(lambdaWidthExpr n B K+(.constant 1))^2+(.constant 64)*(K+(.constant 1))*(E+(.constant 1))+(.constant 19)

private theorem lambdaBound_format (v : Fin 3 → ℕ) (n B K E : Expression) :
    format v (lambdaBoundExpr n B K E)=BinaryFractionalGuessesBounds.lambdaBound (format v n) (format v B) (format v K) (format v E) := by
  simp only [lambdaBoundExpr,BinaryFractionalGuessesBounds.lambdaBound,formatAdd, formatPow, format, lambdaWidth_format]

private def shiftedBoundExpr (n B K : Expression) : Expression :=
  n*((.constant 2048)*(lambdaWidthExpr n B K+(.constant 1))^2+(.constant 11))+arrayBoundExpr n

private theorem shiftedBound_format (v : Fin 3 → ℕ) (n B K : Expression) :
    format v (shiftedBoundExpr n B K)=BinaryFractionalGuessesBounds.shiftedBound (format v n) (format v B) (format v K) := by
  simp only [shiftedBoundExpr,BinaryFractionalGuessesBounds.shiftedBound,formatAdd, formatPow, format, arrayBound_format, lambdaWidth_format]

private def shiftedWidthExpr (n B K : Expression) : Expression :=
  B+lambdaWidthExpr n B K+(.constant 2)

private theorem shiftedWidth_format (v : Fin 3 → ℕ) (n B K : Expression) :
    format v (shiftedWidthExpr n B K)=BinaryFractionalGuessesBounds.shiftedWidth (format v n) (format v B) (format v K) := by
  simp only [shiftedWidthExpr,BinaryFractionalGuessesBounds.shiftedWidth,formatAdd, format, lambdaWidth_format]

private def stateWidthExpr (m B k : Expression) : Expression :=
  (m+(.constant 1))^2*(B+(.constant 2)*m+(.constant 4)+k*((.constant 2)*B+(.constant 2)))+k*(B+(.constant 1))+B+(.constant 2)

private theorem stateWidth_format (v : Fin 3 → ℕ) (m B k : Expression) :
    format v (stateWidthExpr m B k)=BinaryFractionalWidths.stateWidth (format v m) (format v B) (format v k) := by
  simp only [stateWidthExpr,BinaryFractionalWidths.stateWidth,formatAdd, formatPow, format]

private def loadsBoundExpr (m B : Expression) : Expression :=
  m*((.constant 2048)*(B+(.constant 2))^2+(.constant 5))+arrayBoundExpr m

private theorem loadsBound_format (v : Fin 3 → ℕ) (m B : Expression) :
    format v (loadsBoundExpr m B)=BinaryFractionalStepCost.loadsBound (format v m) (format v B) := by
  simp only [loadsBoundExpr,BinaryFractionalStepCost.loadsBound,formatAdd, formatPow, format, arrayBound_format]

private def lengthBoundExpr (m B : Expression) : Expression :=
  (.constant 5)*m+arrayBoundExpr m+sumBoundExpr m (B+(.constant 1))+(.constant 2)*m+(.constant 4)

private theorem lengthBound_format (v : Fin 3 → ℕ) (m B : Expression) :
    format v (lengthBoundExpr m B)=BinaryFractionalRows.lengthBound (format v m) (format v B) := by
  simp only [lengthBoundExpr,BinaryFractionalRows.lengthBound,formatAdd, format, arrayBound_format, sumBound_format]

private def normalizedBoundExpr (m B : Expression) : Expression :=
  lengthBoundExpr m B+m*((.constant 2048)*((m+(.constant 1))*(B+(.constant 1))+(.constant 2))^2+(.constant 4))+arrayBoundExpr m+(.constant 4)

private theorem normalizedBound_format (v : Fin 3 → ℕ) (m B : Expression) :
    format v (normalizedBoundExpr m B)=BinaryFractionalRows.normalizedBound (format v m) (format v B) := by
  simp only [normalizedBoundExpr,BinaryFractionalRows.normalizedBound,formatAdd, formatPow, format, arrayBound_format, lengthBound_format]

private def objectiveBoundExpr (m B : Expression) : Expression :=
  m*((.constant 2048)*(B+(.constant 1))^2+(.constant 6))+arrayBoundExpr m+sumBoundExpr m ((.constant 2)*B+(.constant 1))+(.constant 2)*m+(.constant 4)

private theorem objectiveBound_format (v : Fin 3 → ℕ) (m B : Expression) :
    format v (objectiveBoundExpr m B)=BinaryFractionalRows.objectiveBound (format v m) (format v B) := by
  simp only [objectiveBoundExpr,BinaryFractionalRows.objectiveBound,formatAdd, formatPow, format, arrayBound_format, sumBound_format]

private def scalarWidthExpr (m B : Expression) : Expression :=
  (m+(.constant 1))^2*((.constant 4)*B+(.constant 8))

private theorem scalarWidth_format (v : Fin 3 → ℕ) (m B : Expression) :
    format v (scalarWidthExpr m B)=BinaryFractionalStepCost.scalarWidth (format v m) (format v B) := by
  simp only [scalarWidthExpr,BinaryFractionalStepCost.scalarWidth, formatMul, formatPow, format]

private def factorBoundExpr (B : Expression) : Expression :=
  (.constant 6144)*((.constant 2)*B+(.constant 3))^2+(.constant 12)

private theorem factorBound_format (v : Fin 3 → ℕ) (B : Expression) :
    format v (factorBoundExpr B)=BinaryFractionalRows.factorBound (format v B) := by
  simp only [factorBoundExpr,BinaryFractionalRows.factorBound,formatAdd, formatPow, format]

private def updateBoundExpr (m B : Expression) : Expression :=
  m*(factorBoundExpr B+(.constant 2048)*((.constant 2)*B+(.constant 4))^2+(.constant 8))+arrayBoundExpr m

private theorem updateBound_format (v : Fin 3 → ℕ) (m B : Expression) :
    format v (updateBoundExpr m B)=BinaryFractionalStepCost.updateBound (format v m) (format v B) := by
  simp only [updateBoundExpr,BinaryFractionalStepCost.updateBound,formatAdd, formatPow, format, arrayBound_format, factorBound_format]

private def stepBoundExpr (m B R : Expression) : Expression :=
  objectiveBoundExpr m B + (.constant 4096)*(scalarWidthExpr m B+(.constant 1))^2 + R + normalizedBoundExpr m B + objectiveBoundExpr m ((m+(.constant 1))*(B+(.constant 1))+(.constant 1)) + updateBoundExpr m B + (.constant 2048)*(B+(.constant 1))^2 + loadsBoundExpr m B + (.constant 28)

private theorem stepBound_format (v : Fin 3 → ℕ) (m B R : Expression) :
    format v (stepBoundExpr m B R)=BinaryFractionalStepCost.stepBound (format v m) (format v B) (format v R) := by
  simp only [stepBoundExpr,BinaryFractionalStepCost.stepBound,formatAdd, formatPow, format, loadsBound_format, normalizedBound_format, objectiveBound_format, scalarWidth_format, updateBound_format]

private def loopBoundExpr (m B T R F t : Expression) : Expression :=
  t*(stepBoundExpr m (stateWidthExpr m B T) R+(.constant 36)*(F+(.constant 1))+(.constant 8))+(.constant 4)*(F+(.constant 1))+(.constant 4)

private theorem loopBound_format (v : Fin 3 → ℕ) (m B T R F t : Expression) :
    format v (loopBoundExpr m B T R F t)=BinaryFractionalLoopCost.loopBound (format v m) (format v B) (format v T) (format v R) (format v F) (format v t) := by
  simp only [loopBoundExpr,BinaryFractionalLoopCost.loopBound,formatAdd, format, stateWidth_format, stepBound_format]

private def parameterBoundExpr (D : Expression) : Expression :=
  (.constant 4096)*((.constant 3)*D+(.constant 7))^2

private theorem parameterBound_format (v : Fin 3 → ℕ) (D : Expression) :
    format v (parameterBoundExpr D)=BinaryFractionalEntryCost.parameterBound (format v D) := by
  simp only [parameterBoundExpr,BinaryFractionalEntryCost.parameterBound, formatMul, formatPow, format]

private def startBoundExpr (m B T R : Expression) : Expression :=
  m*((.constant 2048)*(B+(.constant 2)*m+(.constant 5))^2+(.constant 4))+arrayBoundExpr m+R+ normalizedBoundExpr m (stateWidthExpr m B T)+objectiveBoundExpr m (stateWidthExpr m B T)+(.constant 2)*m+(.constant 16)

private theorem startBound_format (v : Fin 3 → ℕ) (m B T R : Expression) :
    format v (startBoundExpr m B T R)=BinaryFractionalEntryCost.startBound (format v m) (format v B) (format v T) (format v R) := by
  simp only [startBoundExpr,BinaryFractionalEntryCost.startBound,formatAdd, formatPow, format, arrayBound_format, normalizedBound_format, objectiveBound_format, stateWidth_format]

private def entryBoundExpr (m B R : Expression) : Expression :=
  (.constant 32)*(m+(.constant 1))^2+parameterBoundExpr (m+(.constant 1))+startBoundExpr m B ((.constant 3)*m^2) R+ loopBoundExpr m B ((.constant 3)*m^2) R ((.constant 3)*m+(.constant 9)) ((.constant 3)*m^2)+(.constant 12)

private theorem entryBound_format (v : Fin 3 → ℕ) (m B R : Expression) :
    format v (entryBoundExpr m B R)=BinaryFractionalEntryCost.entryBound (format v m) (format v B) (format v R) := by
  simp only [entryBoundExpr,BinaryFractionalEntryCost.entryBound,formatAdd, formatPow, format, loopBound_format, parameterBound_format, startBound_format]

private def argminBoundExpr (N B C : Expression) : Expression :=
  N*((.constant 2)*C+(.constant 2048)*(B+(.constant 1))^2+(.constant 12))+(.constant 1)

private theorem argminBound_format (v : Fin 3 → ℕ) (N B C : Expression) :
    format v (argminBoundExpr N B C)=BinaryFractionalGraphBounds.argminBound (format v N) (format v B) (format v C) := by
  simp only [argminBoundExpr,BinaryFractionalGraphBounds.argminBound,formatAdd, formatPow, format]

private def bottleneckBoundExpr (m B : Expression) : Expression :=
  (.constant 16)*m+argminBoundExpr m B (.constant 7)+(.constant 5)

private theorem bottleneckBound_format (v : Fin 3 → ℕ) (m B : Expression) :
    format v (bottleneckBoundExpr m B)=BinaryFractionalGraphBounds.bottleneckBound (format v m) (format v B) := by
  simp only [bottleneckBoundExpr,BinaryFractionalGraphBounds.bottleneckBound,formatAdd, format, argminBound_format]

private def maskBoundExpr (n L : Expression) : Expression :=
  n*((.constant 6)*L+(.constant 9))+arrayBoundExpr n

private theorem maskBound_format (v : Fin 3 → ℕ) (n L : Expression) :
    format v (maskBoundExpr n L)=BinaryFractionalGraphBounds.maskBound (format v n) (format v L) := by
  simp only [maskBoundExpr,BinaryFractionalGraphBounds.maskBound,formatAdd, format, arrayBound_format]

private def collectBoundExpr (n D B : Expression) : Expression :=
  D*(shortestBoundExpr n (B+(.constant 1)) (.constant 13)+(.constant 10))+(.constant 1)

private theorem collectBound_format (v : Fin 3 → ℕ) (n D B : Expression) :
    format v (collectBoundExpr n D B)=BinaryFractionalGraphBounds.collectBound (format v n) (format v D) (format v B) := by
  simp only [collectBoundExpr,BinaryFractionalGraphBounds.collectBound,formatAdd, format, shortestBound_format]

private def selectedBoundExpr (n D B : Expression) : Expression :=
  collectBoundExpr n D B+argminBoundExpr D (n*(B+(.constant 2))+(.constant 1)) (.constant 4)+(.constant 4)

private theorem selectedBound_format (v : Fin 3 → ℕ) (n D B : Expression) :
    format v (selectedBoundExpr n D B)=BinaryFractionalGraphBounds.selectedBound (format v n) (format v D) (format v B) := by
  simp only [selectedBoundExpr,BinaryFractionalGraphBounds.selectedBound,formatAdd, format, argminBound_format, collectBound_format]

private def oracleBoundExpr (n D capacityWidth weightWidth : Expression) : Expression :=
  selectedBoundExpr n D weightWidth+maskBoundExpr n n+bottleneckBoundExpr n capacityWidth+(.constant 8)

private theorem oracleBound_format (v : Fin 3 → ℕ) (n D capacityWidth weightWidth : Expression) :
    format v (oracleBoundExpr n D capacityWidth weightWidth)=BinaryFractionalGraphBounds.oracleBound (format v n) (format v D) (format v capacityWidth) (format v weightWidth) := by
  simp only [oracleBoundExpr,BinaryFractionalGraphBounds.oracleBound,formatAdd, format, bottleneckBound_format, maskBound_format, selectedBound_format]

private def solveGraphBoundExpr (n D B : Expression) : Expression :=
  entryBoundExpr n B (oracleBoundExpr n D B (stateWidthExpr n B ((.constant 3)*n^2)))

private theorem solveGraphBound_format (v : Fin 3 → ℕ) (n D B : Expression) :
    format v (solveGraphBoundExpr n D B)=BinaryFractionalGraphCost.solveGraphBound (format v n) (format v D) (format v B) := by
  simp only [solveGraphBoundExpr,BinaryFractionalGraphCost.solveGraphBound, formatPow, format, entryBound_format, oracleBound_format, stateWidth_format]

private def guessBoundExpr (n D B K E : Expression) : Expression :=
  lambdaBoundExpr n B K E+shiftedBoundExpr n B K+solveGraphBoundExpr n D (shiftedWidthExpr n B K)+(.constant 8)

private theorem guessBound_format (v : Fin 3 → ℕ) (n D B K E : Expression) :
    format v (guessBoundExpr n D B K E)=BinaryFractionalGuessesBounds.guessBound (format v n) (format v D) (format v B) (format v K) (format v E) := by
  simp only [guessBoundExpr,BinaryFractionalGuessesBounds.guessBound,formatAdd, format, lambdaBound_format, shiftedBound_format, shiftedWidth_format, solveGraphBound_format]

private def familyBoundExpr (n D B K E F T : Expression) : Expression :=
  T*(guessBoundExpr n D B K E+(.constant 8)*(E+(.constant 1))+(.constant 36)*(F+(.constant 1))+(.constant 12))+(.constant 4)*(F+(.constant 1))+(.constant 4)

private theorem familyBound_format (v : Fin 3 → ℕ) (n D B K E F T : Expression) :
    format v (familyBoundExpr n D B K E F T)=BinaryFractionalGuessesBounds.familyBound (format v n) (format v D) (format v B) (format v K) (format v E) (format v F) (format v T) := by
  simp only [familyBoundExpr,BinaryFractionalGuessesBounds.familyBound,formatAdd, format, guessBound_format]

private def gridBoundExpr (n B : Expression) : Expression :=
  (.constant 2)*B+(.constant 2)*n+(.constant 4)

private theorem gridBound_format (v : Fin 3 → ℕ) (n B : Expression) :
    format v (gridBoundExpr n B)=BinaryFractionalGuessesBounds.gridBound (format v n) (format v B) := by
  simp only [gridBoundExpr,BinaryFractionalGuessesBounds.gridBound,formatAdd, format]

private def gridChargeExpr (n B : Expression) : Expression :=
  (.constant 4096)*(gridBoundExpr n B+(.constant 2))^2

private theorem gridCharge_format (v : Fin 3 → ℕ) (n B : Expression) :
    format v (gridChargeExpr n B)=BinaryFractionalGuessesBounds.gridCharge (format v n) (format v B) := by
  simp only [gridChargeExpr,BinaryFractionalGuessesBounds.gridCharge, formatMul, formatPow, format, gridBound_format]

private def guessesBoundExpr (n D B : Expression) : Expression :=
  (.constant 32)*(n+(.constant 1))^2+gridChargeExpr n B+ familyBoundExpr n D B (gridBoundExpr n B) (gridBoundExpr n B) (gridBoundExpr n B) (gridBoundExpr n B)+(.constant 8)

private theorem guessesBound_format (v : Fin 3 → ℕ) (n D B : Expression) :
    format v (guessesBoundExpr n D B)=BinaryFractionalGuessesBounds.guessesBound (format v n) (format v D) (format v B) := by
  simp only [guessesBoundExpr,BinaryFractionalGuessesBounds.guessesBound,formatAdd, formatPow, format, familyBound_format, gridBound_format, gridCharge_format]

private def minimumPositiveBoundExpr (m B : Expression) : Expression :=
  m*((.constant 4)*(B+(.constant 1))+(.constant 23))+argminBoundExpr m B (.constant 7)+(.constant 5)

private theorem minimumPositiveBound_format (v : Fin 3 → ℕ) (m B : Expression) :
    format v (minimumPositiveBoundExpr m B)=BinaryFractionalDispatchBounds.minimumPositiveBound (format v m) (format v B) := by
  simp only [minimumPositiveBoundExpr,BinaryFractionalDispatchBounds.minimumPositiveBound,formatAdd, format, argminBound_format]

private def runBoundExpr (n D B : Expression) : Expression :=
  dispatchBoundExpr n D B+minimumPositiveBoundExpr n B+guessesBoundExpr n D B+(.constant 8)

private theorem runBound_format (v : Fin 3 → ℕ) (n D B : Expression) :
    format v (runBoundExpr n D B)=BinaryFractionalGuessesBounds.runBound (format v n) (format v D) (format v B) := by
  simp only [runBoundExpr,BinaryFractionalGuessesBounds.runBound,formatAdd, format, dispatchBound_format, guessesBound_format, minimumPositiveBound_format]

private def solveInputBoundExpr (n D B : Expression) : Expression :=
  inputWidthBoundExpr n B+runBoundExpr n D B+(.constant 12)

private theorem solveInputBound_format (v : Fin 3 → ℕ) (n D B : Expression) :
    format v (solveInputBoundExpr n D B)=BinaryFractionalGuessesBounds.solveInputBound (format v n) (format v D) (format v B) := by
  simp only [solveInputBoundExpr,BinaryFractionalGuessesBounds.solveInputBound,formatAdd, format, inputWidthBound_format, runBound_format]

private def expression : Expression := solveInputBoundExpr (.parameter 0) (.parameter 1) (.parameter 2)

private theorem expression_value (n d b : ℕ) :
    format ![n,d,b] expression=BinaryFractionalGuessesBounds.solveInputBound n d b := by
  rw [expression,solveInputBound_format]
  rfl

noncomputable def envelope : Polynomial ℕ := compile expression

theorem bound {n d b x : ℕ} (hn : n≤x) (hd : d≤x) (hb : b≤x) :
    BinaryFractionalGuessesBounds.solveInputBound n d b≤envelope.eval x := by
  rw [← expression_value, envelope, compile_eval]
  apply eval_mono _ expression
  intro i
  fin_cases i
  · exact hn
  · exact hd
  · exact hb

end DirectedFlowCutGap.BinaryFractionalWorkPolynomial
