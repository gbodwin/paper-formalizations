import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact transition count for sums of products of framed unary operands. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private inductive UnaryProductLabel where
  | readLeft
  | readRight
  | consumeLeft
  | copyRight
  | restoreRight
  | clearRight
  deriving DecidableEq

private instance : Fintype UnaryProductLabel where
  elems := {.readLeft,.readRight,.consumeLeft,.copyRight,.restoreRight,.clearRight}
  complete := by intro label; cases label <;> simp

private abbrev UnaryProductRegister := Option Bool
private abbrev UnaryProductProgram :=
  Turing.TM2.Stmt (fun _ : Fin 5 => Bool) UnaryProductLabel UnaryProductRegister

private def unaryProductObserve (_ : UnaryProductRegister) (symbol : Option Bool) : UnaryProductRegister := symbol

private def unaryProductNext (label : UnaryProductLabel) : UnaryProductProgram :=
  load (fun _ => none) (goto (fun _ => label))

private def unaryProductProgram : UnaryProductLabel → UnaryProductProgram
  | .readLeft =>
    pop 0 unaryProductObserve <|
      branch Option.isSome
        (branch (·.getD false)
          (push 1 (fun _ => true) (unaryProductNext .readLeft))
          (unaryProductNext .readRight))
        (load (fun _ => none) halt)
  | .readRight =>
    pop 0 unaryProductObserve <|
      branch (·.getD false)
        (push 2 (fun _ => true) (unaryProductNext .readRight))
        (unaryProductNext .consumeLeft)
  | .consumeLeft =>
    pop 1 unaryProductObserve <|
      branch Option.isSome (unaryProductNext .copyRight) (unaryProductNext .clearRight)
  | .copyRight =>
    pop 2 unaryProductObserve <|
      branch Option.isSome
        (push 3 (fun _ => true) (push 4 (fun _ => true) (unaryProductNext .copyRight)))
        (unaryProductNext .restoreRight)
  | .restoreRight =>
    pop 3 unaryProductObserve <|
      branch Option.isSome (push 2 (fun _ => true) (unaryProductNext .restoreRight))
        (unaryProductNext .consumeLeft)
  | .clearRight =>
    pop 2 unaryProductObserve <|
      branch Option.isSome (unaryProductNext .clearRight) (unaryProductNext .readLeft)

/-- Read delimited unary operand pairs and sum their products. For each
left tally, move the right tallies to a temporary stack and copy them
to the answer. Restore the right stack before the next left tally. -/
abbrev steinerUnaryProductMachine : FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 4
  Γ _ := Bool
  Λ := UnaryProductLabel
  main := .readLeft
  σ := UnaryProductRegister
  initialState := none
  m := unaryProductProgram

private abbrev tallies (a : ℕ) := List.replicate a true

private def unaryProductCfg (label : Option UnaryProductLabel) (input : List Bool)
    (left right temporary answer : ℕ) : steinerUnaryProductMachine.Cfg where
  l := label
  var := none
  stk := ![input,tallies left,tallies right,tallies temporary,tallies answer]

private theorem unaryProduct_update0 (w x y z a b : List Bool) :
    Function.update (![w,x,y,z,a] : Fin 5 → List Bool) 0 b = ![b,x,y,z,a] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem unaryProduct_update1 (w x y z a b : List Bool) :
    Function.update (![w,x,y,z,a] : Fin 5 → List Bool) 1 b = ![w,b,y,z,a] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem unaryProduct_update2 (w x y z a b : List Bool) :
    Function.update (![w,x,y,z,a] : Fin 5 → List Bool) 2 b = ![w,x,b,z,a] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem unaryProduct_update3 (w x y z a b : List Bool) :
    Function.update (![w,x,y,z,a] : Fin 5 → List Bool) 3 b = ![w,x,y,b,a] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem unaryProduct_update4 (w x y z a b : List Bool) :
    Function.update (![w,x,y,z,a] : Fin 5 → List Bool) 4 b = ![w,x,y,z,b] := by
  funext i
  fin_cases i <;> simp [Function.update]

private abbrev UnaryProductRun (start finish : steinerUnaryProductMachine.Cfg) (steps : ℕ) : Prop :=
  (flip bind steinerUnaryProductMachine.step)^[steps] (some start) = some finish

private theorem unaryProduct_one {start finish : steinerUnaryProductMachine.Cfg}
    (move : steinerUnaryProductMachine.step start = some finish) : UnaryProductRun start finish 1 := move

private theorem unaryProduct_join {start between finish : steinerUnaryProductMachine.Cfg} {a b : ℕ}
    (first : UnaryProductRun start between a) (second : UnaryProductRun between finish b) :
    UnaryProductRun start finish (a+b) := by
  unfold UnaryProductRun at *
  rw [Nat.add_comm a b,Function.iterate_add_apply,first]
  exact second

private theorem unaryProduct_leftSymbol (tail : List Bool) (left answer : ℕ) :
    UnaryProductRun (unaryProductCfg (some .readLeft) (true::tail) left 0 0 answer)
      (unaryProductCfg (some .readLeft) tail (left+1) 0 0 answer) 1 := by
  apply unaryProduct_one
  simp [FinTM2.step,steinerUnaryProductMachine,unaryProductCfg,Turing.TM2.step,Turing.TM2.stepAux,
    unaryProductProgram,unaryProductObserve,unaryProductNext,unaryProduct_update0,unaryProduct_update1,List.replicate_succ]
  rfl

private theorem unaryProduct_leftDivider (tail : List Bool) (left answer : ℕ) :
    UnaryProductRun (unaryProductCfg (some .readLeft) (false::tail) left 0 0 answer)
      (unaryProductCfg (some .readRight) tail left 0 0 answer) 1 := by
  apply unaryProduct_one
  simp [FinTM2.step,steinerUnaryProductMachine,unaryProductCfg,Turing.TM2.step,Turing.TM2.stepAux,
    unaryProductProgram,unaryProductObserve,unaryProductNext,unaryProduct_update0]
  rfl

private theorem unaryProduct_leftEnd (answer : ℕ) :
    UnaryProductRun (unaryProductCfg (some .readLeft) [] 0 0 0 answer)
      (unaryProductCfg none [] 0 0 0 answer) 1 := by
  apply unaryProduct_one
  simp [FinTM2.step,steinerUnaryProductMachine,unaryProductCfg,Turing.TM2.step,Turing.TM2.stepAux,
    unaryProductProgram,unaryProductObserve,unaryProduct_update0]
  rfl

private theorem unaryProduct_rightSymbol (tail : List Bool) (left right answer : ℕ) :
    UnaryProductRun (unaryProductCfg (some .readRight) (true::tail) left right 0 answer)
      (unaryProductCfg (some .readRight) tail left (right+1) 0 answer) 1 := by
  apply unaryProduct_one
  simp [FinTM2.step,steinerUnaryProductMachine,unaryProductCfg,Turing.TM2.step,Turing.TM2.stepAux,
    unaryProductProgram,unaryProductObserve,unaryProductNext,unaryProduct_update0,unaryProduct_update2,List.replicate_succ]
  rfl

private theorem unaryProduct_rightDivider (tail : List Bool) (left right answer : ℕ) :
    UnaryProductRun (unaryProductCfg (some .readRight) (false::tail) left right 0 answer)
      (unaryProductCfg (some .consumeLeft) tail left right 0 answer) 1 := by
  apply unaryProduct_one
  simp [FinTM2.step,steinerUnaryProductMachine,unaryProductCfg,Turing.TM2.step,Turing.TM2.stepAux,
    unaryProductProgram,unaryProductObserve,unaryProductNext,unaryProduct_update0]
  rfl

private theorem unaryProduct_consumeTally (tail : List Bool) (left right answer : ℕ) :
    UnaryProductRun (unaryProductCfg (some .consumeLeft) tail (left+1) right 0 answer)
      (unaryProductCfg (some .copyRight) tail left right 0 answer) 1 := by
  apply unaryProduct_one
  simp [FinTM2.step,steinerUnaryProductMachine,unaryProductCfg,Turing.TM2.step,Turing.TM2.stepAux,
    unaryProductProgram,unaryProductObserve,unaryProductNext,unaryProduct_update1,List.replicate_succ]
  rfl

private theorem unaryProduct_consumeEnd (tail : List Bool) (right answer : ℕ) :
    UnaryProductRun (unaryProductCfg (some .consumeLeft) tail 0 right 0 answer)
      (unaryProductCfg (some .clearRight) tail 0 right 0 answer) 1 := by
  apply unaryProduct_one
  simp [FinTM2.step,steinerUnaryProductMachine,unaryProductCfg,Turing.TM2.step,Turing.TM2.stepAux,
    unaryProductProgram,unaryProductObserve,unaryProductNext,unaryProduct_update1]
  rfl

private theorem unaryProduct_copyTally (tail : List Bool) (left right temporary answer : ℕ) :
    UnaryProductRun (unaryProductCfg (some .copyRight) tail left (right+1) temporary answer)
      (unaryProductCfg (some .copyRight) tail left right (temporary+1) (answer+1)) 1 := by
  apply unaryProduct_one
  simp [FinTM2.step,steinerUnaryProductMachine,unaryProductCfg,Turing.TM2.step,Turing.TM2.stepAux,
    unaryProductProgram,unaryProductObserve,unaryProductNext,unaryProduct_update2,unaryProduct_update3,
    unaryProduct_update4,List.replicate_succ]
  rfl

private theorem unaryProduct_copyEnd (tail : List Bool) (left temporary answer : ℕ) :
    UnaryProductRun (unaryProductCfg (some .copyRight) tail left 0 temporary answer)
      (unaryProductCfg (some .restoreRight) tail left 0 temporary answer) 1 := by
  apply unaryProduct_one
  simp [FinTM2.step,steinerUnaryProductMachine,unaryProductCfg,Turing.TM2.step,Turing.TM2.stepAux,
    unaryProductProgram,unaryProductObserve,unaryProductNext,unaryProduct_update2]
  rfl

private theorem unaryProduct_restoreTally (tail : List Bool) (left right temporary answer : ℕ) :
    UnaryProductRun (unaryProductCfg (some .restoreRight) tail left right (temporary+1) answer)
      (unaryProductCfg (some .restoreRight) tail left (right+1) temporary answer) 1 := by
  apply unaryProduct_one
  simp [FinTM2.step,steinerUnaryProductMachine,unaryProductCfg,Turing.TM2.step,Turing.TM2.stepAux,
    unaryProductProgram,unaryProductObserve,unaryProductNext,unaryProduct_update2,unaryProduct_update3,List.replicate_succ]
  rfl

private theorem unaryProduct_restoreEnd (tail : List Bool) (left right answer : ℕ) :
    UnaryProductRun (unaryProductCfg (some .restoreRight) tail left right 0 answer)
      (unaryProductCfg (some .consumeLeft) tail left right 0 answer) 1 := by
  apply unaryProduct_one
  simp [FinTM2.step,steinerUnaryProductMachine,unaryProductCfg,Turing.TM2.step,Turing.TM2.stepAux,
    unaryProductProgram,unaryProductObserve,unaryProductNext,unaryProduct_update3]
  rfl

private theorem unaryProduct_clearTally (tail : List Bool) (right answer : ℕ) :
    UnaryProductRun (unaryProductCfg (some .clearRight) tail 0 (right+1) 0 answer)
      (unaryProductCfg (some .clearRight) tail 0 right 0 answer) 1 := by
  apply unaryProduct_one
  simp [FinTM2.step,steinerUnaryProductMachine,unaryProductCfg,Turing.TM2.step,Turing.TM2.stepAux,
    unaryProductProgram,unaryProductObserve,unaryProductNext,unaryProduct_update2,List.replicate_succ]
  rfl

private theorem unaryProduct_clearEnd (tail : List Bool) (answer : ℕ) :
    UnaryProductRun (unaryProductCfg (some .clearRight) tail 0 0 0 answer)
      (unaryProductCfg (some .readLeft) tail 0 0 0 answer) 1 := by
  apply unaryProduct_one
  simp [FinTM2.step,steinerUnaryProductMachine,unaryProductCfg,Turing.TM2.step,Turing.TM2.stepAux,
    unaryProductProgram,unaryProductObserve,unaryProductNext,unaryProduct_update2]
  rfl

private theorem unaryProduct_readLeft (tail : List Bool) (remaining loaded answer : ℕ) :
    UnaryProductRun (unaryProductCfg (some .readLeft) (tallies remaining++false::tail) loaded 0 0 answer)
      (unaryProductCfg (some .readRight) tail (loaded+remaining) 0 0 answer) (remaining+1) := by
  induction remaining generalizing loaded with
  | zero =>
    simpa only [Nat.add_zero,Nat.zero_add,List.replicate_zero,List.nil_append] using unaryProduct_leftDivider tail loaded answer
  | succ remaining ih =>
    have first := unaryProduct_leftSymbol (tallies remaining++false::tail) loaded answer
    have all := unaryProduct_join first (ih (loaded+1))
    have loadCount : loaded+1+remaining = loaded+(remaining+1) := by omega
    have stepCount : 1+(remaining+1) = remaining+1+1 := by omega
    simpa only [List.replicate_succ,List.cons_append,loadCount,stepCount] using all

private theorem unaryProduct_readRight (tail : List Bool) (left remaining loaded answer : ℕ) :
    UnaryProductRun (unaryProductCfg (some .readRight) (tallies remaining++false::tail) left loaded 0 answer)
      (unaryProductCfg (some .consumeLeft) tail left (loaded+remaining) 0 answer) (remaining+1) := by
  induction remaining generalizing loaded with
  | zero =>
    simpa only [Nat.add_zero,Nat.zero_add,List.replicate_zero,List.nil_append] using unaryProduct_rightDivider tail left loaded answer
  | succ remaining ih =>
    have first := unaryProduct_rightSymbol (tallies remaining++false::tail) left loaded answer
    have all := unaryProduct_join first (ih (loaded+1))
    have loadCount : loaded+1+remaining = loaded+(remaining+1) := by omega
    have stepCount : 1+(remaining+1) = remaining+1+1 := by omega
    simpa only [List.replicate_succ,List.cons_append,loadCount,stepCount] using all

private theorem unaryProduct_copy (tail : List Bool) (left remaining temporary answer : ℕ) :
    UnaryProductRun (unaryProductCfg (some .copyRight) tail left remaining temporary answer)
      (unaryProductCfg (some .restoreRight) tail left 0 (temporary+remaining) (answer+remaining)) (remaining+1) := by
  induction remaining generalizing temporary answer with
  | zero => simpa only [Nat.add_zero] using unaryProduct_copyEnd tail left temporary answer
  | succ remaining ih =>
    have first := unaryProduct_copyTally tail left remaining temporary answer
    have all := unaryProduct_join first (ih (temporary+1) (answer+1))
    have counts (x : ℕ) : x+1+remaining = x+(remaining+1) := by omega
    have stepCount : 1+(remaining+1) = remaining+1+1 := by omega
    simpa only [counts,stepCount] using all

private theorem unaryProduct_restore (tail : List Bool) (left right remaining answer : ℕ) :
    UnaryProductRun (unaryProductCfg (some .restoreRight) tail left right remaining answer)
      (unaryProductCfg (some .consumeLeft) tail left (right+remaining) 0 answer) (remaining+1) := by
  induction remaining generalizing right with
  | zero => simpa only [Nat.add_zero] using unaryProduct_restoreEnd tail left right answer
  | succ remaining ih =>
    have first := unaryProduct_restoreTally tail left right remaining answer
    have all := unaryProduct_join first (ih (right+1))
    have count : right+1+remaining = right+(remaining+1) := by omega
    have stepCount : 1+(remaining+1) = remaining+1+1 := by omega
    simpa only [count,stepCount] using all

private theorem unaryProduct_clear (tail : List Bool) (right answer : ℕ) :
    UnaryProductRun (unaryProductCfg (some .clearRight) tail 0 right 0 answer)
      (unaryProductCfg (some .readLeft) tail 0 0 0 answer) (right+1) := by
  induction right with
  | zero => exact unaryProduct_clearEnd tail answer
  | succ right ih =>
    have all := unaryProduct_join (unaryProduct_clearTally tail right answer) ih
    have stepCount : 1+(right+1) = right+1+1 := by omega
    simpa only [stepCount] using all

private theorem unaryProduct_consume (tail : List Bool) (left right answer : ℕ) :
    UnaryProductRun (unaryProductCfg (some .consumeLeft) tail left right 0 answer)
      (unaryProductCfg (some .clearRight) tail 0 right 0 (answer+left*right)) (left*(2*right+3)+1) := by
  induction left generalizing answer with
  | zero => simpa only [Nat.zero_mul,Nat.zero_add,Nat.add_zero] using unaryProduct_consumeEnd tail right answer
  | succ left ih =>
    have first := unaryProduct_consumeTally tail left right answer
    have copied := unaryProduct_copy tail left right 0 answer
    have restored := unaryProduct_restore tail left 0 right (answer+right)
    rw [Nat.zero_add] at copied restored
    have one := unaryProduct_join (unaryProduct_join first copied) restored
    have all := unaryProduct_join one (ih (answer+right))
    have count : answer+right+left*right = answer+(left+1)*right := by ring
    have pay : 1+(right+1)+(right+1)+(left*(2*right+3)+1) = (left+1)*(2*right+3)+1 := by ring
    simpa only [count,pay] using all

private def encodeUnaryProductPair (terms : ℕ × ℕ) : List Bool :=
  tallies terms.1 ++ false::(tallies terms.2 ++ [false])

/-- The transitions needed to read, multiply and clear a single pair. -/
def steinerUnaryProductPairSteps (terms : ℕ × ℕ) : ℕ :=
  2*terms.1*terms.2+4*terms.1+2*terms.2+4

private theorem unaryProduct_pair (a b answer : ℕ) (tail : List Bool) :
    UnaryProductRun (unaryProductCfg (some .readLeft) (encodeUnaryProductPair (a,b)++tail) 0 0 0 answer)
      (unaryProductCfg (some .readLeft) tail 0 0 0 (answer+a*b)) (steinerUnaryProductPairSteps (a,b)) := by
  have left := unaryProduct_readLeft (tallies b++false::tail) a 0 answer
  have right := unaryProduct_readRight tail a b 0 answer
  rw [Nat.zero_add] at left right
  have operands := unaryProduct_join left right
  have multiplied := unaryProduct_join operands (unaryProduct_consume tail a b answer)
  have all := unaryProduct_join multiplied (unaryProduct_clear tail b (answer+a*b))
  have pay : a+1+(b+1)+(a*(2*b+3)+1)+(b+1) = steinerUnaryProductPairSteps (a,b) := by
    unfold steinerUnaryProductPairSteps
    ring
  simpa only [pay,encodeUnaryProductPair,List.append_assoc,List.cons_append,List.singleton_append,List.nil_append] using all

/-- Encode every unary operand with a following false delimiter. -/
def encodeSteinerUnaryProductRequests (requests : List (ℕ × ℕ)) : List Bool :=
  requests.flatMap encodeUnaryProductPair

/-- The numerical value computed by the machine. -/
def steinerUnaryProductSum (requests : List (ℕ × ℕ)) : ℕ :=
  (requests.map fun operands => operands.1*operands.2).sum

/-- The unary output contains one true tally per unit of the sum. -/
def encodeSteinerUnaryProductCount (count : ℕ) : List Bool := tallies count

/-- The transition count includes one step after the last pair. -/
def steinerUnaryProductSteps (requests : List (ℕ × ℕ)) : ℕ :=
  (requests.map steinerUnaryProductPairSteps).sum+1

private theorem unaryProduct_all (requests : List (ℕ × ℕ)) (answer : ℕ) :
    UnaryProductRun (unaryProductCfg (some .readLeft) (encodeSteinerUnaryProductRequests requests) 0 0 0 answer)
      (unaryProductCfg none [] 0 0 0 (answer+steinerUnaryProductSum requests)) (steinerUnaryProductSteps requests) := by
  induction requests generalizing answer with
  | nil =>
    simpa only [encodeSteinerUnaryProductRequests,steinerUnaryProductSteps,steinerUnaryProductSum,
      List.flatMap_nil,List.map_nil,List.sum_nil,Nat.add_zero,Nat.zero_add] using unaryProduct_leftEnd answer
  | cons pair remaining ih =>
    obtain ⟨a,b⟩ := pair
    have first := unaryProduct_pair a b answer (encodeSteinerUnaryProductRequests remaining)
    have all := unaryProduct_join first (ih (answer+a*b))
    simpa only [encodeSteinerUnaryProductRequests,steinerUnaryProductSum,steinerUnaryProductSteps,
      List.flatMap_cons,List.map_cons,List.sum_cons,Nat.add_assoc] using all

private theorem unaryProduct_init (input : List Bool) :
    initList steinerUnaryProductMachine input = unaryProductCfg (some .readLeft) input 0 0 0 0 := by
  apply congrArg (fun stk : Fin 5 → List Bool =>
    (⟨some .readLeft,none,stk⟩ : steinerUnaryProductMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem unaryProduct_halt (answer : ℕ) :
    haltList steinerUnaryProductMachine (encodeSteinerUnaryProductCount answer) = unaryProductCfg none [] 0 0 0 answer := by
  apply congrArg (fun stk : Fin 5 → List Bool =>
    (⟨none,none,stk⟩ : steinerUnaryProductMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- The machine returns exactly the unary sum of products. The witness
uses the explicit transition count, including zero operands. -/
def steinerUnaryProductMachine_run (requests : List (ℕ × ℕ)) :
    TM2OutputsInTime steinerUnaryProductMachine (encodeSteinerUnaryProductRequests requests)
      (some (encodeSteinerUnaryProductCount (steinerUnaryProductSum requests))) (steinerUnaryProductSteps requests) where
  steps := steinerUnaryProductSteps requests
  steps_le_m := le_rfl
  evals_in_steps := by
    change UnaryProductRun (initList steinerUnaryProductMachine (encodeSteinerUnaryProductRequests requests))
      (haltList steinerUnaryProductMachine (encodeSteinerUnaryProductCount (steinerUnaryProductSum requests))) _
    rw [unaryProduct_init,unaryProduct_halt]
    simpa only [Nat.zero_add] using unaryProduct_all requests 0

theorem steinerUnaryProductMachine_steps (requests : List (ℕ × ℕ)) :
    (steinerUnaryProductMachine_run requests).steps = steinerUnaryProductSteps requests := rfl

private theorem encodeUnaryProductPair_length (a b : ℕ) : (encodeUnaryProductPair (a,b)).length = a+b+2 := by
  simp only [encodeUnaryProductPair,List.length_append,List.length_cons,List.length_replicate,List.length_nil]
  omega

/-- A quadratic bound in the total length of the framed unary input. -/
theorem steinerUnaryProductSteps_le (requests : List (ℕ × ℕ)) :
    steinerUnaryProductSteps requests ≤ (encodeSteinerUnaryProductRequests requests).length^2+
      4*(encodeSteinerUnaryProductRequests requests).length+1 := by
  unfold steinerUnaryProductSteps
  apply Nat.succ_le_succ
  induction requests with
  | nil => simp
  | cons pair remaining ih =>
    obtain ⟨a,b⟩ := pair
    let left := a+b+2
    let right := (encodeSteinerUnaryProductRequests remaining).length
    have input : (encodeSteinerUnaryProductRequests ((a,b)::remaining)).length = left+right := by
      simp only [encodeSteinerUnaryProductRequests,List.flatMap_cons,List.length_append,
        encodeUnaryProductPair_length,left,right]
    have independent : steinerUnaryProductPairSteps (a,b) ≤ left^2+4*left := by
      dsimp [steinerUnaryProductPairSteps,left]
      nlinarith only [Nat.zero_le (a*a),Nat.zero_le (b*b),Nat.zero_le a,Nat.zero_le b]
    rw [input,List.map_cons,List.sum_cons]
    change (remaining.map steinerUnaryProductPairSteps).sum ≤ right^2+4*right at ih
    have paid := Nat.add_le_add independent ih
    exact paid.trans (by nlinarith only [Nat.zero_le (left*right)])

/-- Copying and restoring spends at least two transitions per output tally. -/
theorem steinerUnaryProductSum_twice_le_steps (requests : List (ℕ × ℕ)) :
    2*steinerUnaryProductSum requests ≤ steinerUnaryProductSteps requests := by
  induction requests with
  | nil => decide
  | cons pair remaining ih =>
    obtain ⟨a,b⟩ := pair
    simp only [steinerUnaryProductSum,steinerUnaryProductSteps,List.map_cons,List.sum_cons,
      steinerUnaryProductPairSteps,Nat.mul_add,Nat.mul_assoc] at ih ⊢
    omega

/-- Polynomial time in the length of the framed unary operands. -/
noncomputable def steinerUnaryProductMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerUnaryProductRequests encodeSteinerUnaryProductCount steinerUnaryProductSum where
  tm := steinerUnaryProductMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X^2+Polynomial.C 4*Polynomial.X+Polynomial.C 1
  outputsFun requests := by
    have run := steinerUnaryProductMachine_run requests
    change TM2OutputsInTime steinerUnaryProductMachine ((encodeSteinerUnaryProductRequests requests).map id)
      (some ((encodeSteinerUnaryProductCount (steinerUnaryProductSum requests)).map id)) _
    simpa only [List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_C] using
      (show TM2OutputsInTime steinerUnaryProductMachine (encodeSteinerUnaryProductRequests requests)
        (some (encodeSteinerUnaryProductCount (steinerUnaryProductSum requests))) _
        from ⟨run.toEvalsTo,run.steps_le_m.trans (steinerUnaryProductSteps_le requests)⟩)

end OnlineReachabilityPreservers
