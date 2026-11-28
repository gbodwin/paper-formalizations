import Mathlib.Data.Nat.Size
import OnlineReachabilityPreservers.SteinerUnaryProductMachine

/-! Compute the bit width of one unary graph dimension by repeated halving. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private inductive UnaryWidthLabel where
  | skip
  | start (side : Bool)
  | halve (side odd : Bool)
  deriving Fintype

private abbrev UnaryWidthProgram :=
  Turing.TM2.Stmt (fun _ : Fin 3 => Bool) UnaryWidthLabel (Option Bool)

private def widthInput : Bool → Fin 3
  | false => 0
  | true => 1

private def widthNext (label : UnaryWidthLabel) : UnaryWidthProgram :=
  load (fun _ => none) (goto (fun _ => label))

private def unaryWidthProgram : UnaryWidthLabel → UnaryWidthProgram
  | .skip => pop 0 (fun _ _ => none) (widthNext (.start false))
  | .start side =>
    pop (widthInput side) (fun _ a => a) <|
      branch Option.isSome
        (push 2 (fun _ => true) (widthNext (.halve side true)))
        (load (fun _ => none) halt)
  | .halve side odd =>
    pop (widthInput side) (fun _ a => a) <|
      branch Option.isSome
        (if odd then push (widthInput (!side)) (fun _ => true) (widthNext (.halve side false))
         else widthNext (.halve side true))
        (widthNext (.start (!side)))

private abbrev unaryWidthMachine (drop : Bool) : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := UnaryWidthLabel
  main := if drop then .skip else .start false
  σ := Option Bool
  initialState := none
  m := unaryWidthProgram

/-- Alternate two unary stacks. Each nonempty pass emits a width tally
and sends half as many input tallies to the other stack. -/
abbrev steinerUnaryBitWidthMachine : FinTM2 := unaryWidthMachine false

/-- The index width for a population of size n is the bit width of
n minus one, with natural-number subtraction at the empty population. -/
abbrev steinerUnaryIndexBitWidthMachine : FinTM2 := unaryWidthMachine true

private def widthCfg (label : Option UnaryWidthLabel) (side : Bool) (input half out : List Bool) :
    steinerUnaryBitWidthMachine.Cfg where
  l := label
  var := none
  stk := if side then ![half,input,out] else ![input,half,out]

private theorem width_update0 (a b c new : List Bool) :
    Function.update (![a,b,c] : Fin 3 → List Bool) 0 new = ![new,b,c] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem width_update1 (a b c new : List Bool) :
    Function.update (![a,b,c] : Fin 3 → List Bool) 1 new = ![a,new,c] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem width_update2 (a b c new : List Bool) :
    Function.update (![a,b,c] : Fin 3 → List Bool) 2 new = ![a,b,new] := by
  funext i
  fin_cases i <;> simp [Function.update]

private def width_one {a b : steinerUnaryBitWidthMachine.Cfg}
    (move : steinerUnaryBitWidthMachine.step a = some b) :
    EvalsToInTime steinerUnaryBitWidthMachine.step a (some b) 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := move

private theorem width_start (side : Bool) (input out : List Bool) :
    steinerUnaryBitWidthMachine.step (widthCfg (some (.start side)) side (true::input) [] out) =
      some (widthCfg (some (.halve side true)) side input [] (true::out)) := by
  cases side <;>
    simp [FinTM2.step,steinerUnaryBitWidthMachine,unaryWidthMachine,widthCfg,Turing.TM2.step,Turing.TM2.stepAux,
      unaryWidthProgram,widthInput,widthNext,width_update0,width_update1,width_update2] <;> rfl

private theorem width_end (side : Bool) (out : List Bool) :
    steinerUnaryBitWidthMachine.step (widthCfg (some (.start side)) side [] [] out) =
      some (widthCfg none false [] [] out) := by
  cases side <;>
    simp [FinTM2.step,steinerUnaryBitWidthMachine,unaryWidthMachine,widthCfg,Turing.TM2.step,Turing.TM2.stepAux,
      unaryWidthProgram,widthInput,width_update0,width_update1] <;> rfl

private theorem width_even (side : Bool) (input half out : List Bool) :
    steinerUnaryBitWidthMachine.step (widthCfg (some (.halve side false)) side (true::input) half out) =
      some (widthCfg (some (.halve side true)) side input half out) := by
  cases side <;>
    simp [FinTM2.step,steinerUnaryBitWidthMachine,unaryWidthMachine,widthCfg,Turing.TM2.step,Turing.TM2.stepAux,
      unaryWidthProgram,widthInput,widthNext,width_update0,width_update1] <;> rfl

private theorem width_odd (side : Bool) (input half out : List Bool) :
    steinerUnaryBitWidthMachine.step (widthCfg (some (.halve side true)) side (true::input) half out) =
      some (widthCfg (some (.halve side false)) side input (true::half) out) := by
  cases side <;>
    simp [FinTM2.step,steinerUnaryBitWidthMachine,unaryWidthMachine,widthCfg,Turing.TM2.step,Turing.TM2.stepAux,
      unaryWidthProgram,widthInput,widthNext,width_update0,width_update1] <;> rfl

private theorem width_swap (side odd : Bool) (half out : List Bool) :
    steinerUnaryBitWidthMachine.step (widthCfg (some (.halve side odd)) side [] half out) =
      some (widthCfg (some (.start (!side))) (!side) half [] out) := by
  cases side <;> cases odd <;>
    simp [FinTM2.step,steinerUnaryBitWidthMachine,unaryWidthMachine,widthCfg,Turing.TM2.step,Turing.TM2.stepAux,
      unaryWidthProgram,widthInput,widthNext,width_update0,width_update1] <;> rfl

private abbrev widthTallies := encodeSteinerUnaryProductCount

private def width_halve (side odd : Bool) (n h : ℕ) (out : List Bool) :
    EvalsToInTime steinerUnaryBitWidthMachine.step
      (widthCfg (some (.halve side odd)) side (widthTallies n) (widthTallies h) out)
      (some (widthCfg (some (.start (!side))) (!side) (widthTallies (h+(n+odd.toNat)/2)) [] out)) (n+1) := by
  induction n generalizing odd h with
  | zero => cases odd <;> exact width_one (width_swap side _ _ out)
  | succ n ih =>
    cases odd with
    | false =>
      exact EvalsToInTime.trans _ _ _ _ _ _
        (width_one (width_even side (widthTallies n) (widthTallies h) out)) (ih true h)
    | true =>
      have all := EvalsToInTime.trans _ _ _ _ _ _
        (width_one (width_odd side (widthTallies n) (widthTallies h) out)) (ih false (h+1))
      have quotient : h+1+(n+false.toNat)/2 = h+(n+1+true.toNat)/2 := by
        simp only [Bool.toNat_false,Bool.toNat_true,Nat.add_zero]
        omega
      rw [quotient] at all
      exact all

private theorem width_size_of_positive {n : ℕ} (positive : 0 < n) :
    (n/2).size+1 = n.size := by
  have name := Nat.bit_bodd_div2 n
  have nz : Nat.bit n.bodd n.div2 ≠ 0 := by
    rw [name]
    exact Nat.ne_of_gt positive
  calc
    (n/2).size+1 = n.div2.size+1 := rfl
    _ = (Nat.bit n.bodd n.div2).size := (Nat.size_bit nz).symm
    _ = n.size := congrArg Nat.size name

private theorem width_tallies_append (n : ℕ) (out : List Bool) :
    widthTallies n++true::out = widthTallies (n+1)++out := by
  simp only [encodeSteinerUnaryProductCount,List.replicate_add,List.replicate_one,List.append_assoc,List.singleton_append]

private def width_evaluate (n : ℕ) (side : Bool) (out : List Bool) :
    EvalsToInTime steinerUnaryBitWidthMachine.step
      (widthCfg (some (.start side)) side (widthTallies n) [] out)
      (some (widthCfg none false [] [] (widthTallies n.size++out))) (3*n+1) := by
  cases n with
  | zero => exact width_one (width_end side out)
  | succ n =>
    have first := width_one (width_start side (widthTallies n) out)
    have half := width_halve side true n 0 (true::out)
    simp only [Nat.zero_add,Bool.toNat_true] at half
    have pass := EvalsToInTime.trans _ _ _ _ _ _ first half
    have tail := width_evaluate ((n+1)/2) (!side) (true::out)
    rw [width_tallies_append,width_size_of_positive (show 0 < n+1 by omega)] at tail
    have all := EvalsToInTime.trans _ _ _ _ _ _ pass tail
    refine ⟨all.toEvalsTo,?_⟩
    have spent := all.steps_le_m
    omega
termination_by n
decreasing_by omega

private theorem width_init (word : List Bool) :
    initList steinerUnaryBitWidthMachine word = widthCfg (some (.start false)) false word [] [] := by
  apply congrArg (fun stk : Fin 3 → List Bool =>
    (⟨some (.start false),none,stk⟩ : steinerUnaryBitWidthMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem width_halt (word : List Bool) :
    haltList steinerUnaryBitWidthMachine word = widthCfg none false [] [] word := by
  apply congrArg (fun stk : Fin 3 → List Bool => (⟨none,none,stk⟩ : steinerUnaryBitWidthMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- The machine emits the exact Nat.size of the unary value in at most
three times its input length plus one transitions. -/
def steinerUnaryBitWidthMachine_run (n : ℕ) :
    TM2OutputsInTime steinerUnaryBitWidthMachine (encodeSteinerUnaryProductCount n)
      (some (encodeSteinerUnaryProductCount n.size)) (3*n+1) := by
  have run := width_evaluate n false []
  rw [List.append_nil] at run
  change EvalsToInTime steinerUnaryBitWidthMachine.step (initList _ _) (some (haltList _ _)) _
  rw [width_init,width_halt]
  exact run

private theorem width_skip (n : ℕ) :
    steinerUnaryBitWidthMachine.step (widthCfg (some .skip) false (widthTallies n) [] []) =
      some (widthCfg (some (.start false)) false (widthTallies (n-1)) [] []) := by
  cases n <;>
    simp [FinTM2.step,steinerUnaryBitWidthMachine,unaryWidthMachine,widthCfg,Turing.TM2.step,Turing.TM2.stepAux,
      unaryWidthProgram,widthNext,width_update0,encodeSteinerUnaryProductCount] <;> rfl

private theorem width_indexInit (word : List Bool) :
    initList steinerUnaryIndexBitWidthMachine word = widthCfg (some .skip) false word [] [] := by
  apply congrArg (fun stk : Fin 3 → List Bool =>
    (⟨some .skip,none,stk⟩ : steinerUnaryIndexBitWidthMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- Skip the first tally before measuring width. The empty input still
returns width zero. -/
def steinerUnaryIndexBitWidthMachine_run (n : ℕ) :
    TM2OutputsInTime steinerUnaryIndexBitWidthMachine (encodeSteinerUnaryProductCount n)
      (some (encodeSteinerUnaryProductCount (n-1).size)) (3*n+2) := by
  have tail := width_evaluate (n-1) false []
  rw [List.append_nil] at tail
  have all := EvalsToInTime.trans _ _ _ _ _ _ (width_one (width_skip n)) tail
  change EvalsToInTime steinerUnaryBitWidthMachine.step (initList steinerUnaryIndexBitWidthMachine _)
    (some (haltList steinerUnaryBitWidthMachine _)) _
  rw [width_indexInit,width_halt]
  exact ⟨all.toEvalsTo,by have spent := all.steps_le_m; omega⟩

/-- A linear transition bound in the unary input length. -/
noncomputable def steinerUnaryBitWidthMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerUnaryProductCount encodeSteinerUnaryProductCount Nat.size where
  tm := steinerUnaryBitWidthMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 3*Polynomial.X+Polynomial.C 1
  outputsFun n := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,Polynomial.eval_X,
      Polynomial.eval_C,encodeSteinerUnaryProductCount,List.length_replicate] using steinerUnaryBitWidthMachine_run n

/-- A linear transition bound for the index-width variant. -/
noncomputable def steinerUnaryIndexBitWidthMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerUnaryProductCount encodeSteinerUnaryProductCount (fun n => (n-1).size) where
  tm := steinerUnaryIndexBitWidthMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 3*Polynomial.X+Polynomial.C 2
  outputsFun n := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,Polynomial.eval_X,
      Polynomial.eval_C,encodeSteinerUnaryProductCount,List.length_replicate] using steinerUnaryIndexBitWidthMachine_run n

end OnlineReachabilityPreservers
