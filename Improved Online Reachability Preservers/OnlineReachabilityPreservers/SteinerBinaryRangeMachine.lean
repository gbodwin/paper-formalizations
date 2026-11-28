import OnlineReachabilityPreservers.SteinerBinaryComparisonMachine
import OnlineReachabilityPreservers.SteinerBinaryVariableWordInput

/-! A finite stack machine for batches of endpoint range checks. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

def alignBinaryDigits (left right : List Bool) : List (Bool × Bool) :=
  List.zipWithAll (fun a b => (a.getD false,b.getD false)) left right

def foldedBorrow (digits : List (Bool × Bool)) (borrow : Bool) : Bool :=
  digits.foldl (fun borrow pair => nextBinaryBorrow pair.1 pair.2 borrow) borrow

theorem alignBinaryDigits_cons {left right : List Bool} (nonempty : ¬ (left = [] ∧ right = [])) :
    alignBinaryDigits left right =
      (left.headD false,right.headD false) :: alignBinaryDigits left.tail right.tail := by
  cases left <;> cases right
  · exact (nonempty ⟨rfl,rfl⟩).elim
  all_goals simp [alignBinaryDigits]

theorem alignedBorrow_eq_binaryLess (left right : List Bool) (borrow : Bool) :
    foldedBorrow (alignBinaryDigits left right) borrow = (binaryLessWithWork left right borrow).1 := by
  induction total : left.length+right.length using Nat.strong_induction_on generalizing left right borrow with
  | h size smaller =>
    by_cases empty : left = [] ∧ right = []
    · obtain ⟨rfl,rfl⟩ := empty
      simp [alignBinaryDigits,foldedBorrow,binaryLessWithWork]
    have shorter : left.tail.length+right.tail.length < size := by
      cases left <;> cases right <;> simp_all <;> omega
    rw [alignBinaryDigits_cons empty,foldedBorrow,List.foldl_cons,binaryLessWithWork,dite_eq_right empty]
    exact smaller _ shorter left.tail right.tail _ rfl

theorem alignBinaryDigits_length_le (left right : List Bool) :
    (alignBinaryDigits left right).length ≤ left.length+right.length := by
  induction left generalizing right with
  | nil => simp [alignBinaryDigits]
  | cons bit left ih =>
    cases right with
    | nil => simp [alignBinaryDigits]
    | cons other right =>
      have former := ih right
      simp only [alignBinaryDigits,List.zipWithAll_cons_cons,List.length_cons] at former ⊢
      omega

/-- Pair the low bits, pad the shorter side with false and put a separator
after each check. The bit pairs are supplied in this encoding. -/
abbrev SteinerRangeWordPair := List Bool × List Bool

def encodeSteinerRangeChecks (checks : List SteinerRangeWordPair) : List (Option (Bool × Bool)) :=
  checks.flatMap fun check => (alignBinaryDigits check.1 check.2).map some ++ [none]

def steinerRangeChecks (checks : List SteinerRangeWordPair) : Bool :=
  checks.all fun check => (binaryLessWithWork check.1 check.2 false).1

private abbrev RangeSymbol := Option (Bool × Bool)
private abbrev RangeRegister := Bool × (Bool × Option RangeSymbol)

private def rangeObserve (r : RangeRegister) (seen : Option RangeSymbol) : RangeRegister :=
  (r.1,(r.2.1,seen))

private def rangeRememberDigit (r : RangeRegister) (seen : Option RangeSymbol) : RangeRegister :=
  let bits := seen.join.getD (false,false)
  (r.1,(nextBinaryBorrow bits.1 bits.2 r.2.1,none))

private def rangeFinishCheck (r : RangeRegister) (_ : Option RangeSymbol) : RangeRegister :=
  (r.1 && r.2.1,(false,none))

private def steinerRangeProgram : Turing.TM2.Stmt (fun _ : Unit => RangeSymbol) Unit RangeRegister :=
  peek () rangeObserve <|
    branch (fun r => r.2.2.isSome)
      (branch (fun r => r.2.2.join.isSome)
        (pop () rangeRememberDigit (goto fun _ => ()))
        (pop () rangeFinishCheck (goto fun _ => ())))
      (push () (fun r => some (r.1,false)) <| load (fun _ => (true,(false,none))) halt)

/-- A single-stack batch range checker. It updates the borrow on a digit
and folds the comparison into the acceptance flag at each separator. -/
abbrev steinerRangeMachine : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := RangeSymbol
  Λ := Unit
  main := ()
  σ := RangeRegister
  initialState := (true,(false,none))
  m _ := steinerRangeProgram

private def rangeConfig (label : Option Unit) (accept borrow : Bool) (tape : List RangeSymbol) :
    steinerRangeMachine.Cfg where
  l := label
  var := (accept,(borrow,none))
  stk := fun _ => tape

private theorem rangeUpdateStack (old next : List RangeSymbol) :
    Function.update (fun _ : Unit => old) () next = fun _ => next := by
  funext k
  cases k
  simp

private theorem rangeStep_digit (accept borrow : Bool) (pair : Bool × Bool) (tape : List RangeSymbol) :
    steinerRangeMachine.step (rangeConfig (some ()) accept borrow (some pair::tape)) =
      some (rangeConfig (some ()) accept (nextBinaryBorrow pair.1 pair.2 borrow) tape) := by
  simp [FinTM2.step,steinerRangeMachine,rangeConfig,Turing.TM2.step,Turing.TM2.stepAux,
    steinerRangeProgram,rangeObserve,rangeRememberDigit,rangeUpdateStack]
  rfl

private theorem rangeStep_separator (accept borrow : Bool) (tape : List RangeSymbol) :
    steinerRangeMachine.step (rangeConfig (some ()) accept borrow (none::tape)) =
      some (rangeConfig (some ()) (accept && borrow) false tape) := by
  simp [FinTM2.step,steinerRangeMachine,rangeConfig,Turing.TM2.step,Turing.TM2.stepAux,
    steinerRangeProgram,rangeObserve,rangeFinishCheck,rangeUpdateStack]
  rfl

private theorem rangeStep_done (accept : Bool) :
    steinerRangeMachine.step (rangeConfig (some ()) accept false []) =
      some (rangeConfig none true false [some (accept,false)]) := by
  simp [FinTM2.step,steinerRangeMachine,rangeConfig,Turing.TM2.step,Turing.TM2.stepAux,
    steinerRangeProgram,rangeObserve,rangeUpdateStack]
  rfl

private def rangeSingleStep {a b : steinerRangeMachine.Cfg}
    (step : steinerRangeMachine.step a = some b) : EvalsToInTime steinerRangeMachine.step a (some b) 1 where
  steps := 1
  evals_in_steps := by change steinerRangeMachine.step a = some b; exact step
  steps_le_m := le_rfl

private def rangeConsumeDigits (digits : List (Bool × Bool)) (tape : List RangeSymbol) (accept borrow : Bool) :
    EvalsToInTime steinerRangeMachine.step
      (rangeConfig (some ()) accept borrow (digits.map some ++ tape))
      (some (rangeConfig (some ()) accept (foldedBorrow digits borrow) tape)) digits.length := by
  induction digits generalizing borrow with
  | nil => exact EvalsToInTime.refl _ _
  | cons digit digits ih =>
    have first := rangeSingleStep (rangeStep_digit accept borrow digit (digits.map some ++ tape))
    have rest := ih (nextBinaryBorrow digit.1 digit.2 borrow)
    exact EvalsToInTime.trans _ _ _ _ _ _ first rest

private def rangeConsumeChecks (checks : List SteinerRangeWordPair) (accept : Bool) :
    EvalsToInTime steinerRangeMachine.step (rangeConfig (some ()) accept false (encodeSteinerRangeChecks checks))
      (some (rangeConfig none true false [some (accept && steinerRangeChecks checks,false)]))
      ((encodeSteinerRangeChecks checks).length+1) := by
  induction checks generalizing accept with
  | nil => simpa [encodeSteinerRangeChecks,steinerRangeChecks] using rangeSingleStep (rangeStep_done accept)
  | cons check rest ih =>
    let digits := alignBinaryDigits check.1 check.2
    let pending := encodeSteinerRangeChecks rest
    let flag := (binaryLessWithWork check.1 check.2 false).1
    have scan := rangeConsumeDigits digits (none::pending) accept false
    rw [show foldedBorrow digits false = flag from alignedBorrow_eq_binaryLess _ _ _] at scan
    have divider := rangeSingleStep (rangeStep_separator accept flag pending)
    have first := EvalsToInTime.trans _ _ _ _ _ _ scan divider
    have later := ih (accept && flag)
    have all := EvalsToInTime.trans _ _ _ _ _ _ first later
    have length : (encodeSteinerRangeChecks (check::rest)).length = digits.length+1+pending.length := by
      change ((digits.map some ++ [none]) ++ pending).length = _
      simp only [List.length_append,List.length_map,List.length_singleton]
    rw [length]
    have count : pending.length+1+(1+digits.length) = digits.length+1+pending.length+1 := by omega
    change EvalsToInTime steinerRangeMachine.step _ _ (pending.length+1+(1+digits.length)) at all
    rw [count] at all
    simpa only [encodeSteinerRangeChecks,List.flatMap_cons,List.append_assoc,List.singleton_append,
      steinerRangeChecks,List.all_cons,Bool.and_assoc,digits,pending,flag] using all

private theorem rangeMachine_init (tape : List RangeSymbol) :
    initList steinerRangeMachine tape = rangeConfig (some ()) true false tape := by
  rfl

private theorem rangeMachine_halt (output : List RangeSymbol) :
    haltList steinerRangeMachine output = rangeConfig none true false output := by
  rfl

/-- Exactly one transition per encoded symbol and one final transition
suffice to return the conjunction of the numeric checks. -/
def steinerRangeMachine_run (checks : List SteinerRangeWordPair) :
    TM2OutputsInTime steinerRangeMachine (encodeSteinerRangeChecks checks)
      (some [some (steinerRangeChecks checks,false)]) ((encodeSteinerRangeChecks checks).length+1) := by
  unfold TM2OutputsInTime
  change EvalsToInTime steinerRangeMachine.step _ (some (haltList steinerRangeMachine _)) _
  rw [rangeMachine_init,rangeMachine_halt]
  simpa only [Bool.true_and] using rangeConsumeChecks checks true

/-- One comparison for each endpoint of each raw row, with the supplied
vertex bound as its right operand. -/
def steinerRangeRequests (bound : List Bool) (rows : List SteinerRangeWordPair) : List SteinerRangeWordPair :=
  rows.flatMap fun row => [(row.1,bound),(row.2,bound)]

theorem encodeSteinerRangeRequests_length_le (bound : List Bool) (rows : List SteinerRangeWordPair) :
    (encodeSteinerRangeChecks (steinerRangeRequests bound rows)).length ≤
      binaryEndpointBits rows+2*rows.length*(bound.length+1) := by
  induction rows with
  | nil => simp [encodeSteinerRangeChecks,steinerRangeRequests,binaryEndpointBits]
  | cons row rows ih =>
    have left := alignBinaryDigits_length_le row.1 bound
    have right := alignBinaryDigits_length_le row.2 bound
    simp only [encodeSteinerRangeChecks,steinerRangeRequests,List.flatMap_cons,List.cons_append,List.nil_append,
      List.length_append,List.length_map,List.length_cons,List.length_nil,binaryEndpointBits,List.map_cons,List.sum_cons] at ih ⊢
    rw [Nat.mul_succ 2,Nat.add_mul]
    omega

/-- The machine's flag agrees with acceptance by the variable-length
endpoint decoder, for any supplied bound word decoding to the vertex count. -/
theorem steinerRangeRequests_accepts_iff {n : ℕ} (bound : List Bool) (number : binaryWordValue bound = n)
    (rows : List SteinerRangeWordPair) (width : ℕ) :
    steinerRangeChecks (steinerRangeRequests bound rows) = true ↔
      ∃ decoded, (decodeBinaryFinArcRowsWithWork (n := n) width rows).1 = some decoded := by
  rw [decodeBinaryFinArcRowsWithWork_some_iff_valid]
  induction rows with
  | nil => simp [steinerRangeRequests,steinerRangeChecks]
  | cons row rows ih =>
    simp only [steinerRangeRequests,List.flatMap_cons,List.cons_append,List.nil_append,steinerRangeChecks,
      List.all_cons,Bool.and_eq_true]
    have prior := ih
    simp only [steinerRangeChecks,steinerRangeRequests] at prior
    rw [prior,(binaryLessWithWork_noBorrow_spec _ _).1,(binaryLessWithWork_noBorrow_spec _ _).1]
    simp [number,and_assoc]

/-- The raw endpoint range check consumes the padded-pair encoding in a
bound polynomial in its supplied rows, endpoint bits and bound word. -/
def steinerRangeMachine_graphInput (bound : List Bool) (rows : List SteinerRangeWordPair) :
    TM2OutputsInTime steinerRangeMachine (encodeSteinerRangeChecks (steinerRangeRequests bound rows))
      (some [some (steinerRangeChecks (steinerRangeRequests bound rows),false)])
      (binaryEndpointBits rows+2*rows.length*(bound.length+1)+1) := by
  have result := steinerRangeMachine_run (steinerRangeRequests bound rows)
  exact ⟨result.toEvalsTo,result.steps_le_m.trans (Nat.add_le_add_right (encodeSteinerRangeRequests_length_le bound rows) 1)⟩

/-- A one-symbol answer in the padded-pair alphabet. -/
def encodeSteinerRangeAnswer (accepted : Bool) : List (Option (Bool × Bool)) :=
  [some (accepted,false)]

/-- The machine is linear in the supplied batch of aligned pairs. -/
noncomputable def steinerRangeMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerRangeChecks encodeSteinerRangeAnswer steinerRangeChecks where
  tm := steinerRangeMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X+Polynomial.C 1
  outputsFun checks := by
    change TM2OutputsInTime steinerRangeMachine ((encodeSteinerRangeChecks checks).map id)
      (some ((encodeSteinerRangeAnswer (steinerRangeChecks checks)).map id)) _
    simpa only [List.map_id_fun,id_eq,encodeSteinerRangeAnswer,Polynomial.eval_add,Polynomial.eval_X,
      Polynomial.eval_C] using steinerRangeMachine_run checks

/-- For the padded-pair representation of a graph input, the machine
returns the decoder's acceptance flag. -/
def steinerRangeMachine_graphDecoder {n : ℕ} (bound : List Bool) (number : binaryWordValue bound = n)
    (rows : List SteinerRangeWordPair) (width : ℕ) :
    TM2OutputsInTime steinerRangeMachine (encodeSteinerRangeChecks (steinerRangeRequests bound rows))
      (some (encodeSteinerRangeAnswer ((decodeBinaryFinArcRowsWithWork (n := n) width rows).1.isSome)))
      (binaryEndpointBits rows+2*rows.length*(bound.length+1)+1) := by
  have correct := steinerRangeRequests_accepts_iff bound number rows width
  have flag : steinerRangeChecks (steinerRangeRequests bound rows) =
      (decodeBinaryFinArcRowsWithWork (n := n) width rows).1.isSome := by
    cases decoded : (decodeBinaryFinArcRowsWithWork (n := n) width rows).1 <;>
      cases accepted : steinerRangeChecks (steinerRangeRequests bound rows) <;> simp_all
  rw [← flag]
  exact steinerRangeMachine_graphInput bound rows

/-- The guarded decoder at the width used by the compact word entry has
the same acceptance flag, so this machine can make its graph check. -/
def steinerRangeMachine_variableGraphCheck {n : ℕ} (bound : List Bool) (number : binaryWordValue bound = n)
    (rows : List SteinerRangeWordPair) :
    TM2OutputsInTime steinerRangeMachine (encodeSteinerRangeChecks (steinerRangeRequests bound rows))
      (some (encodeSteinerRangeAnswer
        ((decodeCheckedBinaryFinArcRowsWithWork (n := n) (n+binaryEndpointBits rows) rows).1.isSome)))
      (binaryEndpointBits rows+2*rows.length*(bound.length+1)+1) := by
  have checked : (decodeCheckedBinaryFinArcRowsWithWork (n := n) (n+binaryEndpointBits rows) rows).1 =
      (decodeBinaryFinArcRowsWithWork (n := n) 0 rows).1 := by
    ext decoded
    exact decodeCheckedBinaryFinArcRowsWithWork_of_actual_bits rows decoded
  rw [checked]
  exact steinerRangeMachine_graphDecoder bound number rows 0

/-- The conjunction of numeric range checks is the guarded decoder's flag. -/
theorem steinerRangeRequests_guarded_flag {n : ℕ} (bound : List Bool) (number : binaryWordValue bound = n)
    (rows : List SteinerRangeWordPair) :
    steinerRangeChecks (steinerRangeRequests bound rows) =
      (decodeCheckedBinaryFinArcRowsWithWork (n := n) (n+binaryEndpointBits rows) rows).1.isSome := by
  have checked : (decodeCheckedBinaryFinArcRowsWithWork (n := n) (n+binaryEndpointBits rows) rows).1 =
      (decodeBinaryFinArcRowsWithWork (n := n) 0 rows).1 := by
    ext decoded
    exact decodeCheckedBinaryFinArcRowsWithWork_of_actual_bits rows decoded
  rw [checked]
  apply Bool.eq_iff_iff.mpr
  exact (steinerRangeRequests_accepts_iff bound number rows 0).trans Option.isSome_iff_exists.symm

end OnlineReachabilityPreservers
