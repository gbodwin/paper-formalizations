import OnlineReachabilityPreservers.SteinerBinaryRangeMachine

/-! A finite stack machine for padding and aligning two separately framed binary words. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

abbrev SteinerAlignmentSymbol := Option Bool ⊕ (Bool × Bool)

private abbrev AlignmentRegisters := Option SteinerAlignmentSymbol × Option SteinerAlignmentSymbol
private abbrev AlignmentProgram :=
  Turing.TM2.Stmt (fun _ : Fin 3 => SteinerAlignmentSymbol) (Fin 4) AlignmentRegisters

private def alignmentBit (symbol : SteinerAlignmentSymbol) : Option Bool :=
  match symbol with
  | .inl bit => bit
  | .inr _ => none

private def alignmentRecord (symbol : Option SteinerAlignmentSymbol) : AlignmentRegisters :=
  (symbol,none)

private def alignmentClear : AlignmentRegisters := (none,none)

private def alignmentProgram (label : Fin 4) : AlignmentProgram :=
  if label = 0 then
    pop 0 (fun _ seen => alignmentRecord seen) <|
      branch (fun r => (r.1.bind alignmentBit).isSome)
        (push 1 (fun r => r.1.getD (Sum.inl none)) <| load (fun _ => alignmentClear) (goto (fun _ => 0)))
        (load (fun _ => alignmentClear) (goto (fun _ => 1)))
  else if label = 1 then
    pop 1 (fun _ seen => alignmentRecord seen) <|
      branch (fun r => r.1.isSome)
        (push 2 (fun r => r.1.getD (Sum.inl none)) <| load (fun _ => alignmentClear) (goto (fun _ => 1)))
        (load (fun _ => alignmentClear) (goto (fun _ => 2)))
  else if label = 2 then
    pop 2 (fun _ seen => alignmentRecord seen) <| pop 0 (fun r seen => (r.1,seen)) <|
      branch (fun r => r.1.isSome || r.2.isSome)
        (push 1 (fun r => Sum.inr ((r.1.bind alignmentBit).getD false,(r.2.bind alignmentBit).getD false)) <|
          load (fun _ => alignmentClear) (goto (fun _ => 2)))
        (load (fun _ => alignmentClear) (goto (fun _ => 3)))
  else
    pop 1 (fun _ seen => alignmentRecord seen) <|
      branch (fun r => r.1.isSome)
        (push 0 (fun r => r.1.getD (Sum.inl none)) <| load (fun _ => alignmentClear) (goto (fun _ => 3)))
        (load (fun _ => alignmentClear) halt)

/-- Move the left word to a work stack in order. Align corresponding
digits until both operands are exhausted and restore the pairs in order. -/
abbrev steinerBinaryAlignmentMachine : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 0
  Γ _ := SteinerAlignmentSymbol
  Λ := Fin 4
  main := 0
  σ := AlignmentRegisters
  initialState := alignmentClear
  m := alignmentProgram

/-- A plain word uses one tagged input symbol per bit. -/
def encodeSteinerAlignmentWord (word : List Bool) : List SteinerAlignmentSymbol :=
  word.map fun bit => Sum.inl (some bit)

/-- Separate the two low-bit-first operands with a divider. -/
def encodeSteinerAlignmentOperands (operands : List Bool × List Bool) : List SteinerAlignmentSymbol :=
  encodeSteinerAlignmentWord operands.1 ++ Sum.inl none :: encodeSteinerAlignmentWord operands.2

/-- Output the aligned pairs with a tag reserved for paired digits. -/
def encodeSteinerAlignedDigits (digits : List (Bool × Bool)) : List SteinerAlignmentSymbol :=
  digits.map Sum.inr

def steinerBinaryAlignmentAnswer (operands : List Bool × List Bool) : List (Bool × Bool) :=
  alignBinaryDigits operands.1 operands.2

/-- The result has exactly the width of the longer operand. -/
theorem steinerBinaryAlignmentAnswer_length (operands : List Bool × List Bool) :
    (steinerBinaryAlignmentAnswer operands).length = max operands.1.length operands.2.length := by
  rcases operands with ⟨left,right⟩
  change (alignBinaryDigits left right).length = max left.length right.length
  induction left generalizing right with
  | nil => simp [alignBinaryDigits]
  | cons bit left ih =>
    cases right with
    | nil => simp [alignBinaryDigits]
    | cons other right =>
      have former := ih right
      simp only [alignBinaryDigits,List.zipWithAll_cons_cons,List.length_cons] at former ⊢
      omega

private def alignCfg (label : Option (Fin 4)) (input buffer left : List SteinerAlignmentSymbol) :
    steinerBinaryAlignmentMachine.Cfg where
  l := label
  var := alignmentClear
  stk := ![input,buffer,left]

private theorem alignStack_input (input buffer left next : List SteinerAlignmentSymbol) :
    Function.update (![input,buffer,left] : Fin 3 → List SteinerAlignmentSymbol) 0 next =
      ![next,buffer,left] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem alignStack_buffer (input buffer left next : List SteinerAlignmentSymbol) :
    Function.update (![input,buffer,left] : Fin 3 → List SteinerAlignmentSymbol) 1 next =
      ![input,next,left] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem alignStack_left (input buffer left next : List SteinerAlignmentSymbol) :
    Function.update (![input,buffer,left] : Fin 3 → List SteinerAlignmentSymbol) 2 next =
      ![input,buffer,next] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem align_collect_bit (bit : Bool) (tail buffer : List SteinerAlignmentSymbol) :
    steinerBinaryAlignmentMachine.step (alignCfg (some 0) (Sum.inl (some bit)::tail) buffer []) =
      some (alignCfg (some 0) tail (Sum.inl (some bit)::buffer) []) := by
  simp [FinTM2.step,steinerBinaryAlignmentMachine,alignCfg,Turing.TM2.step,Turing.TM2.stepAux,
    alignmentProgram,alignmentRecord,alignmentBit,alignStack_input,alignStack_buffer]
  rfl

private theorem align_collect_done (right buffer : List SteinerAlignmentSymbol) :
    steinerBinaryAlignmentMachine.step (alignCfg (some 0) (Sum.inl none::right) buffer []) =
      some (alignCfg (some 1) right buffer []) := by
  simp [FinTM2.step,steinerBinaryAlignmentMachine,alignCfg,Turing.TM2.step,Turing.TM2.stepAux,
    alignmentProgram,alignmentRecord,alignmentBit,alignStack_input]
  rfl

private theorem align_restore_left (head : SteinerAlignmentSymbol)
    (right buffer left : List SteinerAlignmentSymbol) :
    steinerBinaryAlignmentMachine.step (alignCfg (some 1) right (head::buffer) left) =
      some (alignCfg (some 1) right buffer (head::left)) := by
  simp [FinTM2.step,steinerBinaryAlignmentMachine,alignCfg,Turing.TM2.step,Turing.TM2.stepAux,
    alignmentProgram,alignmentRecord,alignStack_buffer,alignStack_left]
  rfl

private theorem align_restore_left_done (right left : List SteinerAlignmentSymbol) :
    steinerBinaryAlignmentMachine.step (alignCfg (some 1) right [] left) =
      some (alignCfg (some 2) right [] left) := by
  simp [FinTM2.step,steinerBinaryAlignmentMachine,alignCfg,Turing.TM2.step,Turing.TM2.stepAux,
    alignmentProgram,alignmentRecord,alignStack_buffer]
  rfl

private theorem align_pair_step {left right : List Bool} (nonempty : ¬ (left = [] ∧ right = []))
    (buffer : List SteinerAlignmentSymbol) :
    steinerBinaryAlignmentMachine.step
      (alignCfg (some 2) (encodeSteinerAlignmentWord right) buffer (encodeSteinerAlignmentWord left)) =
      some (alignCfg (some 2) (encodeSteinerAlignmentWord right.tail)
        (Sum.inr (left.headD false,right.headD false)::buffer) (encodeSteinerAlignmentWord left.tail)) := by
  cases left <;> cases right
  · exact (nonempty ⟨rfl,rfl⟩).elim
  all_goals
    simp [FinTM2.step,steinerBinaryAlignmentMachine,alignCfg,Turing.TM2.step,Turing.TM2.stepAux,
      alignmentProgram,alignmentRecord,alignmentBit,encodeSteinerAlignmentWord,
      alignStack_input,alignStack_buffer,alignStack_left]
    rfl

private theorem align_pair_done (buffer : List SteinerAlignmentSymbol) :
    steinerBinaryAlignmentMachine.step (alignCfg (some 2) [] buffer []) =
      some (alignCfg (some 3) [] buffer []) := by
  simp [FinTM2.step,steinerBinaryAlignmentMachine,alignCfg,Turing.TM2.step,Turing.TM2.stepAux,
    alignmentProgram,alignmentRecord,alignStack_input,alignStack_left]
  rfl

private theorem align_restore_pair (head : SteinerAlignmentSymbol)
    (buffer out : List SteinerAlignmentSymbol) :
    steinerBinaryAlignmentMachine.step (alignCfg (some 3) out (head::buffer) []) =
      some (alignCfg (some 3) (head::out) buffer []) := by
  simp [FinTM2.step,steinerBinaryAlignmentMachine,alignCfg,Turing.TM2.step,Turing.TM2.stepAux,
    alignmentProgram,alignmentRecord,alignStack_input,alignStack_buffer]
  rfl

private theorem align_halt (out : List SteinerAlignmentSymbol) :
    steinerBinaryAlignmentMachine.step (alignCfg (some 3) out [] []) = some (alignCfg none out [] []) := by
  simp [FinTM2.step,steinerBinaryAlignmentMachine,alignCfg,Turing.TM2.step,Turing.TM2.stepAux,
    alignmentProgram,alignmentRecord,alignStack_buffer]
  rfl

private def align_one {a b : steinerBinaryAlignmentMachine.Cfg}
    (step : steinerBinaryAlignmentMachine.step a = some b) :
    EvalsToInTime steinerBinaryAlignmentMachine.step a (some b) 1 where
  steps := 1
  evals_in_steps := by change steinerBinaryAlignmentMachine.step a = some b; exact step
  steps_le_m := le_rfl

private def align_collect (left : List Bool) (right buffer : List SteinerAlignmentSymbol) :
    EvalsToInTime steinerBinaryAlignmentMachine.step
      (alignCfg (some 0) (encodeSteinerAlignmentWord left ++ Sum.inl none :: right) buffer [])
      (some (alignCfg (some 1) right ((encodeSteinerAlignmentWord left).reverse++buffer) []))
      (left.length+1) := by
  induction left generalizing buffer with
  | nil => exact align_one (align_collect_done right buffer)
  | cons bit left ih =>
    have first := align_one (align_collect_bit bit (encodeSteinerAlignmentWord left ++ Sum.inl none :: right) buffer)
    have both := EvalsToInTime.trans _ _ _ _ _ _ first (ih (Sum.inl (some bit)::buffer))
    simpa only [encodeSteinerAlignmentWord,List.map_cons,List.cons_append,List.reverse_cons,List.append_assoc,
      List.singleton_append,List.nil_append,List.length_cons] using both

private def align_restore_operand (buffer right left : List SteinerAlignmentSymbol) :
    EvalsToInTime steinerBinaryAlignmentMachine.step
      (alignCfg (some 1) right buffer left)
      (some (alignCfg (some 2) right [] (buffer.reverse++left))) (buffer.length+1) := by
  induction buffer generalizing left with
  | nil => exact align_one (align_restore_left_done right left)
  | cons head buffer ih =>
    have first := align_one (align_restore_left head right buffer left)
    have both := EvalsToInTime.trans _ _ _ _ _ _ first (ih (head::left))
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using both

private def align_zip (left right : List Bool) (buffer : List SteinerAlignmentSymbol) :
    EvalsToInTime steinerBinaryAlignmentMachine.step
      (alignCfg (some 2) (encodeSteinerAlignmentWord right) buffer (encodeSteinerAlignmentWord left))
      (some (alignCfg (some 3) []
        ((encodeSteinerAlignedDigits (alignBinaryDigits left right)).reverse ++ buffer) []))
      ((alignBinaryDigits left right).length+1) := by
  by_cases empty : left = [] ∧ right = []
  · obtain ⟨rfl,rfl⟩ := empty
    exact align_one (align_pair_done buffer)
  have first := align_one (align_pair_step empty buffer)
  have later := align_zip left.tail right.tail (Sum.inr (left.headD false,right.headD false)::buffer)
  have both := EvalsToInTime.trans _ _ _ _ _ _ first later
  rw [alignBinaryDigits_cons empty]
  simpa only [encodeSteinerAlignedDigits,List.map_cons,List.length_cons,List.reverse_cons,List.append_assoc,
    List.singleton_append] using both
termination_by left.length+right.length
decreasing_by
  simp_wf
  have nonzero : ¬ (left.length = 0 ∧ right.length = 0) := by
    simpa only [List.length_eq_zero_iff] using empty
  omega

private def align_finish (buffer out : List SteinerAlignmentSymbol) :
    EvalsToInTime steinerBinaryAlignmentMachine.step
      (alignCfg (some 3) out buffer []) (some (alignCfg none (buffer.reverse++out) [] []))
      (buffer.length+1) := by
  induction buffer generalizing out with
  | nil => exact align_one (align_halt out)
  | cons head buffer ih =>
    have first := align_one (align_restore_pair head buffer out)
    have both := EvalsToInTime.trans _ _ _ _ _ _ first (ih (head::out))
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using both

private theorem align_machine_init (tape : List SteinerAlignmentSymbol) :
    initList steinerBinaryAlignmentMachine tape = alignCfg (some 0) tape [] [] := by
  unfold initList alignCfg
  apply congrArg (fun stk : Fin 3 → List SteinerAlignmentSymbol =>
    (⟨some 0,alignmentClear,stk⟩ : steinerBinaryAlignmentMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem align_machine_halt (out : List SteinerAlignmentSymbol) :
    haltList steinerBinaryAlignmentMachine out = alignCfg none out [] [] := by
  unfold haltList alignCfg
  apply congrArg (fun stk : Fin 3 → List SteinerAlignmentSymbol =>
    (⟨none,alignmentClear,stk⟩ : steinerBinaryAlignmentMachine.Cfg))
  funext i
  fin_cases i <;> rfl

/-- The machine produces the exact padded digit list. Its transition
bound counts two passes through the left word and two through the pairs. -/
def steinerBinaryAlignmentMachine_run (operands : List Bool × List Bool) :
    TM2OutputsInTime steinerBinaryAlignmentMachine (encodeSteinerAlignmentOperands operands)
      (some (encodeSteinerAlignedDigits (steinerBinaryAlignmentAnswer operands)))
      (2*operands.1.length+2*(steinerBinaryAlignmentAnswer operands).length+4) := by
  rcases operands with ⟨left,right⟩
  let leftWord := encodeSteinerAlignmentWord left
  let rightWord := encodeSteinerAlignmentWord right
  let digits := alignBinaryDigits left right
  let result := encodeSteinerAlignedDigits digits
  have collect := align_collect left rightWord []
  rw [List.append_nil] at collect
  have restore := align_restore_operand leftWord.reverse rightWord []
  rw [List.reverse_reverse,List.append_nil,List.length_reverse] at restore
  have zip := align_zip left right []
  rw [List.append_nil] at zip
  have finish := align_finish result.reverse []
  rw [List.reverse_reverse,List.append_nil,List.length_reverse] at finish
  have start := EvalsToInTime.trans _ _ _ _ _ _ collect restore
  have through := EvalsToInTime.trans _ _ _ _ _ _ start zip
  have all := EvalsToInTime.trans _ _ _ _ _ _ through finish
  have leftLength : leftWord.length = left.length := by simp [leftWord,encodeSteinerAlignmentWord]
  have resultLength : result.length = digits.length := by simp [result,encodeSteinerAlignedDigits]
  change EvalsToInTime steinerBinaryAlignmentMachine.step _ (some (haltList steinerBinaryAlignmentMachine _)) _
  rw [align_machine_init,align_machine_halt]
  exact ⟨all.toEvalsTo,by
    have enough := all.steps_le_m
    have alignedLength : (alignBinaryDigits left right).length = digits.length := rfl
    change all.steps ≤ 2*left.length+2*digits.length+4
    omega⟩

/-- Alignment is linear in the sum of the two raw word lengths plus
the divider, including when one or both words are empty. -/
noncomputable def steinerBinaryAlignmentMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerAlignmentOperands encodeSteinerAlignedDigits steinerBinaryAlignmentAnswer where
  tm := steinerBinaryAlignmentMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 4*Polynomial.X
  outputsFun operands := by
    have run := steinerBinaryAlignmentMachine_run operands
    have aligned := alignBinaryDigits_length_le operands.1 operands.2
    have length : (encodeSteinerAlignmentOperands operands).length = operands.1.length+operands.2.length+1 := by
      simp only [encodeSteinerAlignmentOperands,encodeSteinerAlignmentWord,List.length_append,List.length_cons,List.length_map]
      omega
    have enough : 2*operands.1.length+2*(steinerBinaryAlignmentAnswer operands).length+4 ≤
        (Polynomial.C 4*Polynomial.X).eval (encodeSteinerAlignmentOperands operands).length := by
      simp only [steinerBinaryAlignmentAnswer,Polynomial.eval_C_mul,Polynomial.eval_X,length]
      omega
    change TM2OutputsInTime steinerBinaryAlignmentMachine ((encodeSteinerAlignmentOperands operands).map id)
      (some ((encodeSteinerAlignedDigits (steinerBinaryAlignmentAnswer operands)).map id)) _
    simpa only [List.map_id_fun,id_eq] using
      (show TM2OutputsInTime steinerBinaryAlignmentMachine (encodeSteinerAlignmentOperands operands)
        (some (encodeSteinerAlignedDigits (steinerBinaryAlignmentAnswer operands))) _ from
          ⟨run.toEvalsTo,run.steps_le_m.trans enough⟩)

end OnlineReachabilityPreservers
