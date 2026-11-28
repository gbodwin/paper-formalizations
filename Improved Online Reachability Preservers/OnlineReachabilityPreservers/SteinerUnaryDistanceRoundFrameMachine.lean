import OnlineReachabilityPreservers.SteinerUnarySharedCapRowsMachine

/-! Pair each distance row with a single stored previous weight vector. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private abbrev RoundFrameSymbol := SteinerUnaryCappedRowsSymbol

private inductive RoundFrameLabel where
  | bound
  | savePrior
  | restorePrior
  | read
  | distance
  | prior
  | clearPrior
  | finish
  deriving DecidableEq

private instance : Fintype RoundFrameLabel where
  elems := {.bound,.savePrior,.restorePrior,.read,.distance,.prior,.clearPrior,.finish}
  complete label := by cases label <;> decide

private abbrev RoundFrameRegister := Option RoundFrameSymbol
private abbrev RoundFrameProgram := StackMachineTag.Program (Fin 4) RoundFrameSymbol RoundFrameLabel RoundFrameRegister

private def roundFrameTally : RoundFrameSymbol := Sum.inr (some true)
private def roundFrameField : RoundFrameSymbol := Sum.inr none
private def roundFrameCell : RoundFrameSymbol := Sum.inl false
private def roundFrameRow : RoundFrameSymbol := Sum.inl true

private def roundFrameObserve (_ : RoundFrameRegister) (seen : Option RoundFrameSymbol) : RoundFrameRegister := seen
private def roundFrameSeen (seen : RoundFrameRegister) : RoundFrameSymbol := seen.getD roundFrameCell

private def roundFrameNext (label : RoundFrameLabel) : RoundFrameProgram :=
  load (fun _ => none) (goto (fun _ => label))

private def roundFrameProgram : RoundFrameLabel → RoundFrameProgram
  | .bound =>
    pop 2 roundFrameObserve <|
      push 3 roundFrameSeen <|
        branch (fun r => r == some roundFrameCell) (roundFrameNext .savePrior) (roundFrameNext .bound)
  | .savePrior =>
    pop 2 roundFrameObserve <|
      branch (fun r => r == some roundFrameCell) (roundFrameNext .restorePrior)
        (push 0 roundFrameSeen (roundFrameNext .savePrior))
  | .restorePrior =>
    pop 0 roundFrameObserve <|
      branch Option.isSome
        (push 1 roundFrameSeen (roundFrameNext .restorePrior))
        (roundFrameNext .read)
  | .read =>
    peek 2 roundFrameObserve <|
      branch Option.isSome
        (branch (fun r => r == some roundFrameRow)
          (pop 2 roundFrameObserve <|
            push 3 (fun _ => roundFrameRow) (roundFrameNext .restorePrior))
          (roundFrameNext .distance))
        (roundFrameNext .clearPrior)
  | .distance =>
    pop 2 roundFrameObserve <|
      push 3 roundFrameSeen <|
        branch (fun r => r == some roundFrameField) (roundFrameNext .prior) (roundFrameNext .distance)
  | .prior =>
    pop 1 roundFrameObserve <|
      push 0 roundFrameSeen <|
        branch (fun r => r == some roundFrameField)
          (push 3 (fun _ => roundFrameCell) (roundFrameNext .read))
          (push 3 roundFrameSeen (roundFrameNext .prior))
  | .clearPrior =>
    pop 1 roundFrameObserve <|
      branch Option.isSome (roundFrameNext .clearPrior) (roundFrameNext .finish)
  | .finish =>
    pop 3 roundFrameObserve <|
      branch Option.isSome
        (push 2 roundFrameSeen (roundFrameNext .finish))
        (load (fun _ => none) halt)

/-- Copy a shared cap and zip each matrix row with the stored prior
vector. Restore the prior vector at every row boundary. -/
abbrev steinerUnaryDistanceRoundFrameMachine : FinTM2 where
  K := Fin 4
  k₀ := 2
  k₁ := 2
  Γ _ := RoundFrameSymbol
  Λ := RoundFrameLabel
  main := .bound
  σ := RoundFrameRegister
  initialState := none
  m := roundFrameProgram

private def roundFrameCfg (label : Option RoundFrameLabel) (backup prior input output : List RoundFrameSymbol) :
    steinerUnaryDistanceRoundFrameMachine.Cfg where
  l := label
  var := none
  stk := ![backup,prior,input,output]

private theorem roundFrame_update0 (a v i o w : List RoundFrameSymbol) :
    Function.update (![a,v,i,o] : Fin 4 → List RoundFrameSymbol) 0 w = ![w,v,i,o] := by
  funext slot
  fin_cases slot <;> simp [Function.update]

private theorem roundFrame_update1 (a v i o w : List RoundFrameSymbol) :
    Function.update (![a,v,i,o] : Fin 4 → List RoundFrameSymbol) 1 w = ![a,w,i,o] := by
  funext slot
  fin_cases slot <;> simp [Function.update]

private theorem roundFrame_update2 (a v i o w : List RoundFrameSymbol) :
    Function.update (![a,v,i,o] : Fin 4 → List RoundFrameSymbol) 2 w = ![a,v,w,o] := by
  funext slot
  fin_cases slot <;> simp [Function.update]

private theorem roundFrame_update3 (a v i o w : List RoundFrameSymbol) :
    Function.update (![a,v,i,o] : Fin 4 → List RoundFrameSymbol) 3 w = ![a,v,i,w] := by
  funext slot
  fin_cases slot <;> simp [Function.update]

private def roundFrame_one {a b : steinerUnaryDistanceRoundFrameMachine.Cfg}
    (move : steinerUnaryDistanceRoundFrameMachine.step a = some b) :
    EvalsToInTime steinerUnaryDistanceRoundFrameMachine.step a (some b) 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := move

private def roundFrameTallies (n : ℕ) : List RoundFrameSymbol := List.replicate n roundFrameTally

private theorem roundFrameTallies_push (n : ℕ) (tail : List RoundFrameSymbol) :
    roundFrameTallies n++roundFrameTally::tail = roundFrameTallies (n+1)++tail := by
  simp only [roundFrameTallies,List.replicate_add,List.replicate_one,List.append_assoc,List.singleton_append]

private theorem roundFrame_boundTally (i o : List RoundFrameSymbol) :
    steinerUnaryDistanceRoundFrameMachine.step (roundFrameCfg (some .bound) [] [] (roundFrameTally::i) o) =
      some (roundFrameCfg (some .bound) [] [] i (roundFrameTally::o)) := by
  simp [FinTM2.step,steinerUnaryDistanceRoundFrameMachine,roundFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    roundFrameProgram,roundFrameObserve,roundFrameNext,roundFrameSeen,roundFrameCell,roundFrameTally,
    roundFrame_update2,roundFrame_update3]
  rfl

private theorem roundFrame_boundEnd (i o : List RoundFrameSymbol) :
    steinerUnaryDistanceRoundFrameMachine.step (roundFrameCfg (some .bound) [] [] (roundFrameCell::i) o) =
      some (roundFrameCfg (some .savePrior) [] [] i (roundFrameCell::o)) := by
  simp [FinTM2.step,steinerUnaryDistanceRoundFrameMachine,roundFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    roundFrameProgram,roundFrameObserve,roundFrameNext,roundFrameSeen,roundFrame_update2,roundFrame_update3]
  rfl

private def roundFrame_bound (n : ℕ) (i o : List RoundFrameSymbol) :
    EvalsToInTime steinerUnaryDistanceRoundFrameMachine.step
      (roundFrameCfg (some .bound) [] [] (roundFrameTallies n++roundFrameCell::i) o)
      (some (roundFrameCfg (some .savePrior) [] [] i (roundFrameCell::(roundFrameTallies n++o)))) (n+1) := by
  induction n generalizing o with
  | zero => exact roundFrame_one (roundFrame_boundEnd i o)
  | succ n ih =>
    have all := EvalsToInTime.trans _ _ _ _ _ _
      (roundFrame_one (roundFrame_boundTally (roundFrameTallies n++roundFrameCell::i) o)) (ih (roundFrameTally::o))
    rw [roundFrameTallies_push] at all
    exact all

private theorem roundFrame_saveSymbol (symbol : Option Bool) (a i o : List RoundFrameSymbol) :
    steinerUnaryDistanceRoundFrameMachine.step (roundFrameCfg (some .savePrior) a [] (Sum.inr symbol::i) o) =
      some (roundFrameCfg (some .savePrior) (Sum.inr symbol::a) [] i o) := by
  simp [FinTM2.step,steinerUnaryDistanceRoundFrameMachine,roundFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    roundFrameProgram,roundFrameObserve,roundFrameNext,roundFrameSeen,roundFrameCell,roundFrame_update0,roundFrame_update2]
  rfl

private theorem roundFrame_saveEnd (a i o : List RoundFrameSymbol) :
    steinerUnaryDistanceRoundFrameMachine.step (roundFrameCfg (some .savePrior) a [] (roundFrameCell::i) o) =
      some (roundFrameCfg (some .restorePrior) a [] i o) := by
  simp [FinTM2.step,steinerUnaryDistanceRoundFrameMachine,roundFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    roundFrameProgram,roundFrameObserve,roundFrameNext,roundFrame_update2]
  rfl

private def roundFrame_save (word : List (Option Bool)) (a i o : List RoundFrameSymbol) :
    EvalsToInTime steinerUnaryDistanceRoundFrameMachine.step
      (roundFrameCfg (some .savePrior) a [] (word.map Sum.inr++roundFrameCell::i) o)
      (some (roundFrameCfg (some .restorePrior) ((word.map Sum.inr).reverse++a) [] i o)) (word.length+1) := by
  induction word generalizing a with
  | nil => exact roundFrame_one (roundFrame_saveEnd a i o)
  | cons symbol word ih =>
    have all := EvalsToInTime.trans _ _ _ _ _ _
      (roundFrame_one (roundFrame_saveSymbol symbol a (word.map Sum.inr++roundFrameCell::i) o)) (ih (Sum.inr symbol::a))
    simpa only [List.map_cons,List.cons_append,List.reverse_cons,List.length_cons,List.append_assoc,List.singleton_append,
      List.nil_append] using all

private theorem roundFrame_restoreSymbol (symbol : RoundFrameSymbol) (a v i o : List RoundFrameSymbol) :
    steinerUnaryDistanceRoundFrameMachine.step (roundFrameCfg (some .restorePrior) (symbol::a) v i o) =
      some (roundFrameCfg (some .restorePrior) a (symbol::v) i o) := by
  simp [FinTM2.step,steinerUnaryDistanceRoundFrameMachine,roundFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    roundFrameProgram,roundFrameObserve,roundFrameNext,roundFrameSeen,roundFrame_update0,roundFrame_update1]
  rfl

private theorem roundFrame_restoreEnd (v i o : List RoundFrameSymbol) :
    steinerUnaryDistanceRoundFrameMachine.step (roundFrameCfg (some .restorePrior) [] v i o) =
      some (roundFrameCfg (some .read) [] v i o) := by
  simp [FinTM2.step,steinerUnaryDistanceRoundFrameMachine,roundFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    roundFrameProgram,roundFrameObserve,roundFrameNext,roundFrame_update0]
  rfl

private def roundFrame_restore (a v i o : List RoundFrameSymbol) :
    EvalsToInTime steinerUnaryDistanceRoundFrameMachine.step (roundFrameCfg (some .restorePrior) a v i o)
      (some (roundFrameCfg (some .read) [] (a.reverse++v) i o)) (a.length+1) := by
  induction a generalizing v with
  | nil => exact roundFrame_one (roundFrame_restoreEnd v i o)
  | cons symbol a ih =>
    have all := EvalsToInTime.trans _ _ _ _ _ _
      (roundFrame_one (roundFrame_restoreSymbol symbol a v i o)) (ih (symbol::v))
    simpa only [List.reverse_cons,List.length_cons,List.append_assoc,List.singleton_append] using all

private theorem roundFrame_startDistance (symbol : Option Bool) (a v i o : List RoundFrameSymbol) :
    steinerUnaryDistanceRoundFrameMachine.step (roundFrameCfg (some .read) a v (Sum.inr symbol::i) o) =
      some (roundFrameCfg (some .distance) a v (Sum.inr symbol::i) o) := by
  simp [FinTM2.step,steinerUnaryDistanceRoundFrameMachine,roundFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    roundFrameProgram,roundFrameObserve,roundFrameNext,roundFrameRow]
  rfl

private theorem roundFrame_distanceTally (a v i o : List RoundFrameSymbol) :
    steinerUnaryDistanceRoundFrameMachine.step (roundFrameCfg (some .distance) a v (roundFrameTally::i) o) =
      some (roundFrameCfg (some .distance) a v i (roundFrameTally::o)) := by
  simp [FinTM2.step,steinerUnaryDistanceRoundFrameMachine,roundFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    roundFrameProgram,roundFrameObserve,roundFrameSeen,roundFrameNext,roundFrameField,roundFrameTally,
    roundFrame_update2,roundFrame_update3]
  rfl

private theorem roundFrame_distanceEnd (a v i o : List RoundFrameSymbol) :
    steinerUnaryDistanceRoundFrameMachine.step (roundFrameCfg (some .distance) a v (roundFrameField::i) o) =
      some (roundFrameCfg (some .prior) a v i (roundFrameField::o)) := by
  simp [FinTM2.step,steinerUnaryDistanceRoundFrameMachine,roundFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    roundFrameProgram,roundFrameObserve,roundFrameSeen,roundFrameNext,roundFrame_update2,roundFrame_update3]
  rfl

private def roundFrame_distance (d : ℕ) (a v i o : List RoundFrameSymbol) :
    EvalsToInTime steinerUnaryDistanceRoundFrameMachine.step
      (roundFrameCfg (some .distance) a v (roundFrameTallies d++roundFrameField::i) o)
      (some (roundFrameCfg (some .prior) a v i (roundFrameField::(roundFrameTallies d++o)))) (d+1) := by
  induction d generalizing o with
  | zero => exact roundFrame_one (roundFrame_distanceEnd a v i o)
  | succ d ih =>
    have all := EvalsToInTime.trans _ _ _ _ _ _
      (roundFrame_one (roundFrame_distanceTally a v (roundFrameTallies d++roundFrameField::i) o))
      (ih (roundFrameTally::o))
    rw [roundFrameTallies_push] at all
    exact all

private theorem roundFrame_priorTally (a v i o : List RoundFrameSymbol) :
    steinerUnaryDistanceRoundFrameMachine.step (roundFrameCfg (some .prior) a (roundFrameTally::v) i o) =
      some (roundFrameCfg (some .prior) (roundFrameTally::a) v i (roundFrameTally::o)) := by
  simp [FinTM2.step,steinerUnaryDistanceRoundFrameMachine,roundFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    roundFrameProgram,roundFrameObserve,roundFrameSeen,roundFrameNext,roundFrameField,roundFrameTally,
    roundFrame_update0,roundFrame_update1,roundFrame_update3]
  rfl

private theorem roundFrame_priorEnd (a v i o : List RoundFrameSymbol) :
    steinerUnaryDistanceRoundFrameMachine.step (roundFrameCfg (some .prior) a (roundFrameField::v) i o) =
      some (roundFrameCfg (some .read) (roundFrameField::a) v i (roundFrameCell::o)) := by
  simp [FinTM2.step,steinerUnaryDistanceRoundFrameMachine,roundFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    roundFrameProgram,roundFrameObserve,roundFrameSeen,roundFrameNext,roundFrame_update0,roundFrame_update1,roundFrame_update3]
  rfl

private def roundFrame_prior (s : ℕ) (a v i o : List RoundFrameSymbol) :
    EvalsToInTime steinerUnaryDistanceRoundFrameMachine.step
      (roundFrameCfg (some .prior) a (roundFrameTallies s++roundFrameField::v) i o)
      (some (roundFrameCfg (some .read) (roundFrameField::(roundFrameTallies s++a)) v i
        (roundFrameCell::(roundFrameTallies s++o)))) (s+1) := by
  induction s generalizing a o with
  | zero => exact roundFrame_one (roundFrame_priorEnd a v i o)
  | succ s ih =>
    have all := EvalsToInTime.trans _ _ _ _ _ _
      (roundFrame_one (roundFrame_priorTally a (roundFrameTallies s++roundFrameField::v) i o))
      (ih (roundFrameTally::a) (roundFrameTally::o))
    rw [roundFrameTallies_push,roundFrameTallies_push] at all
    exact all

private def roundFrameFieldPayload (value : ℕ) : List (Option Bool) := List.replicate value (some true)++[none]
private def roundFrameFields (values : List ℕ) : List RoundFrameSymbol :=
  (values.flatMap roundFrameFieldPayload).map Sum.inr

private theorem roundFrame_fields_cons (value : ℕ) (tail : List ℕ) :
    roundFrameFields (value::tail) = roundFrameTallies value++roundFrameField::roundFrameFields tail := by
  simp only [roundFrameFields,roundFrameFieldPayload,List.flatMap_cons,List.map_append,List.map_replicate,
    List.map_cons,List.append_assoc,List.singleton_append,roundFrameTallies,roundFrameTally,roundFrameField]

private def roundFramePair (cell : ℕ × ℕ) : List RoundFrameSymbol :=
  (List.replicate cell.1 (some true)++none::List.replicate cell.2 (some true)).map Sum.inr++[roundFrameCell]

private def roundFramePairedRow (pairs : List (ℕ × ℕ)) : List RoundFrameSymbol := pairs.flatMap roundFramePair

private def roundFrameRows (rows : List (List ℕ)) : List RoundFrameSymbol :=
  rows.flatMap fun row => roundFrameFields row++[roundFrameRow]

private def roundFramePairedRows (rows : List (List (ℕ × ℕ))) : List RoundFrameSymbol :=
  rows.flatMap fun row => roundFramePairedRow row++[roundFrameRow]

private theorem roundFrame_pair_shape (d s : ℕ) :
    roundFramePair (d,s) = roundFrameTallies d++roundFrameField::(roundFrameTallies s++[roundFrameCell]) := by
  simp only [roundFramePair,roundFrameTallies,roundFrameTally,roundFrameField,List.map_append,List.map_replicate,
    List.map_cons,List.append_assoc,List.cons_append]

private theorem roundFrame_pair_length (d s : ℕ) : (roundFramePair (d,s)).length = d+s+2 := by
  rw [roundFrame_pair_shape]
  simp only [roundFrameTallies,List.length_append,List.length_replicate,List.length_cons,List.length_nil]
  omega

private def roundFrame_processPair (d s : ℕ) (a v i o : List RoundFrameSymbol) :
    EvalsToInTime steinerUnaryDistanceRoundFrameMachine.step
      (roundFrameCfg (some .read) a (roundFrameTallies s++roundFrameField::v)
        (roundFrameTallies d++roundFrameField::i) o)
      (some (roundFrameCfg (some .read) (roundFrameField::(roundFrameTallies s++a)) v i
        ((roundFramePair (d,s)).reverse++o))) (2*(roundFramePair (d,s)).length) := by
  have started : EvalsToInTime steinerUnaryDistanceRoundFrameMachine.step
      (roundFrameCfg (some .read) a (roundFrameTallies s++roundFrameField::v)
        (roundFrameTallies d++roundFrameField::i) o)
      (some (roundFrameCfg (some .distance) a (roundFrameTallies s++roundFrameField::v)
        (roundFrameTallies d++roundFrameField::i) o)) 1 := by
    cases d with
    | zero => exact roundFrame_one (roundFrame_startDistance none a _ i o)
    | succ d => exact roundFrame_one (roundFrame_startDistance (some true) a _
        (roundFrameTallies d++roundFrameField::i) o)
  have transferred := EvalsToInTime.trans _ _ _ _ _ _ started
    (roundFrame_distance d a (roundFrameTallies s++roundFrameField::v) i o)
  have all := EvalsToInTime.trans _ _ _ _ _ _ transferred
    (roundFrame_prior s a v i (roundFrameField::(roundFrameTallies d++o)))
  rw [roundFrame_pair_length,roundFrame_pair_shape]
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,roundFrameTallies,List.reverse_replicate,
    List.append_assoc,List.nil_append,List.cons_append]
  refine ⟨all.toEvalsTo,?_⟩
  have paid := all.steps_le_m
  omega

private def roundFrame_processPairs (ds vs : List ℕ) (same : ds.length = vs.length)
    (a i o : List RoundFrameSymbol) :
    EvalsToInTime steinerUnaryDistanceRoundFrameMachine.step
      (roundFrameCfg (some .read) a (roundFrameFields vs) (roundFrameFields ds++i) o)
      (some (roundFrameCfg (some .read) ((roundFrameFields vs).reverse++a) [] i
        ((roundFramePairedRow (ds.zip vs)).reverse++o))) (2*(roundFramePairedRow (ds.zip vs)).length) := by
  induction ds generalizing vs a o with
  | nil =>
    cases vs with
    | nil => exact ⟨⟨0,rfl⟩,Nat.zero_le _⟩
    | cons s vs => simp at same
  | cons d ds ih =>
    cases vs with
    | nil => simp at same
    | cons s vs =>
      have lengths : ds.length = vs.length := by simpa only [List.length_cons,Nat.succ_inj] using same
      have first := roundFrame_processPair d s a (roundFrameFields vs) (roundFrameFields ds++i) o
      have all := EvalsToInTime.trans _ _ _ _ _ _ first
        (ih vs lengths (roundFrameField::(roundFrameTallies s++a)) ((roundFramePair (d,s)).reverse++o))
      rw [roundFrame_fields_cons,roundFrame_fields_cons]
      simp only [List.append_assoc,List.cons_append,List.reverse_append,List.reverse_cons,roundFrameTallies,
        List.reverse_replicate,roundFramePairedRow,List.zip_cons_cons,List.flatMap_cons,
        List.length_append]
      refine ⟨all.toEvalsTo,?_⟩
      have paid := all.steps_le_m
      change all.steps ≤ 2*(roundFramePairedRow (ds.zip vs)).length+2*(roundFramePair (d,s)).length at paid
      change all.steps ≤ 2*((roundFramePair (d,s)).length+(roundFramePairedRow (ds.zip vs)).length)
      omega

private theorem roundFrame_rowEnd (a i o : List RoundFrameSymbol) :
    steinerUnaryDistanceRoundFrameMachine.step (roundFrameCfg (some .read) a [] (roundFrameRow::i) o) =
      some (roundFrameCfg (some .restorePrior) a [] i (roundFrameRow::o)) := by
  simp [FinTM2.step,steinerUnaryDistanceRoundFrameMachine,roundFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    roundFrameProgram,roundFrameObserve,roundFrameNext,roundFrame_update2,roundFrame_update3]
  rfl

private theorem roundFrame_length_row (ds vs : List ℕ) (same : ds.length = vs.length) :
    (roundFramePairedRow (ds.zip vs)).length = (roundFrameFields ds).length+(roundFrameFields vs).length := by
  induction ds generalizing vs with
  | nil => cases vs <;> simp_all [roundFrameFields,roundFramePairedRow]
  | cons d ds ih =>
    cases vs with
    | nil => simp at same
    | cons s vs =>
      have lengths : ds.length = vs.length := by simpa only [List.length_cons,Nat.succ_inj] using same
      change (roundFramePair (d,s)++roundFramePairedRow (ds.zip vs)).length = _
      rw [roundFrame_fields_cons,roundFrame_fields_cons]
      simp only [List.length_append,List.length_cons,roundFrame_pair_length,roundFrameTallies,List.length_replicate,ih vs lengths]
      omega

private theorem roundFrameRows_cons (row : List ℕ) (rows : List (List ℕ)) :
    roundFrameRows (row::rows) = roundFrameFields row++roundFrameRow::roundFrameRows rows := by
  simp only [roundFrameRows,List.flatMap_cons,List.append_assoc,List.singleton_append]

private theorem roundFramePairedRows_cons (row : List (ℕ × ℕ)) (rows : List (List (ℕ × ℕ))) :
    roundFramePairedRows (row::rows) = roundFramePairedRow row++roundFrameRow::roundFramePairedRows rows := by
  simp only [roundFramePairedRows,List.flatMap_cons,List.append_assoc,List.singleton_append]

private def roundFrame_processRows (rows : List (List ℕ)) (vs : List ℕ)
    (valid : ∀ row ∈ rows, row.length = vs.length) (i o : List RoundFrameSymbol) :
    let totals := roundFramePairedRows (rows.map fun row => row.zip vs)
    EvalsToInTime steinerUnaryDistanceRoundFrameMachine.step
      (roundFrameCfg (some .read) [] (roundFrameFields vs) (roundFrameRows rows++i) o)
      (some (roundFrameCfg (some .read) [] (roundFrameFields vs) i (totals.reverse++o))) (3*totals.length) := by
  induction rows generalizing o with
  | nil => exact ⟨⟨0,rfl⟩,Nat.zero_le _⟩
  | cons row rows ih =>
    let sub := roundFramePairedRow (row.zip vs)
    let later := roundFrameRows rows++i
    have same := valid row List.mem_cons_self
    have here := roundFrame_processPairs row vs same [] (roundFrameRow::later) o
    rw [List.append_nil] at here
    have marked := EvalsToInTime.trans _ _ _ _ _ _ here
      (roundFrame_one (roundFrame_rowEnd (roundFrameFields vs).reverse later (sub.reverse++o)))
    have restored := roundFrame_restore (roundFrameFields vs).reverse [] later (roundFrameRow::(sub.reverse++o))
    simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at restored
    have next := EvalsToInTime.trans _ _ _ _ _ _ marked restored
    have all := EvalsToInTime.trans _ _ _ _ _ _ next
      (ih (fun r member => valid r (List.mem_cons_of_mem _ member)) (roundFrameRow::(sub.reverse++o)))
    dsimp only
    rw [roundFrameRows_cons,List.map_cons,roundFramePairedRows_cons]
    simp only [List.append_assoc,List.cons_append,List.reverse_append,List.reverse_cons,List.length_append,List.length_cons]
    refine ⟨all.toEvalsTo,?_⟩
    have paid := all.steps_le_m
    have prior : (roundFrameFields vs).length ≤ sub.length := by
      change (roundFrameFields vs).length ≤ (roundFramePairedRow (row.zip vs)).length
      rw [roundFrame_length_row row vs same]
      omega
    change all.steps ≤ 3*(roundFramePairedRows (rows.map fun row => row.zip vs)).length+
      ((roundFrameFields vs).length+1+(1+2*sub.length)) at paid
    change all.steps ≤ 3*(sub.length+((roundFramePairedRows (rows.map fun row => row.zip vs)).length+1))
    omega

private theorem roundFrame_readEnd (v o : List RoundFrameSymbol) :
    steinerUnaryDistanceRoundFrameMachine.step (roundFrameCfg (some .read) [] v [] o) =
      some (roundFrameCfg (some .clearPrior) [] v [] o) := by
  simp [FinTM2.step,steinerUnaryDistanceRoundFrameMachine,roundFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    roundFrameProgram,roundFrameObserve,roundFrameNext]
  rfl

private theorem roundFrame_clearSymbol (symbol : RoundFrameSymbol) (v o : List RoundFrameSymbol) :
    steinerUnaryDistanceRoundFrameMachine.step (roundFrameCfg (some .clearPrior) [] (symbol::v) [] o) =
      some (roundFrameCfg (some .clearPrior) [] v [] o) := by
  simp [FinTM2.step,steinerUnaryDistanceRoundFrameMachine,roundFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    roundFrameProgram,roundFrameObserve,roundFrameNext,roundFrame_update1]
  rfl

private theorem roundFrame_clearEnd (o : List RoundFrameSymbol) :
    steinerUnaryDistanceRoundFrameMachine.step (roundFrameCfg (some .clearPrior) [] [] [] o) =
      some (roundFrameCfg (some .finish) [] [] [] o) := by
  simp [FinTM2.step,steinerUnaryDistanceRoundFrameMachine,roundFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    roundFrameProgram,roundFrameObserve,roundFrameNext,roundFrame_update1]
  rfl

private def roundFrame_clear (v o : List RoundFrameSymbol) :
    EvalsToInTime steinerUnaryDistanceRoundFrameMachine.step (roundFrameCfg (some .clearPrior) [] v [] o)
      (some (roundFrameCfg (some .finish) [] [] [] o)) (v.length+1) := by
  induction v with
  | nil => exact roundFrame_one (roundFrame_clearEnd o)
  | cons symbol v ih =>
    exact EvalsToInTime.trans _ _ _ _ _ _ (roundFrame_one (roundFrame_clearSymbol symbol v o)) ih

private theorem roundFrame_finishSymbol (symbol : RoundFrameSymbol) (i o : List RoundFrameSymbol) :
    steinerUnaryDistanceRoundFrameMachine.step (roundFrameCfg (some .finish) [] [] i (symbol::o)) =
      some (roundFrameCfg (some .finish) [] [] (symbol::i) o) := by
  simp [FinTM2.step,steinerUnaryDistanceRoundFrameMachine,roundFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    roundFrameProgram,roundFrameObserve,roundFrameSeen,roundFrameNext,roundFrame_update2,roundFrame_update3]
  rfl

private theorem roundFrame_finishEnd (i : List RoundFrameSymbol) :
    steinerUnaryDistanceRoundFrameMachine.step (roundFrameCfg (some .finish) [] [] i []) =
      some (roundFrameCfg none [] [] i []) := by
  simp [FinTM2.step,steinerUnaryDistanceRoundFrameMachine,roundFrameCfg,Turing.TM2.step,Turing.TM2.stepAux,
    roundFrameProgram,roundFrameObserve,roundFrame_update3]
  rfl

private def roundFrame_finish (i o : List RoundFrameSymbol) :
    EvalsToInTime steinerUnaryDistanceRoundFrameMachine.step (roundFrameCfg (some .finish) [] [] i o)
      (some (roundFrameCfg none [] [] (o.reverse++i) [])) (o.length+1) := by
  induction o generalizing i with
  | nil => exact roundFrame_one (roundFrame_finishEnd i)
  | cons symbol o ih =>
    have all := EvalsToInTime.trans _ _ _ _ _ _
      (roundFrame_one (roundFrame_finishSymbol symbol i o)) (ih (symbol::i))
    simpa only [List.reverse_cons,List.length_cons,List.append_assoc,List.singleton_append] using all

/-- Each distance row has one entry for every previously rooted weight. -/
structure SteinerUnaryDistanceRoundRequest where
  cap : ℕ
  columns : ℕ
  prior : Vector ℕ columns
  distances : List (Vector ℕ columns)

private def roundFrameDistLists (request : SteinerUnaryDistanceRoundRequest) : List (List ℕ) :=
  request.distances.map Vector.toList

private theorem roundFrame_rectangular (request : SteinerUnaryDistanceRoundRequest) :
    ∀ row ∈ roundFrameDistLists request, row.length = request.prior.toList.length := by
  intro row present
  change row ∈ request.distances.map Vector.toList at present
  obtain ⟨vector,_,rfl⟩ := List.mem_map.mp present
  simp

/-- The single cap and previous vector precede the ordered distance rows. -/
def encodeSteinerUnaryDistanceRound (request : SteinerUnaryDistanceRoundRequest) : List SteinerUnaryCappedRowsSymbol :=
  roundFrameTallies request.cap++roundFrameCell::(roundFrameFields request.prior.toList++
    roundFrameCell::roundFrameRows (roundFrameDistLists request))

/-- Pair each distance with the prior weight at the same column. -/
def steinerUnaryDistanceRoundPairs (request : SteinerUnaryDistanceRoundRequest) : SteinerUnarySharedCapRows :=
  (request.cap,(roundFrameDistLists request).map fun row => row.zip request.prior.toList)

/-- The resulting frame is the exact input of the shared-cap evaluator. -/
def steinerUnaryDistanceRoundFrameAnswer (request : SteinerUnaryDistanceRoundRequest) :
    List SteinerUnaryCappedRowsSymbol :=
  encodeSteinerUnarySharedCapRows (steinerUnaryDistanceRoundPairs request)

private theorem roundFrame_answer (request : SteinerUnaryDistanceRoundRequest) :
    steinerUnaryDistanceRoundFrameAnswer request = roundFrameTallies request.cap++roundFrameCell::
      roundFramePairedRows ((roundFrameDistLists request).map fun row => row.zip request.prior.toList) := rfl

private theorem roundFrame_paired_size (rows : List (List ℕ)) (v : List ℕ)
    (valid : ∀ row ∈ rows, row.length = v.length) :
    (roundFramePairedRows (rows.map fun row => row.zip v)).length =
      (roundFrameRows rows).length+rows.length*(roundFrameFields v).length := by
  induction rows with
  | nil => simp [roundFrameRows,roundFramePairedRows]
  | cons row rows ih =>
    rw [List.map_cons,roundFramePairedRows_cons,roundFrameRows_cons]
    simp only [List.length_append,List.length_cons,roundFrame_length_row row v (valid row List.mem_cons_self),
      ih (fun r present => valid r (List.mem_cons_of_mem _ present))]
    rw [Nat.succ_mul]
    omega

private theorem roundFrame_dist_rows (rows : List (List ℕ)) : rows.length ≤ (roundFrameRows rows).length := by
  induction rows with
  | nil => exact Nat.zero_le _
  | cons row rows ih =>
    rw [roundFrameRows_cons]
    simp only [List.length_append,List.length_cons]
    omega

private theorem roundFrame_init (word : List RoundFrameSymbol) :
    initList steinerUnaryDistanceRoundFrameMachine word = roundFrameCfg (some .bound) [] [] word [] := by
  apply congrArg (fun stk : Fin 4 → List RoundFrameSymbol =>
    (⟨some .bound,none,stk⟩ : steinerUnaryDistanceRoundFrameMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem roundFrame_halt (word : List RoundFrameSymbol) :
    haltList steinerUnaryDistanceRoundFrameMachine word = roundFrameCfg none [] [] word [] := by
  apply congrArg (fun stk : Fin 4 → List RoundFrameSymbol =>
    (⟨none,none,stk⟩ : steinerUnaryDistanceRoundFrameMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private def roundFrame_prepare (request : SteinerUnaryDistanceRoundRequest) :
    let Y := (steinerUnaryDistanceRoundFrameAnswer request).length
    let V := (roundFrameFields request.prior.toList).length
    TM2OutputsInTime steinerUnaryDistanceRoundFrameMachine (encodeSteinerUnaryDistanceRound request)
      (some (steinerUnaryDistanceRoundFrameAnswer request)) (4*Y+3*V+5) := by
  let distances := roundFrameDistLists request
  let earlier := request.prior.toList
  let archive := roundFrameFields earlier
  let tail := roundFrameRows distances
  let joined := roundFramePairedRows (distances.map fun row => row.zip earlier)
  let header := roundFrameCell::roundFrameTallies request.cap
  let target := steinerUnaryDistanceRoundFrameAnswer request
  let Y := target.length
  let V := archive.length
  have first := roundFrame_bound request.cap (archive++roundFrameCell::tail) []
  rw [List.append_nil] at first
  have saved := roundFrame_save (earlier.flatMap roundFrameFieldPayload) [] tail header
  simp only [List.append_nil] at saved
  have start := EvalsToInTime.trans _ _ _ _ _ _ first saved
  have restored := roundFrame_restore archive.reverse [] tail header
  rw [List.reverse_reverse,List.length_reverse,List.append_nil] at restored
  have prepared := EvalsToInTime.trans _ _ _ _ _ _ start restored
  have zipped := roundFrame_processRows distances earlier (roundFrame_rectangular request) [] header
  rw [List.append_nil] at zipped
  have combined := EvalsToInTime.trans _ _ _ _ _ _ prepared zipped
  have after := EvalsToInTime.trans _ _ _ _ _ _ combined
    (roundFrame_one (roundFrame_readEnd archive (joined.reverse++header)))
  have cleared := EvalsToInTime.trans _ _ _ _ _ _ after (roundFrame_clear archive (joined.reverse++header))
  have reverse : target.reverse = joined.reverse++header := by
    simp only [target,roundFrame_answer,header,joined,distances,earlier,List.reverse_append,List.reverse_cons,
      roundFrameTallies,List.reverse_replicate,List.append_assoc,List.singleton_append]
  have final := roundFrame_finish [] target.reverse
  rw [List.reverse_reverse,List.length_reverse,List.append_nil,reverse] at final
  have all := EvalsToInTime.trans _ _ _ _ _ _ cleared final
  change EvalsToInTime steinerUnaryDistanceRoundFrameMachine.step (initList _ _) (some (haltList _ _)) _
  rw [roundFrame_init,roundFrame_halt]
  refine ⟨all.toEvalsTo,?_⟩
  have paid := all.steps_le_m
  have stored : (earlier.flatMap roundFrameFieldPayload).length = V := by
    change _ = ((earlier.flatMap roundFrameFieldPayload).map (Sum.inr : Option Bool → RoundFrameSymbol)).length
    rw [List.length_map]
  have outputLength : Y = request.cap+1+joined.length := by
    simp only [Y,target,roundFrame_answer,joined,distances,earlier,List.length_append,List.length_cons,
      roundFrameTallies,List.length_replicate]
    omega
  change all.steps ≤ (Y+1)+(V+1+(1+(3*joined.length+(V+1+((earlier.flatMap roundFrameFieldPayload).length+1+
    (request.cap+1)))))) at paid
  change all.steps ≤ 4*Y+3*V+5
  omega

/-- The paired frame length is bounded by the original frame plus at
most one repeated prior-vector contribution per matrix row. -/
theorem steinerUnaryDistanceRoundFrameAnswer_length_le (request : SteinerUnaryDistanceRoundRequest) :
    let X := (encodeSteinerUnaryDistanceRound request).length
    (steinerUnaryDistanceRoundFrameAnswer request).length ≤ X^2+X := by
  let X := (encodeSteinerUnaryDistanceRound request).length
  let Y := (steinerUnaryDistanceRoundFrameAnswer request).length
  let prior := request.prior.toList
  let rows := roundFrameDistLists request
  let M := (roundFrameFields prior).length
  let Z := (roundFrameRows rows).length
  have input : X = request.cap+1+M+1+Z := by
    simp only [X,encodeSteinerUnaryDistanceRound,prior,rows,M,Z,List.length_append,List.length_cons,
      roundFrameTallies,List.length_replicate]
    omega
  have output : Y = request.cap+1+Z+rows.length*M := by
    rw [show Y = (steinerUnaryDistanceRoundFrameAnswer request).length from rfl,roundFrame_answer]
    simp only [List.length_append,List.length_cons,roundFrameTallies,List.length_replicate]
    change request.cap+((roundFramePairedRows (rows.map fun row => row.zip prior)).length+1) = _
    rw [roundFrame_paired_size rows prior (roundFrame_rectangular request)]
    change request.cap+(Z+rows.length*M+1) = _
    omega
  have rFit : rows.length ≤ X := (roundFrame_dist_rows rows).trans (by omega)
  have mFit : M ≤ X := by omega
  have paid := Nat.mul_le_mul rFit mFit
  change Y ≤ X^2+X
  rw [pow_two]
  omega

/-- Prepare the same-cap row frame from a single previous weight vector
and the rectangular distance table in at most a quadratic number of steps. -/
def steinerUnaryDistanceRoundFrameMachine_run (request : SteinerUnaryDistanceRoundRequest) :
    let X := (encodeSteinerUnaryDistanceRound request).length
    TM2OutputsInTime steinerUnaryDistanceRoundFrameMachine (encodeSteinerUnaryDistanceRound request)
      (some (steinerUnaryDistanceRoundFrameAnswer request)) (4*X^2+7*X+5) := by
  let X := (encodeSteinerUnaryDistanceRound request).length
  let Y := (steinerUnaryDistanceRoundFrameAnswer request).length
  let V := (roundFrameFields request.prior.toList).length
  have run := roundFrame_prepare request
  have shape : V ≤ X := by
    dsimp only [X,encodeSteinerUnaryDistanceRound,V]
    simp only [List.length_append,List.length_cons]
    omega
  have frame : Y ≤ X^2+X := steinerUnaryDistanceRoundFrameAnswer_length_le request
  refine ⟨run.toEvalsTo,run.steps_le_m.trans ?_⟩
  change 4*Y+3*V+5 ≤ 4*X^2+7*X+5
  omega

/-- Actual quadratic stack transitions in the compact round input length. -/
noncomputable def steinerUnaryDistanceRoundFrameMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerUnaryDistanceRound id steinerUnaryDistanceRoundFrameAnswer where
  tm := steinerUnaryDistanceRoundFrameMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 4*Polynomial.X^2+Polynomial.C 7*Polynomial.X+Polynomial.C 5
  outputsFun request := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,
      Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_pow] using steinerUnaryDistanceRoundFrameMachine_run request

/-- Read the cached previous root weights once and the ordered distance
rows once. The row count and column count both equal the supplied n. -/
def steinerForestDistanceRoundRequest {n : ℕ} (dist : Fin n × Fin n → ℕ) (h : ℕ) :
    SteinerUnaryDistanceRoundRequest where
  cap := n
  columns := n
  prior := inwardHeightWeightRounds dist h
  distances := List.ofFn fun root => Vector.ofFn fun child => dist (child,root)

theorem steinerUnaryDistanceRoundPairs_forestRound {n : ℕ} (dist : Fin n × Fin n → ℕ) (h : ℕ) :
    steinerUnaryDistanceRoundPairs (steinerForestDistanceRoundRequest dist h) = steinerForestSharedCapRequest dist h := by
  unfold steinerUnaryDistanceRoundPairs steinerForestSharedCapRequest
  apply congrArg (Prod.mk n)
  simp only [roundFrameDistLists,steinerForestDistanceRoundRequest,List.map_ofFn]
  apply congrArg (@List.ofFn (List (ℕ × ℕ)) n)
  funext root
  change (Vector.ofFn (fun child : Fin n => dist (child,root))).toList.zip (inwardHeightWeightRounds dist h).toList = _
  rw [Vector.toList_ofFn]
  apply List.ext_getElem
  · simp [List.length_zip]
  · intro i _ _
    simp only [List.getElem_zip,List.getElem_ofFn,Vector.getElem_toList]

/-- The prepared frame is exactly the one consumed by the shared-cap
forest round for the selected orientation. -/
theorem steinerUnaryDistanceRoundFrameAnswer_forestRound {n : ℕ} (dist : Fin n × Fin n → ℕ) (h : ℕ) :
    steinerUnaryDistanceRoundFrameAnswer (steinerForestDistanceRoundRequest dist h) =
      encodeSteinerUnarySharedCapRows (steinerForestSharedCapRequest dist h) :=
  congrArg encodeSteinerUnarySharedCapRows (steinerUnaryDistanceRoundPairs_forestRound dist h)

end OnlineReachabilityPreservers
