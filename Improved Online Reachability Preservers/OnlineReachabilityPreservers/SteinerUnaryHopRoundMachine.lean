import OnlineReachabilityPreservers.SteinerDistanceHopTransferRows
import OnlineReachabilityPreservers.SteinerUnaryHopMinimumRowsMachine

/-! Execute one full column of the simultaneous hop relaxation. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing

private abbrev HopColumnSymbol := SteinerUnaryCappedRowsSymbol
private abbrev HopColumnPair := steinerUnaryDistanceRoundFrameMachine
private abbrev HopColumnExpand := steinerUnaryHopSharedCapRowFramesMachine
private abbrev HopColumnMinimum := steinerUnaryHopMinimumRowsMachine
private instance : Fintype HopColumnPair.Λ := HopColumnPair.ΛFin
private instance : Fintype HopColumnExpand.Λ := HopColumnExpand.ΛFin
private instance : Fintype HopColumnMinimum.Λ := HopColumnMinimum.ΛFin

private inductive HopColumnLabel where
  | pair (label : HopColumnPair.Λ)
  | expand (label : HopColumnExpand.Λ)
  | minimum (label : HopColumnMinimum.Λ)
  deriving Fintype

private abbrev HopColumnRegister := HopColumnPair.σ × HopColumnExpand.σ × HopColumnMinimum.σ
private abbrev HopColumnSmallProgram := StackMachineTag.Program (Fin 4) HopColumnSymbol HopColumnLabel HopColumnRegister
private abbrev HopColumnProgram := StackMachineTag.Program (Fin 9) HopColumnSymbol HopColumnLabel HopColumnRegister

private def hopColumnInitial : HopColumnRegister :=
  (HopColumnPair.initialState,HopColumnExpand.initialState,HopColumnMinimum.initialState)

private def hopColumnPairTag :
    StackMachineTag HopColumnSymbol HopColumnSymbol HopColumnPair.Λ HopColumnLabel HopColumnPair.σ HopColumnRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (r,HopColumnExpand.initialState,HopColumnMinimum.initialState)
  readRegister := Prod.fst
  writeLabel := .pair
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def hopColumnExpandTag :
    StackMachineTag HopColumnSymbol HopColumnSymbol HopColumnExpand.Λ HopColumnLabel HopColumnExpand.σ HopColumnRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (HopColumnPair.initialState,r,HopColumnMinimum.initialState)
  readRegister r := r.2.1
  writeLabel := .expand
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def hopColumnMinimumTag :
    StackMachineTag HopColumnSymbol HopColumnSymbol HopColumnMinimum.Λ HopColumnLabel HopColumnMinimum.σ HopColumnRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (HopColumnPair.initialState,HopColumnExpand.initialState,r)
  readRegister r := r.2.2
  writeLabel := .minimum
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def hopColumnExpandStart : HopColumnLabel := .expand HopColumnExpand.main
private def hopColumnMinimumStart : HopColumnLabel := .minimum HopColumnMinimum.main

private def hopColumnPairSlots : Fin 4 ↪ Fin 9 where
  toFun := ![0,1,6,2]
  inj' := by intro a b eq; fin_cases a <;> fin_cases b <;> simp_all

private def hopColumnExpandSlots : Fin 4 ↪ Fin 9 where
  toFun := ![6,0,1,2]
  inj' := by intro a b eq; fin_cases a <;> fin_cases b <;> simp_all

private def hopColumnPairCode : HopColumnLabel → HopColumnSmallProgram
  | .pair label => hopColumnPairTag.returningStatement hopColumnExpandStart (HopColumnPair.m label)
  | _ => Turing.TM2.Stmt.halt

private def hopColumnExpandCode : HopColumnLabel → HopColumnSmallProgram
  | .expand label => hopColumnExpandTag.returningStatement hopColumnMinimumStart (HopColumnExpand.m label)
  | _ => Turing.TM2.Stmt.halt

private def hopColumnProgram : HopColumnLabel → HopColumnProgram
  | .pair label => StackIndexEmbedding.statement hopColumnPairSlots (hopColumnPairCode (.pair label))
  | .expand label => StackIndexEmbedding.statement hopColumnExpandSlots (hopColumnExpandCode (.expand label))
  | .minimum label => hopColumnMinimumTag.statement (HopColumnMinimum.m label)

/-- A full hop round from one compact code matrix and one prior column.
Each phase leaves the next phase's input on the same live tape. -/
abbrev steinerUnaryHopRoundMachine : FinTM2 where
  K := Fin 9
  k₀ := 6
  k₁ := 6
  Γ _ := HopColumnSymbol
  Λ := HopColumnLabel
  main := .pair HopColumnPair.main
  σ := HopColumnRegister
  initialState := hopColumnInitial
  m := hopColumnProgram

private def hopColumnTapes (word : List HopColumnSymbol) : Fin 9 → List HopColumnSymbol :=
  fun j => if j = 6 then word else []

private def hopColumnCfg (label : Option HopColumnLabel) (word : List HopColumnSymbol) : steinerUnaryHopRoundMachine.Cfg :=
  ⟨label,hopColumnInitial,hopColumnTapes word⟩

private theorem hopColumnTapes_mount (slots : Fin 4 ↪ Fin 9) (port : Fin 4) (on : slots port = 6)
    (word : List HopColumnSymbol) (active : Fin 4 → List HopColumnSymbol)
    (shape : active = fun i => if i = port then word else []) :
    StackIndexEmbedding.tapesAt slots (fun i => (active i).map id) (fun _ => []) = hopColumnTapes word := by
  funext j
  by_cases found : ∃ i, slots i = j
  · obtain ⟨i,rfl⟩ := found
    rw [StackIndexEmbedding.tapesAt_image,List.map_id,shape]
    have same : slots i = 6 ↔ i = port := by rw [← on]; exact slots.injective.eq_iff
    simp only [hopColumnTapes,same]
  · rw [StackIndexEmbedding.tapesAt_extra slots _ _ (fun i eq => found ⟨i,eq⟩)]
    have unequal : j ≠ 6 := fun eq => found ⟨port,on.trans eq.symm⟩
    simp only [hopColumnTapes,unequal,ite_false]

private noncomputable def hopColumnPairMounted (c : HopColumnPair.Cfg) : steinerUnaryHopRoundMachine.Cfg :=
  StackIndexEmbedding.configuration hopColumnPairSlots (fun _ => [])
    (hopColumnPairTag.returningConfiguration hopColumnExpandStart c)

private noncomputable def hopColumnExpandMounted (c : HopColumnExpand.Cfg) : steinerUnaryHopRoundMachine.Cfg :=
  StackIndexEmbedding.configuration hopColumnExpandSlots (fun _ => [])
    (hopColumnExpandTag.returningConfiguration hopColumnMinimumStart c)

private theorem hopColumnPair_step {a b : HopColumnPair.Cfg} (move : HopColumnPair.step a = some b) :
    steinerUnaryHopRoundMachine.step (hopColumnPairMounted a) = some (hopColumnPairMounted b) := by
  have tagged := hopColumnPairTag.step_embedded_return hopColumnExpandStart
    (base := HopColumnPair.m) (host := hopColumnPairCode) (fun _ => rfl) move
  have mounted := StackIndexEmbedding.step_on hopColumnPairSlots (base := hopColumnPairCode) (fun _ => [])
    (hopColumnPairTag.returningConfiguration hopColumnExpandStart a)
  rw [tagged] at mounted
  rcases a with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact mounted

private theorem hopColumnExpand_step {a b : HopColumnExpand.Cfg} (move : HopColumnExpand.step a = some b) :
    steinerUnaryHopRoundMachine.step (hopColumnExpandMounted a) = some (hopColumnExpandMounted b) := by
  have tagged := hopColumnExpandTag.step_embedded_return hopColumnMinimumStart
    (base := HopColumnExpand.m) (host := hopColumnExpandCode) (fun _ => rfl) move
  have mounted := StackIndexEmbedding.step_on hopColumnExpandSlots (base := hopColumnExpandCode) (fun _ => [])
    (hopColumnExpandTag.returningConfiguration hopColumnMinimumStart a)
  rw [tagged] at mounted
  rcases a with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact mounted

private theorem hopColumn_init (word : List HopColumnSymbol) :
    initList steinerUnaryHopRoundMachine word = hopColumnCfg (some (.pair HopColumnPair.main)) word := by
  apply congrArg (fun tapes : Fin 9 → List HopColumnSymbol =>
    (⟨some (.pair HopColumnPair.main),hopColumnInitial,tapes⟩ : steinerUnaryHopRoundMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem hopColumn_halt (word : List HopColumnSymbol) :
    haltList steinerUnaryHopRoundMachine word = hopColumnCfg none word := by
  apply congrArg (fun tapes : Fin 9 → List HopColumnSymbol =>
    (⟨none,hopColumnInitial,tapes⟩ : steinerUnaryHopRoundMachine.Cfg))
  funext i
  fin_cases i <;> rfl

private theorem hopColumnPair_init (word : List HopColumnSymbol) :
    hopColumnPairMounted (initList HopColumnPair word) = initList steinerUnaryHopRoundMachine word := by
  rw [hopColumn_init]
  apply congrArg (fun tapes : Fin 9 → List HopColumnSymbol =>
    (⟨some (.pair HopColumnPair.main),hopColumnInitial,tapes⟩ : steinerUnaryHopRoundMachine.Cfg))
  exact hopColumnTapes_mount hopColumnPairSlots 2 rfl word _ (by funext i; fin_cases i <;> rfl)

private theorem hopColumnPair_halt (word : List HopColumnSymbol) :
    hopColumnPairMounted (haltList HopColumnPair word) = hopColumnCfg (some hopColumnExpandStart) word := by
  apply congrArg (fun tapes : Fin 9 → List HopColumnSymbol =>
    (⟨some hopColumnExpandStart,hopColumnInitial,tapes⟩ : steinerUnaryHopRoundMachine.Cfg))
  exact hopColumnTapes_mount hopColumnPairSlots 2 rfl word _ (by funext i; fin_cases i <;> rfl)

private theorem hopColumnExpand_init (word : List HopColumnSymbol) :
    hopColumnExpandMounted (initList HopColumnExpand word) = hopColumnCfg (some hopColumnExpandStart) word := by
  apply congrArg (fun tapes : Fin 9 → List HopColumnSymbol =>
    (⟨some hopColumnExpandStart,hopColumnInitial,tapes⟩ : steinerUnaryHopRoundMachine.Cfg))
  exact hopColumnTapes_mount hopColumnExpandSlots 0 rfl word _ (by funext i; fin_cases i <;> rfl)

private theorem hopColumnExpand_halt (word : List HopColumnSymbol) :
    hopColumnExpandMounted (haltList HopColumnExpand word) = hopColumnCfg (some hopColumnMinimumStart) word := by
  apply congrArg (fun tapes : Fin 9 → List HopColumnSymbol =>
    (⟨some hopColumnMinimumStart,hopColumnInitial,tapes⟩ : steinerUnaryHopRoundMachine.Cfg))
  exact hopColumnTapes_mount hopColumnExpandSlots 0 rfl word _ (by funext i; fin_cases i <;> rfl)

private theorem hopColumnMinimum_init (word : List HopColumnSymbol) :
    hopColumnMinimumTag.configuration (initList HopColumnMinimum word) = hopColumnCfg (some hopColumnMinimumStart) word := by
  apply congrArg (fun tapes : Fin 9 → List HopColumnSymbol =>
    (⟨some hopColumnMinimumStart,hopColumnInitial,tapes⟩ : steinerUnaryHopRoundMachine.Cfg))
  funext i
  change ((initList HopColumnMinimum word).stk i).map id = _
  rw [List.map_id]
  fin_cases i <;> rfl

private theorem hopColumnMinimum_halt (word : List HopColumnSymbol) :
    hopColumnMinimumTag.configuration (haltList HopColumnMinimum word) = haltList steinerUnaryHopRoundMachine word := by
  rw [hopColumn_halt]
  apply congrArg (fun tapes : Fin 9 → List HopColumnSymbol =>
    (⟨none,hopColumnInitial,tapes⟩ : steinerUnaryHopRoundMachine.Cfg))
  funext i
  change ((haltList HopColumnMinimum word).stk i).map id = _
  rw [List.map_id]
  fin_cases i <;> rfl

/-- One unary minimum for each code row, in the stored source order. -/
def steinerUnaryHopRoundAnswer (request : SteinerUnaryDistanceRoundRequest) : List SteinerUnaryCappedRowsSymbol :=
  steinerUnaryHopMinimumRowsAnswer (steinerUnaryDistanceRoundPairs request)

private theorem hopColumnCompact_cap (pairs : SteinerUnarySharedCapRows) :
    pairs.1 ≤ (encodeSteinerUnarySharedCapRows pairs).length := by
  rw [encodeSteinerUnarySharedCapRows,List.length_append]
  change pairs.1 ≤ (List.replicate pairs.1 (Sum.inr (some true) : HopColumnSymbol)).length+_
  rw [List.length_replicate]
  omega

/-- Pair the prior, expand the common cap, and minimize in a single
native run on the compact frame. -/
noncomputable def steinerUnaryHopRoundMachine_run (request : SteinerUnaryDistanceRoundRequest) :
    let input := encodeSteinerUnaryDistanceRound request
    let X := input.length
    let C := X^2+X
    TM2OutputsInTime steinerUnaryHopRoundMachine input (some (steinerUnaryHopRoundAnswer request))
      (15*C^2+45*C+4*X^2+7*X+11) := by
  let input := encodeSteinerUnaryDistanceRound request
  let pairs := steinerUnaryDistanceRoundPairs request
  let compact := steinerUnaryDistanceRoundFrameAnswer request
  let expanded := steinerUnaryHopSharedCapRowFramesAnswer pairs
  let X := input.length
  let Y := compact.length
  let Z := expanded.length
  let C := X^2+X
  let pairRun := steinerUnaryDistanceRoundFrameMachine_run request
  have first := iterate_map_some hopColumnPairMounted (fun move => hopColumnPair_step move) pairRun.steps pairRun.evals_in_steps
  rw [hopColumnPair_init,hopColumnPair_halt] at first
  have paired : EvalsToInTime steinerUnaryHopRoundMachine.step (initList steinerUnaryHopRoundMachine input)
      (some (hopColumnCfg (some hopColumnExpandStart) compact)) (4*X^2+7*X+5) :=
    ⟨⟨pairRun.steps,first⟩,pairRun.steps_le_m⟩
  let expandRun := steinerUnaryHopSharedCapRowFramesMachine_run pairs
  have second := iterate_map_some hopColumnExpandMounted (fun move => hopColumnExpand_step move)
    expandRun.steps expandRun.evals_in_steps
  rw [hopColumnExpand_init,hopColumnExpand_halt] at second
  have expandedRun : EvalsToInTime steinerUnaryHopRoundMachine.step (hopColumnCfg (some hopColumnExpandStart) compact)
      (some (hopColumnCfg (some hopColumnMinimumStart) expanded)) (3*Y^2+9*Y+4) :=
    ⟨⟨expandRun.steps,second⟩,expandRun.steps_le_m⟩
  have minimized := hopColumnMinimumTag.evaluation (base := HopColumnMinimum.m) (host := hopColumnProgram)
    (fun _ => rfl) (steinerUnaryHopMinimumRowsMachine_run pairs)
  change EvalsToInTime steinerUnaryHopRoundMachine.step
    (hopColumnMinimumTag.configuration (initList HopColumnMinimum expanded))
    (some (hopColumnMinimumTag.configuration (haltList HopColumnMinimum (steinerUnaryHopRoundAnswer request))))
    (12*Z+2) at minimized
  rw [hopColumnMinimum_init,hopColumnMinimum_halt] at minimized
  have all := EvalsToInTime.trans _ _ _ _ _ _
    (EvalsToInTime.trans _ _ _ _ _ _ paired expandedRun) minimized
  refine ⟨all.toEvalsTo,all.steps_le_m.trans ?_⟩
  have cap : pairs.1 ≤ Y := hopColumnCompact_cap pairs
  have size : Z ≤ (pairs.1+3)*Y := steinerUnaryHopSharedCapRowFramesAnswer_length_le pairs
  have expand : Z ≤ Y^2+3*Y := calc
    Z ≤ (pairs.1+3)*Y := size
    _ ≤ (Y+3)*Y := Nat.mul_le_mul_right _ (by omega)
    _ = Y^2+3*Y := by ring
  have fit : Y ≤ C := steinerUnaryDistanceRoundFrameAnswer_length_le request
  have square : Y^2 ≤ C^2 := Nat.pow_le_pow_left fit 2
  change (12*Z+2)+((3*Y^2+9*Y+4)+(4*X^2+7*X+5)) ≤ 15*C^2+45*C+4*X^2+7*X+11
  omega

/-- The entire native column update has a transition polynomial in the
compact encoded request. -/
noncomputable def steinerUnaryHopRoundMachine_polytime :
    TM2ComputableInPolyTime encodeSteinerUnaryDistanceRound id steinerUnaryHopRoundAnswer where
  tm := steinerUnaryHopRoundMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time :=
    let C : Polynomial ℕ := Polynomial.X^2+Polynomial.X
    Polynomial.C 15*C^2+Polynomial.C 45*C+Polynomial.C 4*Polynomial.X^2+
      Polynomial.C 7*Polynomial.X+Polynomial.C 11
  outputsFun request := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq,Polynomial.eval_add,Polynomial.eval_C_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_pow] using steinerUnaryHopRoundMachine_run request

/-- The ordered unary answer is the exact next hop column. -/
theorem steinerUnaryHopRoundAnswer_hopRound {n : ℕ} (G : Arcs (Fin n)) (depth : ℕ) (target : Fin n) :
    steinerUnaryHopRoundAnswer (steinerHopTransferRoundRequest G depth target) =
      encodeSteinerUnaryCappedRowTallies (List.ofFn fun source => steinerDistanceHopRounds G (depth+1) (source,target)) := by
  unfold steinerUnaryHopRoundAnswer steinerUnaryHopMinimumRowsAnswer
  rw [steinerHopTransferRoundRequest_pairs]
  apply congrArg encodeSteinerUnaryCappedRowTallies
  have exactColumn := congrArg Vector.toList (steinerHopTransferRound_eq_hopRounds G depth target)
  simpa only [List.map_ofFn,Function.comp_def,steinerUnaryHopMinimumRowValue,steinerHopTransferCandidate,
    steinerHopTransferRound,Vector.toList_ofFn,Vector.getElem_ofFn] using exactColumn

/-- One supplied compact code matrix and prior column suffice for
the exact next column at that target. -/
noncomputable def steinerUnaryHopRoundMachine_hopRound {n : ℕ} (G : Arcs (Fin n)) (depth : ℕ) (target : Fin n) :
    let request := steinerHopTransferRoundRequest G depth target
    let X := (encodeSteinerUnaryDistanceRound request).length
    let C := X^2+X
    TM2OutputsInTime steinerUnaryHopRoundMachine (encodeSteinerUnaryDistanceRound request)
      (some (encodeSteinerUnaryCappedRowTallies (List.ofFn fun source => steinerDistanceHopRounds G (depth+1) (source,target))))
      (15*C^2+45*C+4*X^2+7*X+11) := by
  simpa only [steinerUnaryHopRoundAnswer_hopRound] using steinerUnaryHopRoundMachine_run (steinerHopTransferRoundRequest G depth target)

end OnlineReachabilityPreservers
