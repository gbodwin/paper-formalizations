import OnlineReachabilityPreservers.SteinerUnaryForestScaleMachine

/-! Compute the forest proposal's bit width directly from the live scale tally. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing

private abbrev ProposalSymbol := SteinerUnaryCappedRowsSymbol
private abbrev ProposalScaleLabel := steinerUnaryForestScaleMachine.Λ
private abbrev ProposalWidthLabel := steinerUnaryBitWidthMachine.Λ
private instance : Fintype ProposalScaleLabel := steinerUnaryForestScaleMachine.ΛFin
private instance : Fintype ProposalWidthLabel := steinerUnaryBitWidthMachine.ΛFin

private inductive ProposalLabel where
  | scale (label : ProposalScaleLabel)
  | width (label : ProposalWidthLabel)
  deriving Fintype

private abbrev ProposalRegister := steinerUnaryForestScaleMachine.σ × steinerUnaryBitWidthMachine.σ
private abbrev ProposalProgram := StackMachineTag.Program (Fin 13) ProposalSymbol ProposalLabel ProposalRegister

private def proposalInitial : ProposalRegister :=
  (steinerUnaryForestScaleMachine.initialState,steinerUnaryBitWidthMachine.initialState)

private def proposalScaleTag :
    StackMachineTag ProposalSymbol ProposalSymbol ProposalScaleLabel ProposalLabel
      steinerUnaryForestScaleMachine.σ ProposalRegister where
  writeSymbol := id
  readSymbol := some
  writeRegister r := (r,steinerUnaryBitWidthMachine.initialState)
  readRegister := Prod.fst
  writeLabel := .scale
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def proposalWriteBit (bit : Bool) : ProposalSymbol := Sum.inr (some bit)

private def proposalReadBit : ProposalSymbol → Option Bool
  | .inr bit => bit
  | .inl _ => none

private def proposalWidthTag :
    StackMachineTag Bool ProposalSymbol ProposalWidthLabel ProposalLabel steinerUnaryBitWidthMachine.σ ProposalRegister where
  writeSymbol := proposalWriteBit
  readSymbol := proposalReadBit
  writeRegister r := (steinerUnaryForestScaleMachine.initialState,r)
  readRegister := Prod.snd
  writeLabel := .width
  read_written_symbol _ := rfl
  read_written_register _ := rfl

private def proposalWidthStart : ProposalLabel := .width steinerUnaryBitWidthMachine.main

/-- The width input stack is the scale output stack. -/
private def proposalWidthSlots : Fin 3 ↪ Fin 13 where
  toFun := ![12,0,5]
  inj' := by intro a b same; fin_cases a <;> fin_cases b <;> simp_all

private def proposalWidthCode : ProposalLabel → StackMachineTag.Program (Fin 3) ProposalSymbol ProposalLabel ProposalRegister
  | .width label => proposalWidthTag.statement (steinerUnaryBitWidthMachine.m label)
  | .scale _ => Turing.TM2.Stmt.halt

private def proposalProgram : ProposalLabel → ProposalProgram
  | .scale label => proposalScaleTag.returningStatement proposalWidthStart (steinerUnaryForestScaleMachine.m label)
  | .width label => StackIndexEmbedding.statement proposalWidthSlots (proposalWidthCode (.width label))

/-- Produce the bit width of the forest scale by returning directly
from the scale machine to repeated unary halving. -/
abbrev steinerUnaryForestProposalWidthMachine : FinTM2 where
  K := Fin 13
  k₀ := 5
  k₁ := 5
  Γ _ := ProposalSymbol
  Λ := ProposalLabel
  main := .scale steinerUnaryForestScaleMachine.main
  σ := ProposalRegister
  initialState := proposalInitial
  m := proposalProgram

private def proposalAtWidth (word : List ProposalSymbol) : steinerUnaryForestProposalWidthMachine.Cfg where
  l := some proposalWidthStart
  var := proposalInitial
  stk := ![[],[],[],[],[],[],[],[],[],[],[],[],word]

private theorem proposalScale_init (word : List ProposalSymbol) :
    proposalScaleTag.returningConfiguration proposalWidthStart (initList steinerUnaryForestScaleMachine word) =
      initList steinerUnaryForestProposalWidthMachine word := by
  apply congrArg (fun tapes : Fin 13 → List ProposalSymbol =>
    (⟨some (.scale steinerUnaryForestScaleMachine.main),proposalInitial,tapes⟩ : steinerUnaryForestProposalWidthMachine.Cfg))
  funext i
  change ((initList steinerUnaryForestScaleMachine word).stk i).map id = _
  rw [List.map_id]
  rfl

private theorem proposalScale_return (word : List ProposalSymbol) :
    proposalScaleTag.returningConfiguration proposalWidthStart (haltList steinerUnaryForestScaleMachine word) =
      proposalAtWidth word := by
  apply congrArg (fun tapes : Fin 13 → List ProposalSymbol =>
    (⟨some proposalWidthStart,proposalInitial,tapes⟩ : steinerUnaryForestProposalWidthMachine.Cfg))
  funext i
  change ((haltList steinerUnaryForestScaleMachine word).stk i).map id = _
  rw [List.map_id]
  fin_cases i <;> rfl

private noncomputable def proposalWidthHosted (c : steinerUnaryBitWidthMachine.Cfg) :
    steinerUnaryForestProposalWidthMachine.Cfg :=
  StackIndexEmbedding.configuration proposalWidthSlots (fun _ => []) (proposalWidthTag.configuration c)

private theorem proposalWidth_step {c after : steinerUnaryBitWidthMachine.Cfg}
    (move : steinerUnaryBitWidthMachine.step c = some after) :
    steinerUnaryForestProposalWidthMachine.step (proposalWidthHosted c) = some (proposalWidthHosted after) := by
  have tagged := proposalWidthTag.step_embedded (base := steinerUnaryBitWidthMachine.m)
    (host := proposalWidthCode) (fun _ => rfl) c
  change Turing.TM2.step steinerUnaryBitWidthMachine.m c = some after at move
  rw [move] at tagged
  have hosted := StackIndexEmbedding.step_on proposalWidthSlots (base := proposalWidthCode)
    (fun _ => []) (proposalWidthTag.configuration c)
  rw [tagged] at hosted
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some label => exact hosted

private theorem proposalWidth_tapes (c : steinerUnaryBitWidthMachine.Cfg) (i : Fin 13) :
    (proposalWidthHosted c).stk i =
      if i = 12 then (c.stk 0).map proposalWriteBit else
      if i = 0 then (c.stk 1).map proposalWriteBit else
      if i = 5 then (c.stk 2).map proposalWriteBit else [] := by
  have image (j : Fin 3) : (proposalWidthHosted c).stk (proposalWidthSlots j) = (c.stk j).map proposalWriteBit := by
    change StackIndexEmbedding.tapesAt proposalWidthSlots (fun k => (c.stk k).map proposalWriteBit)
      (fun _ => []) (proposalWidthSlots j) = _
    exact StackIndexEmbedding.tapesAt_image proposalWidthSlots _ _ j
  have outside (i : Fin 13) (ne12 : i ≠ 12) (ne0 : i ≠ 0) (ne5 : i ≠ 5) :
      (proposalWidthHosted c).stk i = [] := by
    apply StackIndexEmbedding.tapesAt_extra proposalWidthSlots
    intro j same
    fin_cases j
    · exact ne12 same.symm
    · exact ne0 same.symm
    · exact ne5 same.symm
  by_cases i12 : i = 12
  · subst i
    have here := image 0
    change (proposalWidthHosted c).stk 12 = _ at here
    simpa only [ite_true] using here
  by_cases i0 : i = 0
  · subst i
    have here := image 1
    change (proposalWidthHosted c).stk 0 = _ at here
    simpa only [ite_eq_right i12,ite_true] using here
  by_cases i5 : i = 5
  · subst i
    have here := image 2
    change (proposalWidthHosted c).stk 5 = _ at here
    simpa only [ite_eq_right i12,ite_eq_right i0,ite_true] using here
  simpa only [ite_eq_right i12,ite_eq_right i0,ite_eq_right i5] using outside i i12 i0 i5

private theorem proposalWidth_frame (n : ℕ) :
    (encodeSteinerUnaryProductCount n).map proposalWriteBit = encodeSteinerUnaryRoundTotal n := by
  change (List.replicate n true).map proposalWriteBit = List.replicate n (proposalWriteBit true)
  exact List.map_replicate

private theorem proposalWidth_init (n : ℕ) :
    proposalWidthHosted (initList steinerUnaryBitWidthMachine (encodeSteinerUnaryProductCount n)) =
      proposalAtWidth (encodeSteinerUnaryRoundTotal n) := by
  apply congrArg (fun tapes : Fin 13 → List ProposalSymbol =>
    (⟨some proposalWidthStart,proposalInitial,tapes⟩ : steinerUnaryForestProposalWidthMachine.Cfg))
  funext i
  change (proposalWidthHosted (initList steinerUnaryBitWidthMachine (encodeSteinerUnaryProductCount n))).stk i = _
  rw [proposalWidth_tapes]
  fin_cases i <;> first | exact proposalWidth_frame n | rfl

private theorem proposalWidth_halt (n : ℕ) :
    proposalWidthHosted (haltList steinerUnaryBitWidthMachine (encodeSteinerUnaryProductCount n)) =
      haltList steinerUnaryForestProposalWidthMachine (encodeSteinerUnaryRoundTotal n) := by
  apply congrArg (fun tapes : Fin 13 → List ProposalSymbol =>
    (⟨none,proposalInitial,tapes⟩ : steinerUnaryForestProposalWidthMachine.Cfg))
  funext i
  change (proposalWidthHosted (haltList steinerUnaryBitWidthMachine (encodeSteinerUnaryProductCount n))).stk i = _
  rw [proposalWidth_tapes]
  fin_cases i <;> first | exact proposalWidth_frame n | rfl

private theorem proposalInput_cap_le {n : ℕ} (dist : Fin n × Fin n → ℕ) (height : ℕ) :
    n+1 ≤ (encodeSteinerUnaryForestScaleInput dist height).length := by
  simp only [encodeSteinerUnaryForestScaleInput,encodeSteinerUnaryDistanceHeight,encodeSteinerUnaryRoundCap,
    List.length_append,List.length_cons,List.length_replicate]
  omega

/-- The composed native transition bound at fixed height. -/
noncomputable def steinerUnaryForestProposalWidthPolynomial (height : ℕ) : Polynomial ℕ :=
  steinerUnaryForestScalePolynomial height+Polynomial.C 6*Polynomial.X^(height+2)+Polynomial.C 4

/-- From the two supplied distance orders, compute the bit width of
the exact positive scale on the same tapes. -/
noncomputable def steinerUnaryForestProposalWidthMachine_run {n : ℕ} (dist : Fin n × Fin n → ℕ) (height : ℕ) :
    let input := encodeSteinerUnaryForestScaleInput dist height
    TM2OutputsInTime steinerUnaryForestProposalWidthMachine input
      (some (encodeSteinerUnaryRoundTotal ((forestScaleFromDistanceRounds dist height).size)))
      ((steinerUnaryForestProposalWidthPolynomial height).eval input.length) := by
  let input := encodeSteinerUnaryForestScaleInput dist height
  let S := forestScaleFromDistanceRounds dist height
  let X := input.length
  have small := proposalInput_cap_le dist height
  change n+1 ≤ X at small
  have magnitude : S ≤ 1+2*n*(n+1)^(height+1) := forestScaleFromDistanceRounds_le dist height
  have both := Nat.mul_le_mul (Nat.mul_le_mul_left 2 (show n ≤ X by omega)) (Nat.pow_le_pow_left small (height+1))
  have rewritePower : 2*X*X^(height+1) = 2*X^(height+2) := by rw [pow_succ]; ring
  rw [rewritePower] at both
  have bound : S ≤ 1+2*X^(height+2) := magnitude.trans (Nat.add_le_add_left both 1)
  have first := proposalScaleTag.evaluationReturning proposalWidthStart (base := steinerUnaryForestScaleMachine.m)
    (host := proposalProgram) (fun _ => rfl) (steinerUnaryForestScaleMachine_run dist height)
  rw [proposalScale_init,proposalScale_return] at first
  let second := steinerUnaryBitWidthMachine_run S
  have hosted := iterate_map_some proposalWidthHosted (fun move => proposalWidth_step move)
    second.steps second.evals_in_steps
  rw [proposalWidth_init,proposalWidth_halt] at hosted
  have width : EvalsToInTime steinerUnaryForestProposalWidthMachine.step (proposalAtWidth (encodeSteinerUnaryRoundTotal S))
      (some (haltList steinerUnaryForestProposalWidthMachine (encodeSteinerUnaryRoundTotal S.size))) (3*S+1) :=
    ⟨⟨second.steps,hosted⟩,second.steps_le_m⟩
  have run := EvalsToInTime.trans _ _ _ _ _ _ first width
  refine ⟨run.toEvalsTo,run.steps_le_m.trans ?_⟩
  simp only [steinerUnaryForestProposalWidthPolynomial,Polynomial.eval_add,Polynomial.eval_C_mul,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_C]
  change 3*S+1+(steinerUnaryForestScalePolynomial height).eval X ≤
    (steinerUnaryForestScalePolynomial height).eval X+6*X^(height+2)+4
  omega

/-- The actual width computation is polynomial for each fixed height. -/
noncomputable def steinerUnaryForestProposalWidthMachine_polytime (height : ℕ) :
    TM2ComputableInPolyTime
      (fun request : Σ n : ℕ, (Fin n × Fin n → ℕ) => encodeSteinerUnaryForestScaleInput request.2 height)
      encodeSteinerUnaryRoundTotal (fun request => (forestScaleFromDistanceRounds request.2 height).size) where
  tm := steinerUnaryForestProposalWidthMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := steinerUnaryForestProposalWidthPolynomial height
  outputsFun request := by
    simpa only [Equiv.refl,List.map_id_fun,id_eq] using steinerUnaryForestProposalWidthMachine_run request.2 height

/-- On exact hop data, compute the width used by forest seed decoding. -/
noncomputable def steinerUnaryForestProposalWidthMachine_hops {n : ℕ} (G : Arcs (Fin n)) (height : ℕ) :
    let dist : Fin n × Fin n → ℕ := fun d => hops G d.1 d.2
    let input := encodeSteinerUnaryForestScaleInput dist height
    TM2OutputsInTime steinerUnaryForestProposalWidthMachine input
      (some (encodeSteinerUnaryRoundTotal ((forestScale G height).log2+1)))
      ((steinerUnaryForestProposalWidthPolynomial height).eval input.length) := by
  let dist : Fin n × Fin n → ℕ := fun d => hops G d.1 d.2
  have positive : 1 ≤ (forestScale G height).size :=
    Nat.one_le_iff_ne_zero.mpr fun zero => (ne_of_gt (forestScale_pos G height)) (Nat.size_eq_zero.mp zero)
  have same : (forestScale G height).size = (forestScale G height).log2+1 := by
    rw [← max_size_eq_log2_add_one,max_eq_right positive]
  simpa only [forestScaleFromDistanceRounds_eq G dist (fun _ => rfl),same] using
    steinerUnaryForestProposalWidthMachine_run dist height

end OnlineReachabilityPreservers
