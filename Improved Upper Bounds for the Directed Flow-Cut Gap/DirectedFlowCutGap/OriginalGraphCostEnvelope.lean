import DirectedFlowCutGap.RawGraphInputStore
import Mathlib.Algebra.Polynomial.Eval.Defs
import Lean.Elab.Tactic

/-! Polynomial closure of the actual deterministic interpreter and controller bounds. -/

namespace DirectedFlowCutGap.OriginalGraphCostEnvelope

open Polynomial BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open AdaptiveControllerBounds (Limits)

def Covered {ι : Type} (size : ι → ℕ) (f : ι → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ x, f x ≤ p.eval (size x)

namespace Covered

variable {ι : Type} {width : ι → ℕ}

theorem of_le {f g : ι → ℕ} (h : Covered width g) (le : ∀ x, f x ≤ g x) : Covered width f := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p,fun x => (le x).trans (hp x)⟩

theorem const (c : ℕ) : Covered width (fun _ => c) := ⟨C c,by simp⟩

theorem id : Covered width width := ⟨X,by simp⟩

theorem add {f g : ι → ℕ} (a : Covered width f) (b : Covered width g) : Covered width (fun x => f x+g x) := by
  obtain ⟨p,hp⟩ := a
  obtain ⟨q,hq⟩ := b
  exact ⟨p+q,fun x => by rw [eval_add]; exact Nat.add_le_add (hp x) (hq x)⟩

theorem mul {f g : ι → ℕ} (a : Covered width f) (b : Covered width g) : Covered width (fun x => f x*g x) := by
  obtain ⟨p,hp⟩ := a
  obtain ⟨q,hq⟩ := b
  exact ⟨p*q,fun x => by rw [eval_mul]; exact Nat.mul_le_mul (hp x) (hq x)⟩

theorem pow {f : ι → ℕ} (a : Covered width f) (k : ℕ) : Covered width (fun x => (f x)^k) := by
  obtain ⟨p,hp⟩ := a
  exact ⟨p^k,fun x => by rw [eval_pow]; exact Nat.pow_le_pow_left (hp x) k⟩

theorem max {f g : ι → ℕ} (a : Covered width f) (b : Covered width g) : Covered width (fun x => max (f x) (g x)) :=
  (a.add b).of_le fun _ => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

theorem min {f g : ι → ℕ} (a : Covered width f) : Covered width (fun x => min (f x) (g x)) :=
  a.of_le fun _ => min_le_left _ _

theorem sub {f g : ι → ℕ} (a : Covered width f) : Covered width (fun x => f x-g x) :=
  a.of_le fun _ => Nat.sub_le _ _

theorem size {f : ι → ℕ} (a : Covered width f) : Covered width (fun x => (f x).size) :=
  a.of_le fun _ => Nat.size_le.mpr Nat.lt_two_pow_self

theorem log {f g : ι → ℕ} (a : Covered width g) : Covered width (fun x => Nat.log (f x) (g x)) :=
  a.of_le fun _ => Nat.log_le_self _ _

end Covered

private inductive Formula {ι : Type} (width : ι → ℕ) where
  | input (f : ι → ℕ) (cert : Covered width f)
  | plus : Formula width → Formula width → Formula width
  | times : Formula width → Formula width → Formula width
  | power : Formula width → ℕ → Formula width
  | larger : Formula width → Formula width → Formula width
  | smaller : Formula width → Formula width → Formula width
  | minus : Formula width → Formula width → Formula width
  | size : Formula width → Formula width
  | log : Formula width → Formula width → Formula width

private def Formula.run {ι : Type} {width : ι → ℕ} (x : ι) : Formula width → ℕ
  | .input f _ => f x
  | .plus a b => a.run x+b.run x
  | .times a b => a.run x*b.run x
  | .power a k => (a.run x)^k
  | .larger a b => max (a.run x) (b.run x)
  | .smaller a b => min (a.run x) (b.run x)
  | .minus a b => a.run x-b.run x
  | .size a => (a.run x).size
  | .log a b => Nat.log (a.run x) (b.run x)

private theorem Formula.covered {ι : Type} {width : ι → ℕ} (f : Formula width) :
    Covered width (fun x => f.run x) := by
  induction f with
  | input f h => exact h
  | plus _ _ a b => exact a.add b
  | times _ _ a b => exact a.mul b
  | power _ k a => exact a.pow k
  | larger _ _ a b => exact a.max b
  | smaller _ _ a _ => exact a.min
  | minus _ _ a _ => exact a.sub
  | size _ a => exact a.size
  | log _ _ _ b => exact b.log

open Lean Meta Elab Tactic in
private partial def coverTerm (width point : Expr) (known : List (Expr × Expr)) (term : Expr) : MetaM Expr := do
  let term ← instantiateMVars term.headBeta
  let term := term.consumeMData
  if let .letE _ _ value body _ := term then
    return ← coverTerm width point known (body.instantiate1 value)
  if let some (_, proof) := known.find? (fun item => item.1 == term) then
    return ← mkAppOptM ``Formula.input #[none,some width,some (← mkLambdaFVars #[point] term),some proof]
  if !term.containsFVar point.fvarId! then
    let proof ← mkAppOptM ``Covered.const #[none,some width,some term]
    return ← mkAppOptM ``Formula.input #[none,some width,some (← mkLambdaFVars #[point] term),some proof]
  let args := term.getAppArgs
  let name := term.getAppFn.constName?.getD .anonymous
  let binary := [
    (``HAdd.hAdd,``Formula.plus),(``Nat.add,``Formula.plus),(``HMul.hMul,``Formula.times),(``Nat.mul,``Formula.times),
    (``Max.max,``Formula.larger),(``Min.min,``Formula.smaller),(``HSub.hSub,``Formula.minus),(``Nat.sub,``Formula.minus),
    (``Nat.log,``Formula.log)]
  if let some (_, ctor) := binary.find? (fun p => p.1 == name) then
    let left ← coverTerm width point known args[args.size-2]!
    let right ← coverTerm width point known args[args.size-1]!
    return ← mkAppOptM ctor #[none,some width,some left,some right]
  if name == ``HPow.hPow || name == ``Nat.pow then
    let base ← coverTerm width point known args[args.size-2]!
    return ← mkAppOptM ``Formula.power #[none,some width,some base,some args[args.size-1]!]
  if name == ``Nat.size then
    let arg ← coverTerm width point known args[0]!
    return ← mkAppOptM ``Formula.size #[none,some width,some arg]
  if name == ``Nat.succ then
    let left ← coverTerm width point known args[0]!
    let right ← coverTerm width point known (mkNatLit 1)
    return ← mkAppOptM ``Formula.plus #[none,some width,some left,some right]
  if let some unfolded ← unfoldDefinition? term then
    if unfolded != term then
      return ← coverTerm width point known unfolded
  throwError "no polynomial premise for {term}; known keys = {known.map Prod.fst}"

open Lean Meta Elab Tactic in
elab "cover_arithmetic" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let ty := ty.consumeMData.headBeta
  let args := ty.getAppArgs
  unless ty.getAppFn.constName? == some ``Covered do
    throwError "expected a polynomial coverage goal, got {ty}"
  let width := args[1]!
  let formula ← withLocalDeclD `x args[0]! fun x => do
    let mut known := [(mkApp width x,← mkAppOptM ``Covered.id #[none,some width])]
    for decl in ← getLCtx do
      let type ← instantiateMVars decl.type
      if type.getAppFn.constName? == some ``Covered then
        let input := type.getAppArgs
        if ← isDefEq input[1]! width then
          known := ((mkApp input[2]! x).headBeta,decl.toExpr)::known
    coverTerm width x known (mkApp args[2]! x)
  let proof ← mkAppOptM ``Formula.covered #[none,some width,some formula]
  goal.assign proof
  replaceMainGoal []

section Formulas

variable {ι : Type} {width : ι → ℕ}

private theorem label_range {n : ι → ℕ} (nn : Covered width n) :
    Covered width (fun x => BinaryLabelRangeProgram.steps (n x).bits) := by
  apply Covered.of_le (g:=fun x => n x*(8*(n x).size+19)+10*(n x).size+9)
  · cover_arithmetic
  · intro x
    simpa only [value_bits,Nat.size_eq_bits_len] using BinaryLabelRangeProgram.steps_le (n x).bits

private theorem residual_min_cut {n B W F P : ι → ℕ}
    (nn : Covered width n) (bb : Covered width B) (ww : Covered width W)
    (ff : Covered width F) (pp : Covered width P) :
    Covered width (fun x => ResidualZeroMinCutProgram.instructionBound (n x) (B x) (W x) (F x) (P x)) := by
  simp only [ResidualZeroMinCutProgram.instructionBound,ResidualZeroTableProgram.instructionBound,
    ResidualMaxFlowCutProgram.instructionBound,ResidualFlowLoopProgram.instructionBound,
    ResidualFlowLoopProgram.iterationBound,ResidualFlowStepProgram.instructionBound,
    ResidualCutProgram.instructionBound,ResidualSearchProgram.instructionBound,
    ResidualCutFlagsProgram.instructionBound,ResidualMatrixProgram.instructionBound,
    ResidualRowProgram.instructionBound,SupportRecoveryProgram.searchCap,SupportRecoveryProgram.scanCap,
    ResidualTableUpdateProgram.instructionBound,ResidualRowUpdateProgram.instructionBound,
    ResidualCellUpdateProgram.instructionBound,ResidualUnitUpdateProgram.instructionBound]
  cover_arithmetic

private theorem prepared_candidate {n L V G : ι → ℕ}
    (nn : Covered width n) (ll : Covered width L) (v : Covered width V) (g : Covered width G) :
    Covered width (fun x => CandidatePreparedSolverProgram.instructionBound (n x) (L x) (V x) (G x)) := by
  have cn : Covered width (fun x => CandidatePhysicalCut.networkSize (n x) (L x)) := by
    simp only [CandidatePhysicalCut.networkSize]
    cover_arithmetic
  have cb : Covered width (fun x => CandidatePhysicalCut.budgetCap (n x) (L x)) := by
    simp only [CandidatePhysicalCut.budgetCap]
    cover_arithmetic
  have cw : Covered width (fun x => CandidatePhysicalCut.capacityWidth (n x) (L x)) := by
    simp only [CandidatePhysicalCut.capacityWidth]
    cover_arithmetic
  have ci : Covered width (fun x => CandidateEnumeration.labelBits (n x) (L x)) := by
    simp only [CandidateEnumeration.labelBits]
    cover_arithmetic
  have cut := residual_min_cut cn cw ci cb cb.size
  simp only [CandidatePreparedSolverProgram.instructionBound,CandidateConfiguredCutProgram.instructionBound,
    CandidateInputConfigurationProgram.instructionBound,CandidateSearchConfigurationProgram.instructionBound,
    CandidateBudgetCutProgram.instructionBound,CandidatePhysicalCut.instructionBound,
    CandidateBudgetProgram.instructionBound,WordPairProductProgram.steps,
    CandidateDecoderProgram.instructionBound,CandidateNumeratorScanProgram.instructionBound,
    CandidateNumeratorCellProgram.instructionBound]
  cover_arithmetic

private theorem capacity_matrix {n L V G S : ι → ℕ}
    (nn : Covered width n) (ll : Covered width L) (v : Covered width V) (g : Covered width G)
    (s : Covered width S) :
    Covered width (fun x => CandidateCapacityMatrixProgram.instructionBound (n x) (L x) (V x) (G x) (S x)) := by
  simp only [CandidateCapacityMatrixProgram.instructionBound,CandidateInputNodeListsProgram.instructionBound,
    CandidateNodeListsProgram.steps,CandidateNodeListsProgram.portSteps,
    CandidateCapacitySetupProgram.instructionBound,CandidateBudgetProgram.instructionBound,
    CandidateCapacityTableProgram.instructionBound,CandidateCapacityTableProgram.tableBound,
    CandidateCapacityTableProgram.rowBound,CandidatePhysicalCut.networkSize,CandidatePhysicalCut.budgetCap,
    CandidateCapacityCellProgram.instructionBound,CandidateDescriptorCapacityProgram.instructionBound,
    CandidateTerminalDescriptorProgram.instructionBound,CandidateCoreRelationsProgram.instructionBound,
    CandidateCoreCapacityProgram.instructionBound,CandidatePortEqualityProgram.instructionBound,
    CandidatePortGapAtProgram.instructionBound,CandidateReverseAdjacencyProgram.instructionBound,
    CandidatePortAdjacencyProgram.instructionBound]
  cover_arithmetic

private theorem candidate_refresh {n L V G S : ι → ℕ}
    (nn : Covered width n) (ll : Covered width L) (v : Covered width V) (g : Covered width G)
    (s : Covered width S) :
    Covered width (fun x => CandidateRefreshProgram.instructionBound (n x) (L x) (V x) (G x) (S x)) := by
  have mat := capacity_matrix nn ll v g (s.add (Covered.const 2))
  have solver := prepared_candidate nn ll v g
  simp only [CandidateRefreshProgram.instructionBound,CandidateFamilyProgram.instructionBound,
    CandidateFamilyScanProgram.instructionBound,CandidateFamilyScanProgram.rowLimit,
    CandidateDemandRowProgram.instructionBound,CandidateRawSolverProgram.instructionBound,
    RetainedMassTableProgram.instructionBudget,RetainedMassTableProgram.iterationBudget,
    RetainedMassRowProgram.instructionBudget,EpochActiveFromMaskProgram.flatSteps,ZeroWeightRowProgram.steps]
  cover_arithmetic

private theorem original_setup {n L W : ι → ℕ}
    (nn : Covered width n) (ll : Covered width L) (ww : Covered width W) :
    Covered width (fun x => PhysicalControllerInitializer.instructionBound (n x) (L x) (W x)) := by
  have labels := label_range nn
  have refresh := candidate_refresh nn ll nn.size ll.size (Covered.const 1)
  simp only [PhysicalControllerInitializer.instructionBound,InitialSeedProgram.instructionBound,InitialGraphDictionary.steps,
    WordPairProductProgram.steps,InitialUniformTables.steps,RepeatPointerProgram.steps,
    InitialRetainedStateProgram.instructionBound,RetainedMassTableProgram.instructionBudget,
    RetainedMassTableProgram.iterationBudget,RetainedMassRowProgram.instructionBudget,
    InitialDemandMaskProgram.instructionBound,InitialDemandMaskProgram.rowCap,InitialDemandMaskProgram.pairCap,
    InitialDemandFlagProgram.instructionBound,GraphRecoveryController.instructionBound,
    GraphDiscoveryProgram.discoveryBudget,CostedSupportProgram.recoveryCap]
  cover_arithmetic

private theorem stabilization {n L F H B S R M : ι → ℕ}
    (nn : Covered width n) (ll : Covered width L) (ff : Covered width F) (hh : Covered width H)
    (bb : Covered width B) (ss : Covered width S) (rr : Covered width R) (mm : Covered width M) :
    Covered width (fun x => CacheStabilizeProgram.allocationBound (n x) (L x) (F x) (B x) (S x) (R x) (M x)) ∧
    Covered width (fun x => CacheStabilizeProgram.instructionBound (n x) (L x) (F x) (H x) (B x) (S x) (R x) (M x)) := by
  have refresh := candidate_refresh nn ll nn.size ll.size (ss.add (Covered.const 2))
  constructor
  · simp only [CacheStabilizeProgram.allocationBound,CacheAdvanceProgram.allocationBound,CacheAdvanceProgram.freshBound,
      EpochScanBounds.currentWidth,EpochScanBounds.optimumWidth,CacheGatesProgram.allocationBound,
      AdaptiveGatesProgram.instructionBound,BinaryProductOrderProgram.instructionBound]
    cover_arithmetic
  · simp only [CacheStabilizeProgram.instructionBound,CacheAdvanceProgram.instructionBound,
      CacheAdvanceProgram.allocationBound,CacheAdvanceProgram.freshBound,
      EpochScanBounds.loopBound,EpochScanBounds.currentWidth,EpochScanBounds.optimumWidth,
      CacheGatesProgram.instructionBound,CacheGatesProgram.allocationBound,
      AdaptiveGatesProgram.instructionBound,BinaryProductOrderProgram.instructionBound]
    cover_arithmetic

private theorem epoch {n L F H W B S R M : ι → ℕ}
    (nn : Covered width n) (ll : Covered width L) (ff : Covered width F) (hh : Covered width H)
    (ww : Covered width W) (bb : Covered width B) (ss : Covered width S)
    (rr : Covered width R) (mm : Covered width M) :
    Covered width (fun x => PhysicalEpochScanProgram.allocationBound (n x) (L x) (F x) (W x) (B x) (S x) (R x) (M x)) ∧
    Covered width (fun x => PhysicalEpochScanProgram.instructionBound
      (n x) (L x) (F x) (H x) (W x) (B x) (S x) (R x) (M x)) := by
  have refresh := candidate_refresh nn ll nn.size ll.size ss
  have draw : Covered width (fun x => PhysicalEpochInputProgram.instructionBound (n x) (L x) (F x)) := by
    simp only [PhysicalEpochInputProgram.instructionBound,EpochActiveFromMaskProgram.instructionBound,EpochActiveFromMaskProgram.flatSteps,
      RetainedEpochFromMasks.instructionBound,RetainedEpochFromMasks.width,RetainedEpochScheduleProgram.instructionBound,
      PhysicalDrawSequenceProgram.instructionBound,PhysicalBoundedDrawProgram.instructionBound,
      EpochPermutationProgram.instructionBound,EpochGridTableProgram.steps]
    cover_arithmetic
  have update : Covered width (fun x => EpochScanBounds.roundBound (n x) (L x) (n x*n x) (W x) (B x) (S x)) := by
    simp only [EpochScanBounds.roundBound,AdaptiveRoundRefreshProgram.instructionBound,
      EpochSelectedRoundProgram.instructionBound]
    cover_arithmetic
  constructor
  · simp only [PhysicalEpochScanProgram.allocationBound,EpochScanBounds.stepCells,EpochScanHeadProgram.allocationBound,
      EpochScanBounds.currentWidth,EpochScanBounds.optimumWidth,
      CacheGatesProgram.allocationBound,AdaptiveGatesProgram.instructionBound,BinaryProductOrderProgram.instructionBound]
    cover_arithmetic
  · simp only [PhysicalEpochScanProgram.instructionBound,EpochScanBounds.loopBound,EpochScanBounds.stepCells,
      EpochScanBounds.baseInstructions,EpochScanHeadProgram.allocationBound,EpochScanHeadProgram.instructionBound,
      EpochScanBounds.currentWidth,EpochScanBounds.optimumWidth,
      CacheGatesProgram.allocationBound,CacheGatesProgram.instructionBound,AdaptiveGatesProgram.instructionBound,
      BinaryProductOrderProgram.instructionBound]
    cover_arithmetic

private theorem controller {n L T F W B S R M E H : ι → ℕ}
    (nn : Covered width n) (ll : Covered width L) (tt : Covered width T) (ff : Covered width F)
    (ww : Covered width W) (bb : Covered width B) (ss : Covered width S) (rr : Covered width R)
    (mm : Covered width M) (ee : Covered width E) (hh : Covered width H) :
    Covered width (fun x => OriginalGraphControllerProgram.instructionBound
      ⟨n x,L x,T x,F x,W x,B x,S x,R x,M x⟩ (E x) (H x)) := by
  have setup := original_setup nn ll ww
  obtain ⟨alloc,stable⟩ := stabilization nn ll ff (Covered.const 0) bb ss rr mm
  have mw : Covered width (fun x => EpochScanBounds.currentWidth (n x) (B x)) := by
    simp only [EpochScanBounds.currentWidth]
    cover_arithmetic
  have z : Covered width (fun x => 0+CacheStabilizeProgram.allocationBound (n x) (L x) (F x) (B x) (S x) (R x) (M x)+
      EpochScanBounds.currentWidth (n x) (B x)+4) := by cover_arithmetic
  obtain ⟨cells,scan⟩ := epoch nn ll tt z ww bb ss rr mw
  simp only [OriginalGraphControllerProgram.instructionBound,AdaptiveControllerBounds.instructionBound,
    AdaptiveControllerBounds.loopLimit,Limits.slope,Limits.stepCells,Limits.stepInstructions,
    Limits.threshold,Limits.epochCells,Limits.epochInstructions,Limits.stabilizeCells,Limits.stabilizeInstructions,
    ControllerEpochParameters.instructionBound]
  cover_arithmetic

theorem raw_charge_covered {n L H A : ι → ℕ} {trials : ι → Bits}
    (nn : Covered width n) (ll : Covered width L) (hh : Covered width H) (aa : Covered width A)
    (tt : Covered width (fun x => value (trials x))) (tw : Covered width (fun x => (trials x).length)) :
    Covered width (fun x => RawGraphControllerProgram.chargeBound (n x) (L x) (H x) (A x) (trials x)) := by
  have restart : Covered width (fun x => IntegerEpochParameters.restart (n x)) := by
    simp only [IntegerEpochParameters.restart,Nat.log2_eq_log_two]
    cover_arithmetic
  have epochs : Covered width (fun x => OriginalGraphControllerLaw.epochs (n x)) := by
    simp only [OriginalGraphControllerLaw.epochs,IntegerEpochParameters.fuel]
    cover_arithmetic
  have ratio : Covered width (fun x => (OriginalGraphControllerLaw.ratio (n x)).length) := by
    simpa only [OriginalGraphControllerLaw.ratio,Nat.size_eq_bits_len] using restart.size
  have b : Covered width (fun x => RawGraphControllerProgram.weightWidth (L x)) := by
    simp only [RawGraphControllerProgram.weightWidth]
    cover_arithmetic
  have w : Covered width (fun x => RawGraphControllerProgram.wordWidth (n x) (L x)) := by
    simp only [RawGraphControllerProgram.wordWidth,RetainedEpochFromMasks.width]
    cover_arithmetic
  have s : Covered width (fun x => RawGraphControllerProgram.scaleWidth (n x)) := by
    simp only [RawGraphControllerProgram.scaleWidth]
    cover_arithmetic
  have prep : Covered width (fun x => RawGraphControllerProgram.preparationBound (n x) (trials x)) := by
    simp only [RawGraphControllerProgram.preparationBound,PhysicalControllerControls.instructionBound,
      OriginalControlWordsProgram.restartLimit,OriginalControlWordsProgram.cubeLimit,PhysicalControllerControls.logLimit,
      BinaryGeometricCounterProgram.stepBound]
    cover_arithmetic
  have total := controller nn ll tt epochs w b s ratio (Covered.const 0) epochs (hh.add prep)
  have steps : Covered width (fun x => RawGraphControllerProgram.instructionBound (n x) (L x) (H x) (trials x)) := by
    simp only [RawGraphControllerProgram.instructionBound,RawGraphControllerProgram.limits]
    cover_arithmetic
  simp only [RawGraphControllerProgram.chargeBound,completeBound,runBound,stepBound,controlCost,
    GuardedReferenceExecution.guardCost]
  cover_arithmetic

end Formulas

open RawGraphControllerProgram (chargeBound instructionBound)
open RawGraphInputStore (cells prepare)
open OriginalGraphControllerLaw (epochs ratio readBound)
open RetainedGridState (PairFlags)
open IntegralNetworkFlow

/-- The confidence parameter is fixed in this bound. Its numerical size enters
the polynomial coefficient, while the graph and level words are its input. -/
def confidenceTrials (n κ : ℕ) : ℕ :=
  FairBitConfidence.trials (epochs n*(2*n*n)) (EncodedVertexAmplification.confidenceExponent n κ)

def originalWidth (n L : ℕ) : ℕ := n+n*n+n.bits.length+L.bits.length+1

def preparedCells (n L T : ℕ) : ℕ :=
  11+2*(n+n*n+n.bits.length+L.bits.length+T.bits.length)

theorem preparedCells_eq {n : ℕ} (adj : PairFlags n) (L T : ℕ) :
    cells (GraphRelaxationRefinement.matrix adj) n.bits L.bits T.bits=preparedCells n L T := by
  rw [cells,preparedCells,GraphRelaxationRefinement.matrix_length]
  have h : PackedOriginalStore.rowBits (GraphRelaxationRefinement.matrix adj)=n*n := by
    simp [PackedOriginalStore.rowBits,GraphRelaxationRefinement.matrix,List.map_map,Function.comp_def]
  rw [h]

def packedCost (n L T : ℕ) : ℕ :=
  let H := preparedCells n L T
  64*H^3+16+chargeBound n L (H+1) H T.bits

private def Parameters := { p : ℕ × ℕ // p.2 ≤ p.1 }

private theorem total_covered (κ : ℕ) :
    Covered (fun p : Parameters => originalWidth p.1.1 p.1.2)
      (fun p => packedCost p.1.1 p.1.2 (confidenceTrials p.1.1 κ)) := by
  let width (p : Parameters) := originalWidth p.1.1 p.1.2
  have n : Covered width (fun p => p.1.1) := Covered.id.of_le (fun p => by unfold width originalWidth; omega)
  have L : Covered width (fun p => p.1.2) := n.of_le Subtype.property
  have T : Covered width (fun p => confidenceTrials p.1.1 κ) := by
    simp only [confidenceTrials,FairBitConfidence.trials,FairBitWords.width,EncodedVertexAmplification.confidenceExponent,
      OriginalGraphControllerLaw.epochs,IntegerEpochParameters.fuel,IntegerEpochParameters.restart,Nat.log2_eq_log_two]
    cover_arithmetic
  have S : Covered width (fun p => preparedCells p.1.1 p.1.2 (confidenceTrials p.1.1 κ)) := by
    simp only [preparedCells,Nat.size_eq_bits_len]
    cover_arithmetic
  have q := raw_charge_covered n L (S.add (Covered.const 1)) S
    (trials:=fun p => (confidenceTrials p.1.1 κ).bits)
    (by simpa only [value_bits] using T) (by simpa only [Nat.size_eq_bits_len] using T.size)
  change Covered width _
  simp only [packedCost]
  cover_arithmetic

/-- A fixed polynomial bounds packing plus guarded execution for every original
graph and every positive level in the controller's active range. -/
theorem packed_bit_time (κ : ℕ) :
    ∃ p : Polynomial ℕ, ∀ (n L : ℕ), L≤n →
      packedCost n L (confidenceTrials n κ) ≤ p.eval (originalWidth n L) := by
  obtain ⟨p,h⟩ := total_covered κ
  exact ⟨p,fun n L inside => h ⟨(n,L),inside⟩⟩

private theorem packed_general_covered :
    Covered (fun x : Parameters × ℕ => x.1.1.1+x.2) (fun x => packedCost x.1.1.1 x.1.1.2 x.2) := by
  let width (x : Parameters × ℕ) := x.1.1.1+x.2
  have n : Covered width (fun x => x.1.1.1) := Covered.id.of_le (fun _ => Nat.le_add_right _ _)
  have L : Covered width (fun x => x.1.1.2) := n.of_le (fun x => x.1.property)
  have T : Covered width (fun x => x.2) := Covered.id.of_le (fun _ => Nat.le_add_left _ _)
  have S : Covered width (fun x => preparedCells x.1.1.1 x.1.1.2 x.2) := by
    simp only [preparedCells,Nat.size_eq_bits_len]
    cover_arithmetic
  have q := raw_charge_covered n L (S.add (Covered.const 1)) S (trials:=fun x => x.2.bits)
    (by simpa only [value_bits] using T) (by simpa only [Nat.size_eq_bits_len] using T.size)
  change Covered width _
  simp only [packedCost]
  cover_arithmetic

theorem bounded_trials_polynomial :
    ∃ p : Polynomial ℕ, ∀ n L T, L≤n → packedCost n L T ≤ p.eval (n+T) := by
  obtain ⟨p,h⟩ := packed_general_covered
  exact ⟨p,fun n L T inside => h (⟨(n,L),inside⟩,T)⟩

set_option maxHeartbeats 1800000 in
theorem solve_packed (κ : ℕ) :
    ∃ p : Polynomial ℕ, ∀ {n L : ℕ} (adj : PairFlags n) (positive : 0<L) (_inside : L≤n) (tape : Bits),
      let T := confidenceTrials n κ
      let H := preparedCells n L T
      let input := prepare (GraphRelaxationRefinement.matrix adj) n.bits L.bits T.bits tape
      readBound n L T ≤ tape.length →
      ∃ out paid cut,
        GuardedReferenceExecution.execute RawGraphControllerProgram.program
          (instructionBound n L (H+1) T.bits+1) input.1 0=some (out,paid) ∧
        PhysicalCoverReader.readWord (eraseState out).heap (eraseState out).registers.d=some cut ∧
        (RawGraphControllerLaw.readCut (n:=n) cut)∈
          (FiniteDrawTrees.ideal (LazyFairBitTrees.lower T
            (OriginalGraphControllerLaw.cutTree (adj:=adj) positive (CandidateEnumeration.make n L).network.enumeration))).support ∧
        input.2+paid ≤ p.eval (originalWidth n L) := by
  obtain ⟨p,cost⟩ := packed_bit_time κ
  refine ⟨p,?_⟩
  intro n L adj positive inside tape
  dsimp only
  intro enough
  let T := confidenceTrials n κ
  let H := preparedCells n L T
  let E := (CandidateEnumeration.make n L).network.enumeration
  let EN := (CandidateEnumeration.make n L).nodes.enumeration
  let input := prepare (GraphRelaxationRefinement.matrix adj) n.bits L.bits T.bits tape
  obtain ⟨data,packing⟩ := RawGraphInputStore.prepare_spec (L:=L) adj T.bits tape
  simp only [preparedCells_eq] at data packing
  have observed := RawGraphControllerProgram.guarded_cut positive EN E input.1
    data.bounded data.entry data.quiet data.dense data.graph data.trials
  have source : input.1.source=tape := rfl
  rw [value_bits,source] at observed
  obtain ⟨result,used,exactRun,usedBound⟩ :=
    OriginalGraphControllerLaw.tape_complete (adj:=adj) positive E T tape enough
  rw [exactRun] at observed
  obtain ⟨out,paid,physical,mem,tail,_,_,_,paidBound⟩ := observed
  refine ⟨out,paid,result.data.cut.toList,physical,mem,?_,?_⟩
  · rw [RawGraphControllerLaw.readCut_flags]
    have cut := OriginalGraphControllerLaw.cutRun_eq (adj:=adj) positive E T tape
    rw [OriginalGraphControllerLaw.cutRun,exactRun] at cut
    -- The successful literal run belongs to the support of its binary tree.
    have hres : ∃ suffix, EncodedSolverBits.run
        (LazyFairBitTrees.lower T (OriginalGraphControllerLaw.cutTree (adj:=adj) positive E)) tape =
          some (RetainedGridState.cutSet result.data.cut,suffix) := by
      rw [OriginalGraphControllerLaw.cutTree_eq]
      change ∃ suffix, EncodedSolverBits.run (RetainedFairBitLaw.bitTree T _ _ _ _ _ _ _) tape = _
      have h := cut.symm
      cases hobs : EncodedSolverBits.run (RetainedFairBitLaw.bitTree T _ _ _ _ _ _ _) tape with
      | none => rw [hobs] at h; simp at h
      | some outcome =>
        rcases outcome with ⟨X,suffix⟩
        rw [hobs] at h
        have hx : X=RetainedGridState.cutSet result.data.cut := Option.some.inj h
        exact ⟨suffix,congrArg (fun Y => some (Y,suffix)) hx⟩
    obtain ⟨suffix,hs⟩ := hres
    exact EncodedSolverBits.run_support (LazyFairBitTrees.lower_binary T _) hs
  · exact (Nat.add_le_add packing paidBound).trans (cost n L inside)

end DirectedFlowCutGap.OriginalGraphCostEnvelope
