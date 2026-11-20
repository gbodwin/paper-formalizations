import DirectedFlowCutGap.RunnerPreparationLayout
import DirectedFlowCutGap.VertexMaskProjectionArrays

/-! Keep exactly the modeled arrays produced when the inner projections run.
A cutoff that returns no result does not start a mask pullback. -/
namespace DirectedFlowCutGap.RunnerProjectionLayout

open BinaryArithmetic EncodedArrayStorage EncodedUnitCostReplication Polynomial
open BinaryArrayNestedStorage (Code WithChildren copyBudget cellBudget copyBudget_eval cellBudget_eval)
open ArrayMaterializationLayout (flat)
open VertexPreparationBounds (flat_le)
open EncodedUniformChain (materializeWith)
open EncodedUnitCostPreparation (build prepareAndReduce build_size_le build_clone_count empty_objective_zero)
open PhysicalIntegerRoundingCost (eval_mono)

def uniformCode {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) : Code :=
  let p := (BinaryUniformArithmetic.compute D).1
  if (BinaryRawRational.le RawNonnegativeRational.Code.one p.total).1 then
    let level := BinaryUniformArithmetic.cutoff p.average
    let chain := materializeWith p.ports p.average p.counts level.1
    if (GuardedCutoffWork.runBinary T chain.data.adjacency chain.cutoff tape).1.isSome then
      flat chain.size++flat n
    else []
  else []

def uniformModel {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) (trace : Code) : Prop :=
  let p := (BinaryUniformArithmetic.compute D).1
  if (BinaryRawRational.le RawNonnegativeRational.Code.one p.total).1 then
    let level := BinaryUniformArithmetic.cutoff p.average
    let chain := materializeWith p.ports p.average p.counts level.1
    match (GuardedCutoffWork.runBinary T chain.data.adjacency chain.cutoff tape).1 with
    | none => trace=[]
    | some (cut,_) => trace=flat chain.size++flat n ∧
      WithChildren (EncodedUniformOutput.originalView chain).ports (fun _ => []) (flat chain.size) ∧
      WithChildren (EncodedUniformOutput.originalMaskWithCost chain cut.mask).1 (fun _ => []) (flat n)
  else trace=[]

attribute [local irreducible] BinaryUniformArithmetic.compute materializeWith GuardedCutoffWork.runBinary in
set_option maxHeartbeats 700000 in
theorem uniform_model {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) :
    uniformModel T D tape (uniformCode T D tape) := by
  simp only [uniformModel,uniformCode]
  split
  · let p := (BinaryUniformArithmetic.compute D).1
    let level := BinaryUniformArithmetic.cutoff p.average
    let chain := materializeWith p.ports p.average p.counts level.1
    cases (GuardedCutoffWork.runBinary T chain.data.adjacency chain.cutoff tape).1 with
    | none => simp only [Option.isSome_none,Bool.false_eq_true,ite_false]
    | some answer =>
      obtain ⟨cut,fee⟩ := answer
      simp only [Option.isSome_some,ite_true,true_and]
      exact VertexMaskProjectionArrays.uniform chain cut.mask
  · rfl

def weightedCode {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) : Code :=
  let prepared := (BinaryPortPreparation.prepareAndReduce D).1
  match prepared.reduced with
  | .zero _ _ => flat n
  | .replicated _ _ replica _ => uniformCode T replica.input tape++
    if (PaidVertexRounding.uniform T replica.input tape).1.isSome then
      flat prepared.prepared.size++flat n
    else []

def weightedModel {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) (trace : Code) : Prop :=
  let prepared := (BinaryPortPreparation.prepareAndReduce D).1
  match prepared.reduced with
  | .zero mask _ => trace=flat n ∧ WithChildren (prepared.prepared.pullbackMaskWithCost mask).1 (fun _ => []) (flat n)
  | .replicated _ counts replica _ =>
    uniformModel T replica.input tape (uniformCode T replica.input tape) ∧
    match (PaidVertexRounding.uniform T replica.input tape).1 with
    | none => trace=uniformCode T replica.input tape
    | some result =>
      let mask := result.cut.mask
      let fiber := (fullFiberMaskWithCost counts replica.labels mask).1
      trace=uniformCode T replica.input tape++flat prepared.prepared.size++flat n ∧
        WithChildren fiber (fun _ => []) (flat prepared.prepared.size) ∧
        WithChildren (prepared.prepared.pullbackSampleWithCost counts replica mask).1 (fun _ => []) (flat n)

attribute [local irreducible] BinaryPortPreparation.prepareAndReduce PaidVertexRounding.uniform in
set_option maxHeartbeats 850000 in
theorem weighted_model {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) :
    weightedModel T D tape (weightedCode T D tape) := by
  let prepared := (BinaryPortPreparation.prepareAndReduce D).1
  simp only [weightedModel,weightedCode]
  cases prepared.reduced with
  | zero mask work => exact ⟨rfl,VertexMaskProjectionArrays.port _ mask⟩
  | replicated normalized counts replica work =>
    refine ⟨uniform_model T replica.input tape,?_⟩
    cases ran : (PaidVertexRounding.uniform T replica.input tape).1 with
    | none => simp only [ran,Option.isSome_none,Bool.false_eq_true,ite_false,List.append_nil]
    | some result =>
      simp only [ran,Option.isSome_some,ite_true,List.append_assoc,true_and]
      exact VertexMaskProjectionArrays.parallel _ counts replica result.cut.mask

def code {n : ℕ} (mode : ChargedVertexModes.Mode) (T : ℕ) (D : Input n) (tape : Bits) : Code :=
  match mode with
  | .mass => weightedCode T D tape
  | .size =>
    let prep := (BinaryHeavyPreparation.prepare D).1.1
    weightedCode T prep.data tape++
      if (PaidVertexRounding.weighted T prep.data tape).1.isSome then flat prep.size++flat n++flat n else []


theorem heavy_model {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) :
    let prep := (BinaryHeavyPreparation.prepare D).1.1
    weightedModel T prep.data tape (weightedCode T prep.data tape) ∧
      match (PaidVertexRounding.weighted T prep.data tape).1 with
      | none => code .size T D tape=weightedCode T prep.data tape
      | some result =>
        let view := EncodedHeavyVertexPreparation.liftView prep
        code .size T D tape=weightedCode T prep.data tape++flat prep.size++flat n++flat n ∧
          WithChildren view.ports (fun _ => []) (flat prep.size) ∧
          WithChildren (view.pullbackMaskWithCost result.cut.mask).1 (fun _ => []) (flat n) ∧
          WithChildren (EncodedHeavyVertexPreparation.combinedMaskWithCost prep result.cut.mask).1
            (fun _ => []) (flat n) := by
  let prep := (BinaryHeavyPreparation.prepare D).1.1
  refine ⟨weighted_model T prep.data tape,?_⟩
  cases ran : (PaidVertexRounding.weighted T prep.data tape).1 with
  | none => simp only [code,ran,Option.isSome_none,Bool.false_eq_true,ite_false,List.append_nil,prep]
  | some result =>
    simp only [code,ran,Option.isSome_some,ite_true,List.append_assoc,true_and,prep]
    exact VertexMaskProjectionArrays.heavy prep result.cut.mask

open EncodedUniformWeightParameters in
attribute [local irreducible] BinaryUniformArithmetic.compute materializeWith GuardedCutoffWork.runBinary in
set_option maxHeartbeats 700000 in
private theorem uniform_bound {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) {bound : ℕ} (fits : 6*n≤bound) :
    (uniformCode T D tape).length ≤ 2*copyBudget bound ∧ fresh (uniformCode T D tape) ≤ 2*cellBudget bound := by
  unfold uniformCode
  dsimp only
  split
  · rename_i active
    rw [BinaryRawRational.le_value,BinaryUniformArithmetic.compute_value] at active
    have positive : 0 < (compute D).total.realValue := by
      rw [compute_total]
      exact lt_of_lt_of_le (by norm_num) ((nontrivial_iff D).mp active)
    let p := (BinaryUniformArithmetic.compute D).1
    let chain := materializeWith p.ports p.average p.counts (BinaryUniformArithmetic.cutoff p.average).1
    have count : chain.size≤6*n := by
      rw [chain.size_eq]
      dsimp only [p]
      rw [BinaryUniformArithmetic.compute_value]
      exact clone_count D positive
    obtain ⟨chainWork,chainSpace⟩ := flat_le (count.trans fits)
    obtain ⟨maskWork,maskSpace⟩ := flat_le (show n≤bound by omega)
    simp only [chain,p] at chainWork chainSpace
    split
    · simp only [List.length_append,fresh_append]
      constructor <;> omega
    · exact ⟨Nat.zero_le _,Nat.zero_le _⟩
  · exact ⟨Nat.zero_le _,Nat.zero_le _⟩

attribute [local irreducible] EncodedUnitCostPreparation.build BinaryPortPreparation.prepareAndReduce
  PaidVertexRounding.uniform in
set_option maxHeartbeats 1200000 in
private theorem weighted_bound {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) {bound : ℕ}
    (fits : 24*n^2+3*n ≤ bound) :
    (weightedCode T D tape).length ≤ 4*copyBudget bound ∧ fresh (weightedCode T D tape) ≤ 4*cellBudget bound := by
  let prep := build D
  have orig : n≤bound := by omega
  have port : prep.size≤bound := (build_size_le D).trans (by omega)
  obtain ⟨maskWork,maskSpace⟩ := flat_le orig
  obtain ⟨fiberWork,fiberSpace⟩ := flat_le port
  simp only [prep] at fiberWork fiberSpace
  unfold weightedCode
  rw [BinaryPortPreparation.prepareAndReduce_value]
  dsimp only [prepareAndReduce]
  by_cases zero : prep.data.totals.objective.num=0
  · rw [Input.reduce_zero _ zero]
    dsimp only
    constructor <;> omega
  · have positive : 0<n := by
      by_contra empty
      obtain rfl : n=0 := by omega
      exact zero (empty_objective_zero D)
    let replica := materialize prep.data prep.data.counts
    have small : (cloneList prep.data.counts).length ≤ 4*n^2 := build_clone_count D positive zero
    have count : 6*(cloneList prep.data.counts).length≤bound := by omega
    obtain ⟨uniformWork,uniformSpace⟩ := uniform_bound T replica.input tape (bound := bound) count
    simp only [replica,prep,Input.counts] at uniformWork uniformSpace
    rw [Input.reduce_positive _ zero]
    dsimp only
    split
    · simp only [List.length_append,fresh_append,prep]
      constructor <;> omega
    · simp only [List.append_nil,prep]
      constructor <;> omega

set_option maxHeartbeats 1200000 in
theorem polynomial : ∃ cells copies : Polynomial ℕ, ∀ {n : ℕ}
    (mode : ChargedVertexModes.Mode) (T : ℕ) (D : Input n) (tape : Bits),
    fresh (code mode T D tape)≤cells.eval n ∧ (code mode T D tape).length≤copies.eval n := by
  let p : Polynomial ℕ := 24*X^2+3*X
  refine ⟨7*cellBudget p,7*copyBudget p,?_⟩
  intro n mode T D tape
  let B := 24*n^2+3*n
  have h : n≤B := by dsimp only [B]; omega
  simp only [eval_mul,eval_ofNat,cellBudget_eval,copyBudget_eval,p,eval_add,eval_pow,eval_X]
  change fresh (code mode T D tape)≤7*cellBudget B ∧ (code mode T D tape).length≤7*copyBudget B
  cases mode with
  | mass =>
    obtain ⟨work,space⟩ := weighted_bound T D tape (bound := B) le_rfl
    change fresh (weightedCode T D tape)≤_ ∧ (weightedCode T D tape).length≤_
    constructor <;> omega
  | size =>
    let prep := (BinaryHeavyPreparation.prepare D).1.1
    have remaining : prep.size≤n := by
      change (BinaryHeavyPreparation.prepare D).1.1.size≤n
      rw [BinaryHeavyPreparation.prepare_value]
      exact EncodedHeavyVertexPreparation.build_size_le D (EncodedCubeRootThreshold.threshold n)
    have pad : 24*prep.size^2+3*prep.size≤B := by
      dsimp only [B]
      gcongr
    obtain ⟨weightedWork,weightedSpace⟩ := weighted_bound T prep.data tape pad
    obtain ⟨labelWork,labelSpace⟩ := flat_le (remaining.trans h)
    obtain ⟨maskWork,maskSpace⟩ := flat_le h
    simp only [prep] at weightedWork weightedSpace labelWork labelSpace
    simp only [code]
    split
    · simp only [List.length_append,fresh_append]
      constructor <;> omega
    · simp only [List.append_nil]
      constructor <;> omega

def Model {n : ℕ} (mode : ChargedVertexModes.Mode) (T : ℕ) (D : Input n) (tape : Bits) (trace : Code) : Prop :=
  ∃ prior, RunnerPreparationLayout.Model mode T D tape prior ∧ trace=prior++code mode T D tape

theorem arrays : ∃ cells copies : Polynomial ℕ, ∀ {n : ℕ}
    (mode : ChargedVertexModes.Mode) (T : ℕ) (D : Input n) (tape : Bits),
    ∃ trace, Model mode T D tape trace ∧ fresh trace≤cells.eval (n+T) ∧ trace.length≤copies.eval (n+T) := by
  obtain ⟨beforeCells,beforeCopies,before⟩ := RunnerPreparationLayout.arrays
  obtain ⟨afterCells,afterCopies,after⟩ := polynomial
  refine ⟨beforeCells+afterCells,beforeCopies+afterCopies,?_⟩
  intro n mode T D tape
  obtain ⟨prior,modeled,beforeSpace,beforeWork⟩ := before mode T D tape
  obtain ⟨afterSpace,afterWork⟩ := after mode T D tape
  refine ⟨prior++code mode T D tape,⟨prior,modeled,rfl⟩,?_,?_⟩
  · simp only [fresh_append,eval_add]
    exact Nat.add_le_add beforeSpace (afterSpace.trans (eval_mono _ (Nat.le_add_right _ _)))
  · simp only [List.length_append,eval_add]
    exact Nat.add_le_add beforeWork (afterWork.trans (eval_mono _ (Nat.le_add_right _ _)))

end DirectedFlowCutGap.RunnerProjectionLayout
