import DirectedFlowCutGap.GuardedCutoffWork
import DirectedFlowCutGap.PhysicalAmplifiedBinaryVertex

/-! Preserve incurred work through the existing binary preprocessing and mask
pullbacks, including the case where packed rounding exhausts its tape. -/
namespace DirectedFlowCutGap.PaidVertexRounding

open BinaryArithmetic RetainedGridState RawNonnegativeRational
open EncodedUnitCostReplication
open PhysicalBinaryVertexRounding (Result)
open PhysicalCoverAccess (Read)
open VertexReductionWidths (InputFits)

private def project {n m : ℕ} (decode : Flags m → Flags n × ℕ) (work arithmeticBase arithmeticEnd : ℕ)
    (r : Read (Result m)) : Read (Result n) :=
  let base := work+arithmeticBase+arithmeticEnd+r.2
  match r.1 with
  | none => (none,base)
  | some result =>
      let pulled := decode result.cut.mask
      (some ⟨⟨pulled.1,result.cut.suffix,work+result.cut.paid+pulled.2⟩,
        arithmeticBase+result.arithmetic+arithmeticEnd⟩,base+pulled.2)

private theorem project_value {n m : ℕ} (decode : Flags m → Flags n × ℕ) (work arithmeticBase arithmeticEnd : ℕ)
    (r : Read (Result m)) : (project decode work arithmeticBase arithmeticEnd r).1=r.1.map (fun result =>
      ⟨PhysicalVertexRounding.project decode work result.cut,arithmeticBase+result.arithmetic+arithmeticEnd⟩) := by
  unfold project
  cases r.1 <;> rfl

private theorem project_paid {n m : ℕ} (decode : Flags m → Flags n × ℕ) (work arithmeticBase arithmeticEnd : ℕ)
    (r : Read (Result m)) {prepare core finish : ℕ} (first : work+arithmeticBase+arithmeticEnd ≤ prepare)
    (round : r.2 ≤ core) (each : ∀ mask, (decode mask).2 ≤ finish) :
    (project decode work arithmeticBase arithmeticEnd r).2 ≤ prepare+core+finish := by
  unfold project
  have base := Nat.add_le_add first round
  cases r.1 with
  | none => exact base.trans (Nat.le_add_right _ _)
  | some cut => exact Nat.add_le_add base (each cut.cut.mask)

section Uniform

open EncodedUniformChain EncodedUniformOutput EncodedUniformWeightParameters

def uniform {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) : Read (PhysicalBinaryVertexRounding.Result n) :=
  let ready := BinaryUniformArithmetic.compute D
  let p := ready.1
  let test := BinaryRawRational.le Code.one p.total
  if test.1 then
    let level := BinaryUniformArithmetic.cutoff p.average
    let chain := materializeWith p.ports p.average p.counts level.1
    let cut := GuardedCutoffWork.runBinary T chain.data.adjacency chain.cutoff tape
    project (originalMaskWithCost chain) (p.work+chain.work+10) (ready.2+test.2+level.2) 6
      (cut.1.map (fun (r,q) => ⟨r,q⟩),cut.2)
  else
    let work := p.work+4*n+10
    let paid := ready.2+test.2+6
    (some ⟨⟨Vector.replicate n false,tape,work⟩,paid⟩,work+paid)

theorem uniform_value {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) :
    (uniform T D tape).1=PhysicalBinaryVertexRounding.uniform T D tape := by
  unfold uniform PhysicalBinaryVertexRounding.uniform
  dsimp only
  split
  · simp only [project_value,GuardedCutoffWork.binary_value,Option.map_map,Function.comp_def]
  · rfl

theorem uniform_paid (p : Polynomial ℕ) (bounds : ∀ n L T, GuardedCutoffWork.budget n L T ≤ p.eval (n+T))
    {n b : ℕ} (T : ℕ) (D : Input n) (fits : InputFits D b) (tape : Bits) :
    (uniform T D tape).2 ≤ PhysicalVertexRoundingCost.uniformBudget p n T+PhysicalBinaryVertexRounding.uniformBudget n b := by
  let ready := BinaryUniformArithmetic.compute D
  let test := BinaryRawRational.le Code.one ready.1.total
  let level := BinaryUniformArithmetic.cutoff ready.1.average
  let chain := materializeWith ready.1.ports ready.1.average ready.1.counts level.1
  have eq : ready.1=compute D := BinaryUniformArithmetic.compute_value D
  obtain ⟨total,avg,_⟩ := VertexReductionWidths.uniform_fields D fits
  have measured : ready.2 ≤ _ := BinaryUniformArithmetic.compute_paid D fits
  have ht : ready.1.total.Bounded (VertexReductionWidths.uniformWidth n b) := eq.symm ▸ total
  have ha : ready.1.average.Bounded (VertexReductionWidths.uniformWidth n b) := eq.symm ▸ avg
  have cmp : test.2 ≤ _ := BinaryRawRational.le_paid (Code.bounded_mono Code.bounded_one (Nat.zero_le _)) ht
  have k : level.2 ≤ _ := BinaryUniformArithmetic.cutoff_paid ha
  have counted : ready.1.work=(compute D).work := congrArg Parameters.work eq
  unfold uniform
  dsimp only
  split
  next pass =>
    have positive : nontrivial D=true := by
      change (BinaryRawRational.le Code.one ready.1.total).1=true at pass
      rw [BinaryRawRational.le_value,eq] at pass
      exact pass
    have mass : 0<(compute D).total.realValue := by
      rw [compute_total]
      exact lt_of_lt_of_le (by norm_num) ((nontrivial_iff D).mp positive)
    let Dimensions (parameters : Parameters n) (k : ℕ) : Prop :=
      let c := materializeWith parameters.ports parameters.average parameters.counts k
      c.cutoff ≤ c.size ∧ c.size ≤ 6*n ∧ c.work ≤ 2160*n^2+351*n+36 ∧
        ∀ mask, (originalMaskWithCost c mask).2 ≤ 120*n^2+224*n+24
    have limits : Dimensions ready.1 level.1 := by
      change Dimensions ready.1 (BinaryUniformArithmetic.cutoff ready.1.average).1
      rw [BinaryUniformArithmetic.cutoff_value,eq]
      exact ⟨(expand_cutoff_bounds D positive).2,expand_size_bound D mass,computed_work_bound D mass,
        computed_originalMask_work D mass⟩
    obtain ⟨inside,dimension,material,unpack⟩ := limits
    change chain.work ≤ 2160*n^2+351*n+36 at material
    change ∀ mask : Flags chain.size, (originalMaskWithCost chain mask).2 ≤ 120*n^2+224*n+24 at unpack
    let cut := GuardedCutoffWork.runBinary T chain.data.adjacency chain.cutoff tape
    let inner : Read (PhysicalBinaryVertexRounding.Result chain.size) := (cut.1.map (fun (r,q) => ⟨r,q⟩),cut.2)
    have gate : inner.2 ≤ p.eval (6*n+T)+BinaryIntegerCutoff.budget (6*n) (6*n) := by
      have levelBound := (BinaryNaturalOperations.size_le_self chain.cutoff).trans (inside.trans dimension)
      exact (GuardedCutoffWork.binary_paid (T:=T) chain.data.adjacency tape levelBound).trans
        (Nat.add_le_add ((bounds _ _ _).trans (PhysicalIntegerRoundingCost.eval_mono p (Nat.add_le_add_right dimension T)))
          (BinaryIntegerCutoff.budget_mono dimension (Nat.le_refl _)))
    change (project (originalMaskWithCost chain) (ready.1.work+chain.work+10)
      (ready.2+test.2+level.2) 6 inner).2 ≤ _
    refine (project_paid _ _ _ _ _ (Nat.le_refl _) gate unpack).trans ?_
    rw [counted,compute_work]
    unfold PhysicalVertexRoundingCost.uniformBudget PhysicalBinaryVertexRounding.uniformBudget
    omega
  next =>
    change ready.1.work+4*n+10+(ready.2+test.2+6) ≤ _
    rw [counted,compute_work]
    unfold PhysicalVertexRoundingCost.uniformBudget PhysicalBinaryVertexRounding.uniformBudget
    omega

end Uniform

section Weighted

open EncodedUnitCostPreparation

private def weightedWith {n : ℕ} (T : ℕ) (r : Reduction n) (paid : ℕ) (tape : Bits) : Read (Result n) :=
  match r.reduced with
  | .zero mask _ =>
      let out := r.prepared.pullbackMaskWithCost mask
      let work := r.work+out.2+5
      (some ⟨⟨out.1,tape,work⟩,paid+4⟩,work+paid+4)
  | .replicated _ counts replica _ =>
      project (r.prepared.pullbackSampleWithCost counts replica) (r.work+5) (paid+4) 0 (uniform T replica.input tape)

def weighted {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) : Read (Result n) :=
  let prep := BinaryPortPreparation.prepareAndReduce D
  weightedWith T prep.1 prep.2 tape

theorem weighted_value {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) :
    (weighted T D tape).1=PhysicalBinaryVertexRounding.weighted T D tape := by
  let r := (BinaryPortPreparation.prepareAndReduce D).1
  let work := (BinaryPortPreparation.prepareAndReduce D).2
  change (weightedWith T r work tape).1=(match r.reduced with
    | .zero mask _ =>
        let out := r.prepared.pullbackMaskWithCost mask
        some ⟨⟨out.1,tape,r.work+out.2+5⟩,work+4⟩
    | .replicated _ counts replica _ =>
        (PhysicalBinaryVertexRounding.uniform T replica.input tape).map (fun out =>
          ⟨PhysicalVertexRounding.project (r.prepared.pullbackSampleWithCost counts replica) (r.work+5) out.cut,
            work+4+out.arithmetic⟩))
  unfold weightedWith
  cases r.reduced with
  | zero mask work => rfl
  | replicated qs counts replica work =>
      simp only [project_value,uniform_value,Nat.add_zero]

set_option maxHeartbeats 1200000 in
theorem weighted_paid (p : Polynomial ℕ) (bounds : ∀ n L T, GuardedCutoffWork.budget n L T ≤ p.eval (n+T))
    {n b : ℕ} (T : ℕ) (D : Input n) (fits : InputFits D b) (tape : Bits) :
    (weighted T D tape).2 ≤ PhysicalVertexRoundingCost.weightedBudget p n T+PhysicalBinaryVertexRounding.weightedBudget n b := by
  let prep := BinaryPortPreparation.prepareAndReduce D
  let original := prepareAndReduce D
  let pre := build D
  let clone := materialize pre.data pre.data.counts
  have observed : prep.1=original := BinaryPortPreparation.prepareAndReduce_value D
  have arithmetic : prep.2 ≤ _ := BinaryPortPreparation.prepareAndReduce_paid D fits
  have entrance : original.work ≤ _ := prepareAndReduce_work D
  change (weightedWith T prep.1 prep.2 tape).2 ≤ _
  rw [observed]
  unfold weightedWith
  rw [show original.reduced=pre.data.reduce from rfl]
  by_cases zero : pre.data.totals.objective.num=0
  · rw [Input.reduce_zero _ zero]
    have unpack := pullback_work_bound D pre.data.zeroMask
    change (pre.pullbackMaskWithCost pre.data.zeroMask).2 ≤ 60*n^2+62*n+10 at unpack
    change original.work+(pre.pullbackMaskWithCost pre.data.zeroMask).2+5+prep.2+4 ≤ _
    unfold PhysicalVertexRoundingCost.weightedBudget PhysicalBinaryVertexRounding.weightedBudget
    omega
  · rw [Input.reduce_positive _ zero]
    have pos : 0<n := by
      by_contra empty
      obtain rfl : n=0 := by omega
      exact zero (empty_objective_zero D)
    let decode := pre.pullbackSampleWithCost pre.data.counts clone
    have dimension := build_clone_count D pos zero
    have inner := (uniform_paid p bounds T clone.input (VertexReductionWidths.replica_fields D fits) tape).trans
      (Nat.add_le_add (PhysicalVertexRoundingCost.uniformBudget_mono p dimension T)
        (PhysicalBinaryVertexRounding.uniformBudget_mono dimension (Nat.le_refl _)))
    have unpack (mask : Flags (cloneList pre.data.counts).length) :
        (decode mask).2 ≤ 108*n^3+116*n^2+122*n+24 := pullbackSample_work_bound D pos zero mask
    change (project decode (original.work+5) (prep.2+4) 0 (uniform T clone.input tape)).2 ≤ _
    refine (project_paid _ _ _ _ _ (Nat.le_refl _) inner unpack).trans ?_
    unfold PhysicalVertexRoundingCost.weightedBudget PhysicalBinaryVertexRounding.weightedBudget
    omega

end Weighted

section Size

open EncodedHeavyVertexPreparation EncodedCubeRootThreshold

def size {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) : Read (Result n) :=
  let p := BinaryHeavyPreparation.prepare D
  project (combinedMaskWithCost p.1.1) (p.1.2+5) (p.2+4) 0 (weighted T p.1.1.data tape)

attribute [local irreducible] BinaryHeavyPreparation.prepare PhysicalBinaryVertexRounding.weighted in
set_option maxHeartbeats 1000000 in
theorem size_value {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) :
    (size T D tape).1=PhysicalBinaryVertexRounding.size T D tape := by
  let prep := BinaryHeavyPreparation.prepare D
  change (project (combinedMaskWithCost prep.1.1) (prep.1.2+5) (prep.2+4) 0
    (weighted T prep.1.1.data tape)).1= _
  rw [project_value,weighted_value,PhysicalBinaryVertexRounding.size]
  simp only [Nat.add_zero]
  rfl

set_option maxHeartbeats 1000000 in
theorem size_paid (p : Polynomial ℕ) (bounds : ∀ n L T, GuardedCutoffWork.budget n L T ≤ p.eval (n+T))
    {n b : ℕ} (T : ℕ) (D : Input n) (fits : InputFits D b) (tape : Bits) :
    (size T D tape).2 ≤ PhysicalVertexRoundingCost.sizeBudget p n T+PhysicalBinaryVertexRounding.sizeBudget n b := by
  let prep := BinaryHeavyPreparation.prepare D
  have same : prep.1=prepare D := BinaryHeavyPreparation.prepare_value D
  have fields : InputFits prep.1.1.data (b+1) := same.symm ▸ VertexReductionWidths.heavy_fields D fits
  have small : prep.1.1.size ≤ n := same.symm ▸ build_size_le D (threshold n)
  have arithmetic : prep.2 ≤ _ := BinaryHeavyPreparation.prepare_paid D fits
  have entrance : prep.1.2 ≤ _ := same.symm ▸ prepare_work D
  have unpack : ∀ mask : Flags prep.1.1.size, (combinedMaskWithCost prep.1.1 mask).2 ≤ 20*n^2+66*n+36 := by
    rw [same]
    exact build_combinedMask_work D (threshold n)
  have inner := (weighted_paid p bounds T _ fields tape).trans
    (Nat.add_le_add (PhysicalVertexRoundingCost.weightedBudget_mono p small T)
      (PhysicalBinaryVertexRounding.weightedBudget_mono small (Nat.le_refl _)))
  change (project (combinedMaskWithCost prep.1.1) (prep.1.2+5) (prep.2+4) 0 (weighted T prep.1.1.data tape)).2 ≤ _
  refine (project_paid _ _ _ _ _ (Nat.le_refl _) inner unpack).trans ?_
  unfold PhysicalVertexRoundingCost.sizeBudget PhysicalBinaryVertexRounding.sizeBudget
  omega

end Size

open PhysicalBinaryVertexRounding.Result (charge)

def runner {n : ℕ} (mode : ChargedVertexModes.Mode) (T : ℕ) (D : Input n) (tape : Bits) :
    Read (PhysicalIntegerRounding.Result n) :=
  let r := match mode with
    | .mass => weighted T D tape
    | .size => size T D tape
  (r.1.map charge,r.2)

theorem runner_value {n : ℕ} (mode : ChargedVertexModes.Mode) (T : ℕ) (D : Input n) (tape : Bits) :
    (runner mode T D tape).1=PhysicalAmplifiedBinaryVertex.runner mode T D tape := by
  cases mode <;> simp only [runner,PhysicalAmplifiedBinaryVertex.runner,weighted_value,size_value]

end DirectedFlowCutGap.PaidVertexRounding
