import DirectedFlowCutGap.BinaryPortPreparation
import DirectedFlowCutGap.BinaryHeavyPreparation
import DirectedFlowCutGap.PhysicalVertexRoundingCost
import DirectedFlowCutGap.BinaryIntegerCutoff

/-! Join the binary numerical preparation to the packed integer controller
and reuse the physical cuts and pullbacks. The added counter records actual
binary scalar operations, alongside the earlier graph and execution counter. -/

namespace DirectedFlowCutGap.PhysicalBinaryVertexRounding

open BinaryArithmetic RetainedGridState RawNonnegativeRational
open EncodedUnitCostReplication
open VertexReductionWidths (InputFits)

structure Result (n : ℕ) where
  cut : PhysicalIntegerRounding.Result n
  arithmetic : ℕ

def Result.charge {n : ℕ} (r : Result n) : PhysicalIntegerRounding.Result n :=
  { r.cut with paid := r.cut.paid+r.arithmetic }

private def project {n m : ℕ} (decode : Flags m → Flags n × ℕ)
    (work binary : ℕ) (r : Result m) : Result n :=
  ⟨PhysicalVertexRounding.project decode work r.cut,binary+r.arithmetic⟩

private theorem project_cut {n m : ℕ} (decode : Flags m → Flags n × ℕ) (work binary : ℕ)
    (r : Option (Result m)) :
    (r.map (project decode work binary)).map Result.cut=(r.map Result.cut).map (PhysicalVertexRounding.project decode work) := by
  simp only [Option.map_map,Function.comp_def,project]

section Uniform

open EncodedUniformChain EncodedUniformOutput EncodedUniformWeightParameters

def uniform {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) : Option (Result n) :=
  let ready := BinaryUniformArithmetic.compute D
  let p := ready.1
  let test := BinaryRawRational.le Code.one p.total
  if test.1 then
    let level := BinaryUniformArithmetic.cutoff p.average
    let chain := materializeWith p.ports p.average p.counts level.1
    (BinaryIntegerCutoff.run T chain.data.adjacency chain.cutoff tape).map (fun r =>
      ⟨PhysicalVertexRounding.project (originalMaskWithCost chain) (p.work+chain.work+10) r.1,
        ready.2+test.2+level.2+r.2+6⟩)
  else some ⟨⟨Vector.replicate n false,tape,p.work+4*n+10⟩,ready.2+test.2+6⟩

theorem uniform_cut {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) :
    (uniform T D tape).map Result.cut=PhysicalVertexRounding.uniform T D tape := by
  let readout (p : Parameters n) (test : Bool) (k : ℕ) : Option (PhysicalIntegerRounding.Result n) :=
    if test then
      let chain := materializeWith p.ports p.average p.counts k
      (PhysicalIntegerRounding.run T chain.data.adjacency chain.cutoff tape).map
        (PhysicalVertexRounding.project (originalMaskWithCost chain) (p.work+chain.work+10))
    else some ⟨Vector.replicate n false,tape,p.work+4*n+10⟩
  let p := (BinaryUniformArithmetic.compute D).1
  have h : (uniform T D tape).map Result.cut =
      readout p (BinaryRawRational.le Code.one p.total).1 (BinaryUniformArithmetic.cutoff p.average).1 := by
    unfold uniform readout
    dsimp only
    split_ifs
    · rw [← BinaryIntegerCutoff.run_cut T _ _ tape]
      simp only [Option.map_map,Function.comp_def]
      rfl
    · rfl
  rw [h,BinaryRawRational.le_value,BinaryUniformArithmetic.cutoff_value,
    show p=compute D from BinaryUniformArithmetic.compute_value D]
  rfl

def uniformBudget {R : Type*} [Semiring R] (n b : R) : R :=
  BinaryUniformArithmetic.budget n b+3*BinaryRawRational.budget (VertexReductionWidths.uniformWidth n b)+
    BinaryIntegerCutoff.budget (6*n) (6*n)+10

theorem uniformBudget_mono {n m a b : ℕ} (h : n ≤ m) (width : a ≤ b) : uniformBudget n a ≤ uniformBudget m b := by
  unfold uniformBudget BinaryUniformArithmetic.budget BinaryRawRational.budget
    BinaryVertexReductionArithmetic.aggregateWidth VertexReductionWidths.uniformWidth
  have dimensions := Nat.mul_le_mul_left 6 h
  dsimp only
  gcongr
  exact BinaryIntegerCutoff.budget_mono dimensions dimensions

theorem uniform_paid {n b : ℕ} (T : ℕ) (D : Input n) (fits : InputFits D b) (tape : Bits) {r : Result n}
    (observed : uniform T D tape=some r) : r.arithmetic ≤ uniformBudget n b := by
  let ready := BinaryUniformArithmetic.compute D
  let p := ready.1
  let test := BinaryRawRational.le Code.one p.total
  let level := BinaryUniformArithmetic.cutoff p.average
  let chain := materializeWith p.ports p.average p.counts level.1
  have measured := BinaryUniformArithmetic.compute_paid D fits
  obtain ⟨total,avg,_⟩ := VertexReductionWidths.uniform_fields D fits
  have eq : p=compute D := BinaryUniformArithmetic.compute_value D
  have ht : p.total.Bounded (VertexReductionWidths.uniformWidth n b) := eq.symm ▸ total
  have ha : p.average.Bounded (VertexReductionWidths.uniformWidth n b) := eq.symm ▸ avg
  have cmp := BinaryRawRational.le_paid (Code.bounded_mono Code.bounded_one (Nat.zero_le _)) ht
  have k := BinaryUniformArithmetic.cutoff_paid ha
  change ready.2 ≤ _ at measured
  change test.2 ≤ _ at cmp
  change level.2 ≤ _ at k
  change (if test.1 then ((BinaryIntegerCutoff.run T chain.data.adjacency chain.cutoff tape).map fun out =>
      ⟨PhysicalVertexRounding.project (originalMaskWithCost chain) (p.work+chain.work+10) out.1,
        ready.2+test.2+level.2+out.2+6⟩)
    else some ⟨⟨Vector.replicate n false,tape,p.work+4*n+10⟩,ready.2+test.2+6⟩)=some r at observed
  by_cases h : test.1=true
  · rw [ite_eq_left h] at observed
    cases call : BinaryIntegerCutoff.run T chain.data.adjacency chain.cutoff tape with
    | none => simp [call] at observed
    | some out =>
      simp only [call,Option.map_some,Option.some.injEq] at observed
      have positive : nontrivial D = true := by
        change (BinaryRawRational.le Code.one p.total).1=true at h
        rw [BinaryRawRational.le_value,eq] at h
        exact h
      have mass : 0 < (compute D).total.realValue := by
        rw [compute_total]
        exact lt_of_lt_of_le (by norm_num) ((nontrivial_iff D).mp positive)
      let dimensions (parameters : Parameters n) (k : ℕ) : Prop :=
        let c := materializeWith parameters.ports parameters.average parameters.counts k
        c.cutoff ≤ c.size ∧ c.size ≤ 6*n
      have hd : dimensions p level.1 := by
        change dimensions p (BinaryUniformArithmetic.cutoff p.average).1
        rw [BinaryUniformArithmetic.cutoff_value,eq]
        exact ⟨(expand_cutoff_bounds D positive).2,expand_size_bound D mass⟩
      change chain.cutoff ≤ chain.size ∧ chain.size ≤ 6*n at hd
      have bound := (BinaryNaturalOperations.size_le_self chain.cutoff).trans (hd.1.trans hd.2)
      have gate := (BinaryIntegerCutoff.run_paid T chain.data.adjacency bound tape call).trans
        (BinaryIntegerCutoff.budget_mono hd.2 le_rfl)
      rw [← observed]
      unfold uniformBudget
      dsimp only
      omega
  · rw [ite_eq_right h] at observed
    rw [← Option.some.inj observed]
    unfold uniformBudget
    dsimp only
    omega

end Uniform

section Weighted

open EncodedUnitCostPreparation

private def weightedWith {n : ℕ} (T : ℕ) (r : Reduction n) (paid : ℕ) (tape : Bits) : Option (Result n) :=
  match r.reduced with
  | .zero mask _ =>
    let out := r.prepared.pullbackMaskWithCost mask
    some ⟨⟨out.1,tape,r.work+out.2+5⟩,paid+4⟩
  | .replicated _ counts replica _ =>
    (uniform T replica.input tape).map
      (project (r.prepared.pullbackSampleWithCost counts replica) (r.work+5) (paid+4))

def weighted {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) : Option (Result n) :=
  let prep := BinaryPortPreparation.prepareAndReduce D
  weightedWith T prep.1 prep.2 tape

theorem weighted_cut {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) :
    (weighted T D tape).map Result.cut=PhysicalVertexRounding.weighted T D tape := by
  unfold weighted PhysicalVertexRounding.weighted
  simp only [BinaryPortPreparation.prepareAndReduce_value]
  unfold weightedWith
  cases h : (prepareAndReduce D).reduced with
  | zero mask work => rfl
  | replicated qs count replica work =>
    change ((uniform T replica.input tape).map _).map Result.cut = _
    rw [project_cut,uniform_cut]

def weightedBudget {R : Type*} [Semiring R] (n b : R) : R :=
  BinaryPortPreparation.portBudget n b+BinaryVertexReductionArithmetic.reductionBudget (3*n) (b+1)+8+
    uniformBudget (4*n^2) (b+1)

theorem weightedBudget_mono {n m a b : ℕ} (h : n ≤ m) (width : a ≤ b) : weightedBudget n a ≤ weightedBudget m b := by
  have hu := uniformBudget_mono (show 4*n^2 ≤ 4*m^2 by gcongr) (Nat.add_le_add_right width 1)
  unfold weightedBudget BinaryPortPreparation.portBudget BinaryVertexReductionArithmetic.reductionBudget
    BinaryVertexReductionArithmetic.aggregateWidth BinaryVertexReductionArithmetic.normalizedWidth BinaryRawRational.budget
  dsimp only
  gcongr

theorem weighted_paid {n b : ℕ} (T : ℕ) (D : Input n) (fits : InputFits D b) (tape : Bits) {r : Result n}
    (observed : weighted T D tape=some r) : r.arithmetic ≤ weightedBudget n b := by
  let p := build D
  let prep := BinaryPortPreparation.prepareAndReduce D
  let clone := materialize p.data p.data.counts
  have setup := BinaryPortPreparation.prepareAndReduce_paid D fits
  change weightedWith T prep.1 prep.2 tape=some r at observed
  rw [show prep.1=prepareAndReduce D from BinaryPortPreparation.prepareAndReduce_value D] at observed
  unfold weightedWith at observed
  have hreduce : (prepareAndReduce D).reduced=p.data.reduce := rfl
  rw [hreduce] at observed
  by_cases zero : p.data.totals.objective.num=0
  · rw [Input.reduce_zero _ zero] at observed
    rw [← Option.some.inj observed]
    change prep.2+4 ≤ _
    unfold weightedBudget
    change prep.2 ≤ _ at setup
    omega
  · rw [Input.reduce_positive _ zero] at observed
    change ((uniform T clone.input tape).map (project (p.pullbackSampleWithCost p.data.counts clone)
      ((prepareAndReduce D).work+5) (prep.2+4)))=some r at observed
    cases call : uniform T clone.input tape with
    | none => simp [call] at observed
    | some out =>
      simp only [call,Option.map_some,Option.some.injEq] at observed
      have pos : 0<n := by
        by_contra empty
        obtain rfl : n=0 := by omega
        exact zero (empty_objective_zero D)
      have dimension := build_clone_count D pos zero
      have bits := (uniform_paid T clone.input (VertexReductionWidths.replica_fields D fits) tape call).trans
        (uniformBudget_mono dimension le_rfl)
      rw [← observed]
      change prep.2+4+out.arithmetic ≤ _
      change prep.2 ≤ _ at setup
      unfold weightedBudget
      omega

end Weighted

section Size

open EncodedHeavyVertexPreparation EncodedCubeRootThreshold

def size {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) : Option (Result n) :=
  let p := BinaryHeavyPreparation.prepare D
  (weighted T p.1.1.data tape).map (project (combinedMaskWithCost p.1.1) (p.1.2+5) (p.2+4))

theorem size_cut {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) :
    (size T D tape).map Result.cut=PhysicalVertexRounding.size T D tape := by
  unfold size PhysicalVertexRounding.size
  rw [project_cut,weighted_cut]
  exact congrArg (fun p : Residual n × ℕ =>
    (PhysicalVertexRounding.weighted T p.1.data tape).map
      (PhysicalVertexRounding.project (combinedMaskWithCost p.1) (p.2+5)))
    (BinaryHeavyPreparation.prepare_value D)

def sizeBudget {R : Type*} [Semiring R] (n b : R) : R :=
  BinaryHeavyPreparation.budget n b+4+weightedBudget n (b+1)

theorem sizeBudget_mono {n m a b : ℕ} (h : n ≤ m) (width : a ≤ b) : sizeBudget n a ≤ sizeBudget m b := by
  have hw := weightedBudget_mono h (Nat.add_le_add_right width 1)
  unfold sizeBudget BinaryHeavyPreparation.budget BinaryCubeThreshold.budget BinaryCubeThreshold.testBudget BinaryRawRational.budget
  gcongr

theorem size_paid {n b : ℕ} (T : ℕ) (D : Input n) (fits : InputFits D b) (tape : Bits) {r : Result n}
    (observed : size T D tape=some r) : r.arithmetic ≤ sizeBudget n b := by
  let p := BinaryHeavyPreparation.prepare D
  have setup := BinaryHeavyPreparation.prepare_paid D fits
  have eq : p.1=prepare D := BinaryHeavyPreparation.prepare_value D
  have fields : InputFits p.1.1.data (b+1) := eq.symm ▸ VertexReductionWidths.heavy_fields D fits
  have dim : p.1.1.size ≤ n := eq.symm ▸ build_size_le D (threshold n)
  change ((weighted T p.1.1.data tape).map (project (combinedMaskWithCost p.1.1) (p.1.2+5) (p.2+4)))=some r at observed
  cases call : weighted T p.1.1.data tape with
  | none => simp [call] at observed
  | some out =>
    simp only [call,Option.map_some,Option.some.injEq] at observed
    have paid := (weighted_paid T _ fields tape call).trans (weightedBudget_mono dim le_rfl)
    rw [← observed]
    change p.2+4+out.arithmetic ≤ sizeBudget n b
    change p.2 ≤ _ at setup
    unfold sizeBudget
    omega

end Size

end DirectedFlowCutGap.PhysicalBinaryVertexRounding
