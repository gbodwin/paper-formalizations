import DirectedFlowCutGap.EncodedWeightedOutput
import DirectedFlowCutGap.EncodedRoundingRepetition

/-!
# One retained weighted vertex query through the actual integer rounding entry

The caller supplies retained raw-rational arrays for ORIGINAL weights and the
EXACT current penalized cost row. `queryInput` only wraps those three references.
It does not normalize or fill the original weights, and it does not decode a
binary row for free. The binary input/reduction realization remains a separate
named obligation; this module composes the existing declared word programs.

Preparation, aggregate scans, normalized counts, replica, stored dimension,
uniform parameters and chain are each bound once. The uniform test reads the
retained total. The chain is materialized from the retained parameters rather
than by calling `expand` and repeating their construction. The core is the
actual `EncodedRoundingRepetition.run`, with its exact first-on-ties selector.
Every returned core record and the charged original-mask pullback are retained.

Only a typed, explicitly charged tape callback is external. Its actual fair-bit
body, failure/trial/consumption metadata accumulation, probability coupling and
fixed structural cost certificate must still be supplied. The `sampling` field
below is the existing sampler-operation subtotal, not a random-bit counter.
No callback is assigned constant cost and no operand-width bound is asserted to
be a runtime theorem. There is no native compiler or allocator claim.
-/
namespace DirectedFlowCutGap.EncodedWeightedVertexQuery

set_option backward.isDefEq.respectTransparency false
open scoped NNReal
open RawNonnegativeRational EncodedUnitCostReplication
open RetainedGridState IntegralNetworkFlow.Tabulated

/-- Three retained references, with no fresh weight/cost map. -/
def queryInput {n : ℕ} (adjacency : PairFlags n)
    (originalWeights penalizedCosts : Vector Code n) : Input n :=
  ⟨adjacency,originalWeights,penalizedCosts⟩

@[simp] theorem queryInput_weights {n : ℕ} (a : PairFlags n)
    (w c : Vector Code n) : (queryInput a w c).weights = w := rfl

@[simp] theorem queryInput_costs {n : ℕ} (a : PairFlags n)
    (w c : Vector Code n) : (queryInput a w c).costs = c := rfl

/-- Positivity is required before forming a finite-grid callback domain. -/
abbrev TapeSampler (M : Type → Type) :=
  (N L : ℕ) → (hL : 0 < L) → (a : PairFlags N) → M (RetainedTapeInput.Tape L a × ℕ)

/-- The complete selected/sample records are retained, with their actual size. -/
structure CoreRecord where
  size : ℕ
  cutoff : ℕ
  result : EncodedRoundingRepetition.Result size

structure Output (n : ℕ) where
  mask : Vector Bool n
  operations : ℕ
  sampling : ℕ
  core : Option CoreRecord

/-- Erased validity and zero cost are proved at the actual deterministic branch. -/
structure Finished {n : ℕ} (D : Input n) where
  mask : Vector Bool n
  operations : ℕ
  valid : IsIntegralCut D.graph (selectedSet mask) (thresholdDemands D.graph D.weight)
  zero_cost : cutCost D.cost (selectedSet mask) = 0

def Finished.output {n : ℕ} {D : Input n} (r : Finished D) : Output n :=
  ⟨r.mask,r.operations,0,none⟩

/-- Equalities are erased. Runtime consumers use these actual retained records,
never evaluate the canonical expressions again to obtain a dimension or label. -/
structure Ready {n : ℕ} (D : Input n) where
  prepared : EncodedUnitCostPreparation.Prepared n
  prepared_eq : prepared = EncodedUnitCostPreparation.build D
  counts : Vector ℕ prepared.size
  counts_eq : counts = prepared.data.counts
  replica : Replica counts
  replica_eq : replica = materialize prepared.data counts
  sized : EncodedInputSizing.SizedInput (cloneList counts).length
  sized_eq : sized = EncodedInputSizing.retainReplica replica
  parameters : EncodedUniformWeightParameters.Parameters sized.size
  parameters_eq : parameters = EncodedUniformWeightParameters.compute sized.data
  chain : EncodedUniformChain.Chain parameters.counts
  chain_eq : chain = EncodedUniformChain.materialize parameters.ports parameters.average parameters.counts
  positive : prepared.data.totals.objective.num ≠ 0
  nontrivial : EncodedUniformWeightParameters.nontrivial sized.data = true
  operations : ℕ
  operations_eq : operations = prepared.work + prepared.data.totals.work + replica.work +
    60*prepared.size + 40 + sized.work + parameters.work + chain.work + 32

def Ready.pullback {n : ℕ} {D : Input n} (r : Ready D)
    (mask : Vector Bool r.chain.size) : Vector Bool n × ℕ :=
  EncodedWeightedOutput.pullbackWithCost r.prepared r.counts r.replica r.sized r.chain mask

@[simp] theorem selectedSet_false (n : ℕ) :
    selectedSet (Vector.replicate n false) = ∅ := by
  ext i
  simp [selectedSet]

@[simp] theorem restore_false {m : ℕ} (S : EncodedInputSizing.SizedInput m) :
    selectedSet (S.restoreMask (Vector.replicate S.size false)) = ∅ := by
  rcases S with ⟨N,hN,data,work⟩
  subst N
  ext i
  simp [EncodedInputSizing.SizedInput.restoreMask,selectedSet]

/-- The empty replica mask uses the same retained size cast and full-fiber
pullback as every sampled mask. Its original cost is zero. -/
theorem small_output {n : ℕ} (D : Input n)
    (hC : (EncodedUnitCostPreparation.build D).data.totals.objective.num ≠ 0)
    (hU : EncodedUniformWeightParameters.nontrivial
      (EncodedWeightedEnvelope.retained D).data ≠ true) :
    let P := EncodedWeightedEnvelope.prepared D
    let R := EncodedWeightedEnvelope.replicated D
    let S := EncodedWeightedEnvelope.retained D
    let mask := S.restoreMask (Vector.replicate S.size false)
    IsIntegralCut D.graph (selectedSet (P.pullbackSample P.data.counts R mask))
      (thresholdDemands D.graph D.weight) ∧
    cutCost D.cost (selectedSet (P.pullbackSample P.data.counts R mask)) = 0 := by
  dsimp only
  have hu := EncodedUniformWeightParameters.trivial_cut
    (EncodedWeightedEnvelope.retained D).data hU
  have hr : IsIntegralCut (EncodedWeightedEnvelope.replicated D).input.graph
      (selectedSet ((EncodedWeightedEnvelope.retained D).restoreMask
        (Vector.replicate (EncodedWeightedEnvelope.retained D).size false)))
      (thresholdDemands (EncodedWeightedEnvelope.replicated D).input.graph
        (EncodedWeightedEnvelope.replicated D).input.weight) := by
    apply EncodedInputSizing.retain_cut (EncodedWeightedEnvelope.replicated D).input
    change IsIntegralCut (EncodedWeightedEnvelope.retained D).data.graph
      (selectedSet (Vector.replicate (EncodedWeightedEnvelope.retained D).size false))
      (thresholdDemands (EncodedWeightedEnvelope.retained D).data.graph
        (EncodedWeightedEnvelope.retained D).data.weight)
    simpa only [selectedSet_false] using hu
  have hc := EncodedUnitCostPreparation.sampled_original_output_spec D hC 0
    ((EncodedWeightedEnvelope.retained D).restoreMask
      (Vector.replicate (EncodedWeightedEnvelope.retained D).size false)) hr
    (by simp only [restore_false,Finset.card_empty,Nat.cast_zero,zero_mul,le_refl])
  refine ⟨hc.1,le_antisymm ?_ zero_le⟩
  simpa only [mul_zero,zero_mul] using hc.2

/-- All branches are concrete. The allowances include zero-mask construction,
normalization/count loops, retained-size wrappers, branch and output records.
The existing component counters price every graph and output scan separately. -/
def prepare {n : ℕ} (D : Input n) : Finished D ⊕ Ready D :=
  let P := EncodedUnitCostPreparation.build D
  let totals := P.data.totals
  if hC : totals.objective.num = 0 then
    let selected := P.data.zeroMask
    let out := P.pullbackMaskWithCost selected
    .inl
      { mask := out.1
        operations := P.work+totals.work+40*P.size+20+out.2+12
        valid := (EncodedUnitCostPreparation.zero_output_spec D hC).1
        zero_cost := (EncodedUnitCostPreparation.zero_output_spec D hC).2 }
  else
    let normalized := P.data.normalized totals
    let counts := Input.copyCounts normalized
    let R := materialize P.data counts
    let S := EncodedInputSizing.retainReplica R
    let parameters := EncodedUniformWeightParameters.compute (n := S.size) S.data
    let setupWork := P.work+totals.work+R.work+60*P.size+40+S.work+parameters.work+32
    if hU : Code.one.le parameters.total = true then
      let U := EncodedUniformChain.materialize parameters.ports parameters.average parameters.counts
      .inr
        { prepared := P, prepared_eq := rfl
          counts := counts, counts_eq := rfl
          replica := R, replica_eq := rfl
          sized := S, sized_eq := rfl
          parameters := parameters, parameters_eq := rfl
          chain := U, chain_eq := rfl
          positive := hC, nontrivial := hU
          operations := setupWork+U.work
          operations_eq := by dsimp only [setupWork]; omega }
    else
      let empty := Vector.replicate S.size false
      let restored := S.restoreMaskWithCost empty
      let out := P.pullbackSampleWithCost counts R restored.1
      .inl
        { mask := out.1
          operations := setupWork+2*S.size+8+restored.2+out.2+12
          valid := (small_output D hC hU).1
          zero_cost := (small_output D hC hU).2 }

/-- The cutoff proof refers to the retained chain actually consumed below. -/
theorem Ready.cutoff_positive {n : ℕ} {D : Input n} (r : Ready D) : 0 < r.chain.cutoff := by
  rcases r with ⟨P,hP,k,hk,R,hR,S,hS,p,hp,U,hU,hC,hT,q,hq⟩
  subst P; subst k; subst R; subst S; subst p; subst U
  exact (EncodedUniformChain.expand_cutoff_bounds _ hT).1

/-- Original n and ORIGINAL W remain the bounds even though every clone count
and the complete current query cost row may change between calls. -/
theorem Ready.envelope {n : ℕ} {D : Input n} (r : Ready D) (hn : 0<n) :
    r.chain.size ≤ 24*n^2 ∧ r.chain.cutoff ≤ r.chain.size ∧
      (r.chain.size : ℝ≥0)/r.chain.cutoff ≤ 6*totalWeight D.weight := by
  rcases r with ⟨P,hP,k,hk,R,hR,S,hS,p,hp,U,hU,hC,hT,q,hq⟩
  subst P; subst k; subst R; subst S; subst p; subst U
  exact ⟨EncodedWeightedEnvelope.expanded_size D hn hC hT,
    (EncodedUniformChain.expand_cutoff_bounds _ hT).2,
    EncodedWeightedEnvelope.expanded_integer_mass D hC hT⟩

/-- Sum of the actual preparation/replication/uniform construction counters.
The original size controls every materialized table. This is a word-operation
bound; binary rational substitution and representation movement remain open. -/
def readyWordBound (n : ℕ) : ℕ :=
  9*n^2*(CountedSearch.searchBound (3*n) 24+224)+
    46720*n^4+3872*n^2+889*n+304

theorem Ready.operations_bound {n : ℕ} {D : Input n} (r : Ready D) (hn : 0<n) :
    r.operations ≤ readyWordBound n := by
  rcases r with ⟨P,hP,k,hk,R,hR,S,hS,p,hp,U,hU,hC,hT,q,hq⟩
  subst P; subst k; subst R; subst S; subst p; subst U
  have hp := EncodedUnitCostPreparation.build_work_bound D
  have hm := materialize_work_bound (EncodedUnitCostPreparation.build D).data n
    (EncodedUnitCostPreparation.build_preparedBounds D hn) hC
  have hP := EncodedUnitCostPreparation.build_size_le D
  have hS := EncodedWeightedEnvelope.retained_size D hn hC
  have hS2 := Nat.pow_le_pow_left hS 2
  have hU := EncodedUniformChain.computed_work_bound
    (EncodedWeightedEnvelope.retained D).data
    (EncodedWeightedEnvelope.uniform_positive (EncodedWeightedEnvelope.retained D).data hT)
  have hw : (EncodedWeightedEnvelope.retained D).work = 12 := rfl
  change q ≤ readyWordBound n
  rw [hq]
  change (EncodedWeightedEnvelope.prepared D).work+
    (EncodedWeightedEnvelope.prepared D).data.totals.work+
    (EncodedWeightedEnvelope.replicated D).work+
    60*(EncodedWeightedEnvelope.prepared D).size+40+
    (EncodedWeightedEnvelope.retained D).work+
    (EncodedUniformWeightParameters.compute (EncodedWeightedEnvelope.retained D).data).work+
    (EncodedWeightedEnvelope.expanded D).work+32 ≤ _
  rw [Input.totals_work,hw,EncodedUniformWeightParameters.compute_work]
  unfold readyWordBound
  nlinarith

theorem Ready.pullback_valid {n : ℕ} {D : Input n} (r : Ready D)
    (mask : Vector Bool r.chain.size)
    (hcut : IsIntegralCut r.chain.data.graph (selectedSet mask)
      (CandidateSchedule.unweightedDemands r.chain.data.graph (r.chain.cutoff : ℝ≥0) :
        Set (Pair r.chain.size))) :
    IsIntegralCut D.graph (selectedSet (r.pullback mask).1)
      (thresholdDemands D.graph D.weight) := by
  rcases r with ⟨P,hP,k,hk,R,hR,S,hS,p,hp,U,hU,hC,hT,q,hq⟩
  subst P; subst k; subst R; subst S; subst p; subst U
  exact EncodedWeightedOutput.originalMask_correct D hT mask hcut

/-- The approximation premise is about the actual selected mask; no other
argmin, existential cut, or constant-time graph oracle is substituted. -/
theorem Ready.pullback_cost {n : ℕ} {D : Input n} (r : Ready D) (hn : 0<n)
    (alpha : ℕ → ℕ → ℝ≥0) (mask : Vector Bool r.chain.size)
    (hcut : IsIntegralCut r.chain.data.graph (selectedSet mask)
      (CandidateSchedule.unweightedDemands r.chain.data.graph (r.chain.cutoff : ℝ≥0) :
        Set (Pair r.chain.size)))
    (hsize : ((selectedSet mask).card : ℝ≥0) ≤
      alpha r.chain.size r.chain.cutoff*(r.chain.size : ℝ≥0)/r.chain.cutoff) :
    cutCost D.cost (selectedSet (r.pullback mask).1) ≤
      12*EncodedWeightedEnvelope.factor alpha n (6*totalWeight D.weight)*
        weightedCost D.cost D.weight := by
  rcases r with ⟨P,hP,k,hk,R,hR,S,hS,p,hp,U,hU,hC,hT,q,hq⟩
  subst P; subst k; subst R; subst S; subst p; subst U
  exact EncodedWeightedOutput.originalMask_envelope_cost_le D hn hC hT alpha mask hcut hsize

/-- This is the already proved pullback scan charge, now tied to the retained
records of this actual call. It is a word-model statement. -/
theorem Ready.pullback_work {n : ℕ} {D : Input n} (r : Ready D) (hn : 0<n)
    (mask : Vector Bool r.chain.size) :
    (r.pullback mask).2 ≤ 1920*n^4+108*n^3+1012*n^2+122*n+59 := by
  rcases r with ⟨P,hP,k,hk,R,hR,S,hS,p,hp,U,hU,hC,hT,q,hq⟩
  subst P; subst k; subst R; subst S; subst p; subst U
  exact EncodedWeightedOutput.pullback_work_bound D hn hC hT mask

/-- This construction retains the complete core result and pulls back its
literal selected flags exactly once. `sampling` is already inside operations. -/
def finish {n : ℕ} {D : Input n} (r : Ready D)
    (core : EncodedRoundingRepetition.Result r.chain.size) : Output n :=
  let pulled := r.pullback core.selected.flags
  { mask := pulled.1
    operations := r.operations+core.operations+pulled.2+16
    sampling := core.sampling
    core := some ⟨r.chain.size,r.chain.cutoff,core⟩ }

def runReady {M : Type → Type} [Monad M] {n : ℕ} {D : Input n}
    (sample : TapeSampler M) (r : Ready D) (extra : ℕ) : M (Output n) := do
  let core ← EncodedRoundingRepetition.run
    (sample r.chain.size r.chain.cutoff r.cutoff_positive)
    r.chain.data.adjacency r.cutoff_positive extra
  pure (finish r core)

/-- Raw-array entry. No fresh binary decoding is hidden in its arguments. -/
def run {M : Type → Type} [Monad M] {n : ℕ}
    (sample : TapeSampler M) (D : Input n) (extra : ℕ) : M (Output n) :=
  match prepare D with
  | .inl done => pure done.output
  | .inr ready => runReady sample ready extra

/-- The exact current penalized row and original fixed weights are wrapped
once; the additional four operations pay the retained input/output records. -/
def query {M : Type → Type} [Monad M] {n : ℕ}
    (sample : TapeSampler M) (adjacency : PairFlags n)
    (originalWeights penalizedCosts : Vector Code n) (extra : ℕ) : M (Output n) :=
  (fun o => {o with operations := o.operations+4}) <$>
    run sample (queryInput adjacency originalWeights penalizedCosts) extra

noncomputable section

/-- Every typed tape outcome yields an original valid cut, even if its legal
bounded-bit default is biased. This theorem does not claim cost quality. -/
theorem runReady_valid {n : ℕ} {D : Input n} (sample : TapeSampler PMF)
    (r : Ready D) (extra : ℕ) {out : Output n}
    (hout : out ∈ (runReady sample r extra).support) :
    IsIntegralCut D.graph (selectedSet out.mask) (thresholdDemands D.graph D.weight) := by
  let : NeZero r.chain.cutoff := ⟨r.cutoff_positive.ne'⟩
  unfold runReady at hout
  obtain ⟨core,hcore,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  have he := (PMF.mem_support_pure_iff _ _).mp hout
  subst out
  apply r.pullback_valid core.selected.flags
  exact EncodedRoundingRepetition.run_flags_valid_any
    (sample r.chain.size r.chain.cutoff r.cutoff_positive)
    r.chain.data.adjacency r.cutoff_positive extra hcore

theorem run_valid {n : ℕ} (sample : TapeSampler PMF) (D : Input n)
    (extra : ℕ) {out : Output n} (hout : out ∈ (run sample D extra).support) :
    IsIntegralCut D.graph (selectedSet out.mask) (thresholdDemands D.graph D.weight) := by
  unfold run at hout
  cases h : prepare D with
  | inl done =>
      rw [h] at hout
      have he := (PMF.mem_support_pure_iff _ _).mp hout
      subst out
      exact done.valid
  | inr ready =>
      rw [h] at hout
      exact runReady_valid sample ready extra hout

/-- The callback charge is paid on every actual call; no arbitrary expensive
sampler is treated as a primitive of unit cost. This remains the declared word
model until the named body/representation certificates are substituted. -/
theorem runReady_operations {n : ℕ} {D : Input n} (sample : TapeSampler PMF)
    (r : Ready D) (hn : 0<n) (extra K : ℕ)
    (hK : ∀ a t, t ∈ (sample r.chain.size r.chain.cutoff r.cutoff_positive a).support → t.2 ≤ K)
    {out : Output n} (hout : out ∈ (runReady sample r extra).support) :
    out.operations ≤ r.operations+
      (extra+1)*(EncodedAllRegimeRounding.operationBound r.chain.size K+4*r.chain.size+28)+10+
      (1920*n^4+108*n^3+1012*n^2+122*n+59)+16 := by
  let : NeZero r.chain.cutoff := ⟨r.cutoff_positive.ne'⟩
  unfold runReady at hout
  obtain ⟨core,hcore,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  have he := (PMF.mem_support_pure_iff _ _).mp hout
  subst out
  have hc := (EncodedRoundingRepetition.run_bound
    (sample r.chain.size r.chain.cutoff r.cutoff_positive) K hK
    r.chain.data.adjacency r.cutoff_positive extra hcore).1
  have hp := r.pullback_work hn core.selected.flags
  change r.operations+core.operations+(r.pullback core.selected.flags).2+16 ≤ _
  omega

/-- Direct composition of the reached program counters with preparation and
pullback. The only external charge premise is the explicitly named tape body;
no bit-work claim follows until its body and the raw reductions are realized. -/
theorem runReady_word_bound {n : ℕ} {D : Input n} (sample : TapeSampler PMF)
    (r : Ready D) (hn : 0<n) (extra K : ℕ)
    (hK : ∀ a t, t ∈ (sample r.chain.size r.chain.cutoff r.cutoff_positive a).support → t.2 ≤ K)
    {out : Output n} (hout : out ∈ (runReady sample r extra).support) :
    out.operations ≤ readyWordBound n+
      (extra+1)*(EncodedAllRegimeRounding.operationBound r.chain.size K+4*r.chain.size+28)+10+
      (1920*n^4+108*n^3+1012*n^2+122*n+59)+16 := by
  have h := runReady_operations sample r hn extra K hK hout
  have hp := r.operations_bound hn
  omega

/-- Same-query semantic boundary, stated on ORIGINAL weights and the actual
penalized cost row. This is also the target relation of the pending binary
raw-array materializer, whose cost is not provided by this theorem. -/
theorem query_valid {n : ℕ} (sample : TapeSampler PMF) (adjacency : PairFlags n)
    (originalWeights penalizedCosts : Vector Code n) (extra : ℕ) {out : Output n}
    (hout : out ∈ (query sample adjacency originalWeights penalizedCosts extra).support) :
    IsIntegralCut (queryInput adjacency originalWeights penalizedCosts).graph
      (selectedSet out.mask)
      (thresholdDemands (queryInput adjacency originalWeights penalizedCosts).graph
        (queryInput adjacency originalWeights penalizedCosts).weight) := by
  obtain ⟨r,hr,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  exact run_valid sample _ extra (out := r) hr

/-- The cost-independent mass envelope uses original n and original weight
mass for every current cost row, never the auxiliary positive capacities. -/
theorem query_envelope {n : ℕ} (adjacency : PairFlags n)
    (originalWeights penalizedCosts : Vector Code n)
    (r : Ready (queryInput adjacency originalWeights penalizedCosts)) (hn : 0<n) :
    r.chain.size ≤ 24*n^2 ∧ r.chain.cutoff ≤ r.chain.size ∧
      (r.chain.size : ℝ≥0)/r.chain.cutoff ≤
        6*totalWeight (fun v : Fin n => originalWeights[v.val].realValue) :=
  r.envelope hn

end
end DirectedFlowCutGap.EncodedWeightedVertexQuery
