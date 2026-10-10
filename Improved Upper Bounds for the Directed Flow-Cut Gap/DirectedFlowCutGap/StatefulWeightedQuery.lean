import DirectedFlowCutGap.StatefulOutputShape
import DirectedFlowCutGap.EncodedWeightedVertexQuery

/-!
# Actual bounded-bit weighted query

The actual repeated selected flag array is pulled back through the retained
weighted reduction. All entering physical ledgers are permitted. The finite
cost envelope depends only on original size and weight mass, although the
materialized chain and current cost row may change. The same actual output
also retains the declared operation and sampling charge.

Raw-rational input arrays are still supplied, and their binary materializer,
fuel construction charge, physical reference/storage simulation and adaptive
packing-provider join are separate obligations.
-/
namespace DirectedFlowCutGap.StatefulWeightedQuery
noncomputable section
open scoped NNReal
open EncodedWeightedVertexQuery EncodedUnitCostReplication
open BinaryArithmetic BinarySamplerMetadata BinaryWeightedSamplingLaw
open BinaryRetainedTapeCost BinaryRetainedRoundingCost BinaryRetainedEntryCost
open RetainedGridState EncodedIntegerShortestPaths FiniteAmplification
set_option backward.isDefEq.respectTransparency false

/-- The callback body is concrete bounded rejection, with a logarithmic fuel
word determined by the actual transformed dimension. -/
def sample : TapeSampler (StateT Ledger PMF) := fun N L hL =>
  BinaryRetainedTape.callback fairBit (StatefulBoundedRoundingQuality.canonicalFuel N)
    L.bits (value_bits L) hL

def threshold (C ε : ℝ) (N L : ℕ) : ℕ :=
  Nat.ceil (2*max 1 (C*(N : ℝ)^ε*AdaptiveCost.sizeFactor (Fin N) (L : ℝ≥0)))

/-- This finite formula converts the actual cardinal threshold to the input
normalization used by the checked weighted pullback. -/
def alpha (C ε : ℝ) (N L : ℕ) : ℝ≥0 :=
  (threshold C ε N L : ℝ≥0)*L/N

def costBound {n : ℕ} (D : Input n) (C ε : ℝ) : ℝ≥0 :=
  12*EncodedWeightedEnvelope.factor (alpha C ε) n (6*totalWeight D.weight)*
    weightedCost D.cost D.weight

def readyCharge {n : ℕ} {D : Input n} (r : Ready D) (extra : ℕ) (state : Ledger) : ℕ :=
  let N := r.chain.size
  let K := commonCharge N (StatefulBoundedRoundingQuality.canonicalFuel N)
    r.chain.cutoff.bits (ledgerWidth state) (totalCallbacks N extra)
  readyWordBound n+(extra+1)*(EncodedAllRegimeRounding.operationBound N K+4*N+28)+10+
    (1920*n^4+108*n^3+1012*n^2+122*n+59)+16

theorem finish_good {n : ℕ} {D : Input n} (r : Ready D) (hn : 0<n)
    (C ε : ℝ) (extra : ℕ) (state : Ledger)
    {core : EncodedRoundingRepetition.Result r.chain.size × Ledger}
    (hc : core ∈ ((EncodedRoundingRepetition.run
      (sample r.chain.size r.chain.cutoff r.cutoff_positive)
      r.chain.data.adjacency r.cutoff_positive extra).run state).support)
    (hsize : core.1.selected.vertices.length ≤ threshold C ε r.chain.size r.chain.cutoff) :
    IsIntegralCut D.graph (selectedSet (finish r core.1).mask)
        (thresholdDemands D.graph D.weight) ∧
      cutCost D.cost (selectedSet (finish r core.1).mask) ≤ costBound D C ε ∧
      core.2.operations=state.operations+(finish r core.1).sampling ∧
      (finish r core.1).operations ≤ readyCharge r extra state := by
  let : NeZero r.chain.cutoff := ⟨r.cutoff_positive.ne'⟩
  have hs := StatefulOutputShape.selected_shape
    (sample r.chain.size r.chain.cutoff r.cutoff_positive)
    r.chain.data.adjacency r.cutoff_positive extra state hc
  have hj := StatefulRoundingCertificate.run_certificate
    (StatefulBoundedRoundingQuality.canonicalFuel r.chain.size)
    r.chain.cutoff.bits (value_bits r.chain.cutoff)
    r.chain.data.adjacency r.cutoff_positive extra state hc
  have hv : IsIntegralCut r.chain.data.graph (selectedSet core.1.selected.flags)
      (CandidateSchedule.unweightedDemands r.chain.data.graph (r.chain.cutoff : ℝ≥0) :
        Set (Pair r.chain.size)) := by
    rw [← hs.2]
    exact hj.1
  have hen := r.envelope hn
  have hN : r.chain.size≠0 := by have hL := r.cutoff_positive; omega
  have hN' : (r.chain.size : ℝ≥0)≠0 := by exact_mod_cast hN
  have hL' : (r.chain.cutoff : ℝ≥0)≠0 := by exact_mod_cast r.cutoff_positive.ne'
  have hnormalize : alpha C ε r.chain.size r.chain.cutoff *
      (r.chain.size : ℝ≥0)/r.chain.cutoff = threshold C ε r.chain.size r.chain.cutoff := by
    unfold alpha
    field_simp [hN',hL']
  have hcard : ((selectedSet core.1.selected.flags).card : ℝ≥0) ≤
      alpha C ε r.chain.size r.chain.cutoff*(r.chain.size : ℝ≥0)/r.chain.cutoff := by
    rw [hnormalize,← hs.2,List.toFinset_card_of_nodup hs.1]
    exact_mod_cast hsize
  have hcost := r.pullback_cost hn (alpha C ε) core.1.selected.flags hv hcard
  have hp := r.pullback_work hn core.1.selected.flags
  have hr := r.operations_bound hn
  refine ⟨r.pullback_valid core.1.selected.flags hv,hcost,hj.2.2.2.1,?_⟩
  have hop := hj.2.2.2.2.2
  change r.operations+core.1.operations+(r.pullback core.1.selected.flags).2+16 ≤ _
  dsimp only [readyCharge]
  omega

/-- All failures refer to one actual weighted output and its retained ledger. -/
def Good {n : ℕ} (D : Input n) (C ε : ℝ) (bound : ℕ) (state : Ledger)
    (out : EncodedWeightedVertexQuery.Output n × Ledger) : Prop :=
  IsIntegralCut D.graph (selectedSet out.1.mask) (thresholdDemands D.graph D.weight) ∧
    cutCost D.cost (selectedSet out.1.mask) ≤ costBound D C ε ∧
    out.2.operations=state.operations+out.1.sampling ∧ out.1.operations≤bound

private theorem push_failure_le {A B : Type} (μ : PMF A) (f : A → B)
    (P : A → Prop) (Q : B → Prop)
    (h : ∀ a∈μ.support, P a → Q (f a)) :
    (((μ.map f).toOuterMeasure {b | ¬Q b}).toReal) ≤
      (μ.toOuterMeasure {a | ¬P a}).toReal := by
  rw [PMF.toOuterMeasure_map_apply]
  apply ENNReal.toReal_mono
  · rw [PMF.toOuterMeasure_apply]
    exact μ.tsum_coe_indicator_ne_top _
  · apply μ.toOuterMeasure_mono
    intro a ha
    exact fun hp => ha.1 (h a ha.2 hp)

/-- One constant is fixed before the original graph, current cost array,
prepared chain, repetition count and entering ledger. -/
theorem uniform_ready_confidence :
    ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧
      ∀ (n : ℕ) (D : Input n) (hn : 0<n) (r : Ready D) (k : ℕ) (state : Ledger),
      ((((runReady sample r (3*k)).run state).toOuterMeasure
        {out | ¬Good D C ε (readyCharge r (3*k) state) state out}).toReal) ≤ ((1 : ℝ)/2)^k := by
  intro ε hε
  obtain ⟨C,hC,hquality⟩ := StatefulRoundingCertificate.uniform_joint_confidence ε hε
  refine ⟨C,hC,?_⟩
  intro n D hn r k state
  let : NeZero r.chain.cutoff := ⟨r.cutoff_positive.ne'⟩
  let fuel := StatefulBoundedRoundingQuality.canonicalFuel r.chain.size
  have hf : FairBitConfidence.trials (AllRegimeBoundedTapeLaw.drawBudget r.chain.size) 2 ≤
      value fuel := by rw [StatefulBoundedRoundingQuality.canonicalFuel_value]
  have hq := hquality r.chain.size r.chain.cutoff fuel r.chain.cutoff.bits
    (value_bits r.chain.cutoff) r.chain.data.adjacency r.cutoff_positive k state hf
  let μ := (EncodedRoundingRepetition.run
    (sample r.chain.size r.chain.cutoff r.cutoff_positive)
    r.chain.data.adjacency r.cutoff_positive (3*k)).run state
  let P := fun core : EncodedRoundingRepetition.Result r.chain.size × Ledger =>
    StatefulRoundingCertificate.Certificate fuel r.chain.cutoff.bits r.chain.data.adjacency
      r.chain.cutoff (3*k) state core ∧
      core.1.selected.vertices.length ≤ threshold C ε r.chain.size r.chain.cutoff
  have ht := push_failure_le μ (fun core => (finish r core.1,core.2)) P
    (Good D C ε (readyCharge r (3*k) state) state)
    (fun core hc hp => finish_good r hn C ε (3*k) state hc hp.2)
  have he : ((runReady sample r (3*k)).run state) =
      μ.map (fun core => (finish r core.1,core.2)) := rfl
  rw [he]
  exact ht.trans hq

/-- The branch-specific counter is read from the same deterministic preparation.
It prices the concrete finished branch or the actual repeated Ready branch. -/
def chargeBound {n : ℕ} (D : Input n) (extra : ℕ) (state : Ledger) : ℕ :=
  match prepare D with
  | .inl done => done.operations
  | .inr r => readyCharge r extra state

theorem uniform_run_confidence :
    ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧
      ∀ (n : ℕ) (D : Input n) (hn : 0<n) (k : ℕ) (state : Ledger),
      ((((run sample D (3*k)).run state).toOuterMeasure
        {out | ¬Good D C ε (chargeBound D (3*k) state) state out}).toReal) ≤ ((1 : ℝ)/2)^k := by
  intro ε hε
  obtain ⟨C,hC,hready⟩ := uniform_ready_confidence ε hε
  refine ⟨C,hC,?_⟩
  intro n D hn k state
  unfold run chargeBound
  cases h : prepare D with
  | inl done =>
      change ((PMF.pure (done.output,state)).toOuterMeasure
        {out | ¬Good D C ε done.operations state out}).toReal ≤ _
      have hg : Good D C ε done.operations state (done.output,state) := by
        refine ⟨done.valid,?_,?_,le_rfl⟩
        · change cutCost D.cost (selectedSet done.mask) ≤ _
          rw [done.zero_cost]
          exact zero_le _
        · exact (Nat.add_zero _).symm
      have hz : (PMF.pure (done.output,state)).toOuterMeasure
          {out | ¬Good D C ε done.operations state out} = 0 := by
        apply (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr
        apply Set.disjoint_left.mpr
        intro out ho hb
        have he := (PMF.mem_support_pure_iff _ _).mp ho
        subst out
        exact hb hg
      rw [hz,ENNReal.toReal_zero]
      positivity
  | inr r => exact hready n D hn r k state

/-- The original weights and exact current penalized row are passed to the
actual query wrapper. Its additional four operations are paid explicitly. -/
theorem uniform_query_confidence :
    ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧
      ∀ (n : ℕ) (hn : 0<n) (adjacency : PairFlags n)
        (weights costs : Vector RawNonnegativeRational.Code n) (k : ℕ) (state : Ledger),
      let D := queryInput adjacency weights costs
      ((((query sample adjacency weights costs (3*k)).run state).toOuterMeasure
        {out | ¬Good D C ε (chargeBound D (3*k) state+4) state out}).toReal) ≤ ((1 : ℝ)/2)^k := by
  intro ε hε
  obtain ⟨C,hC,hrun⟩ := uniform_run_confidence ε hε
  refine ⟨C,hC,?_⟩
  intro n hn adjacency weights costs k state
  let D := queryInput adjacency weights costs
  let μ := (run sample D (3*k)).run state
  let f := fun out : EncodedWeightedVertexQuery.Output n × Ledger =>
    ({out.1 with operations := out.1.operations+4},out.2)
  have ht := push_failure_le μ f
    (Good D C ε (chargeBound D (3*k) state) state)
    (Good D C ε (chargeBound D (3*k) state+4) state)
    (fun out _ hp => ⟨hp.1,hp.2.1,hp.2.2.1,Nat.add_le_add_right hp.2.2.2 4⟩)
  have he : ((query sample adjacency weights costs (3*k)).run state) = μ.map f := rfl
  change _ ≤ _
  rw [he]
  exact ht.trans (hrun n D hn k state)

end
end DirectedFlowCutGap.StatefulWeightedQuery
