import DirectedFlowCutGap.StatefulWeightedQuery

/-!
# Actual heavy-vertex preparation and stateful weighted rounding

The computed heavy threshold and residual are retained once. The actual
residual query is run on its stored raw arrays, then its literal selected
mask is lifted and unioned with the stored heavy mask. The zero-residual
branch is explicit. The same final record retains every declared preparation,
query and pullback charge. This module keeps the finite approximation envelope;
its analytic rate and the physical bit-storage/provider joins are separate.
Binary raw-input materialization and fuel-word construction are not priced by
these declared counters.
-/
namespace DirectedFlowCutGap.StatefulHeavyQuery
noncomputable section
open scoped NNReal
open EncodedUnitCostReplication EncodedWeightedVertexQuery
open BinarySamplerMetadata RetainedGridState
set_option backward.isDefEq.respectTransparency false

abbrev residual {n : ℕ} (D : Input n) := (EncodedHeavyVertexPreparation.prepare D).1

def emptyOutput (n : ℕ) : EncodedWeightedVertexQuery.Output n :=
  ⟨Vector.replicate n false,2*n+8,0,none⟩

def finish {n : ℕ} (prepared : EncodedHeavyVertexPreparation.Residual n × ℕ)
    (inner : EncodedWeightedVertexQuery.Output prepared.1.size) : EncodedWeightedVertexQuery.Output n :=
  let lifted := EncodedHeavyVertexPreparation.combinedMaskWithCost prepared.1 inner.mask
  { mask := lifted.1
    operations := prepared.2+inner.operations+lifted.2+12
    sampling := inner.sampling
    core := inner.core }

def run {n : ℕ} (D : Input n) (extra : ℕ) : StateT Ledger PMF (EncodedWeightedVertexQuery.Output n) := do
  let prepared := EncodedHeavyVertexPreparation.prepare D
  if prepared.1.size=0 then pure (finish prepared (emptyOutput prepared.1.size)) else
    let inner ← EncodedWeightedVertexQuery.run StatefulWeightedQuery.sample prepared.1.data extra
    pure (finish prepared inner)

def innerFactor {n : ℕ} (D : Input n) (C ε : ℝ) : ℝ≥0 :=
  12*EncodedWeightedEnvelope.factor (StatefulWeightedQuery.alpha C ε)
    (residual D).size (6*totalWeight (residual D).data.weight)

def costBound {n : ℕ} (D : Input n) (C ε : ℝ) : ℝ≥0 :=
  (4*(EncodedCubeRootThreshold.ceilCube n : ℝ≥0)+2*innerFactor D C ε)*
    weightedCost D.cost D.weight

def innerCharge {n : ℕ} (D : Input n) (extra : ℕ) (state : Ledger) : ℕ :=
  if (residual D).size=0 then 2*(residual D).size+8 else
    StatefulWeightedQuery.chargeBound (residual D).data extra state

def chargeBound {n : ℕ} (D : Input n) (extra : ℕ) (state : Ledger) : ℕ :=
  (EncodedHeavyVertexPreparation.prepare D).2+innerCharge D extra state+
    (20*n^2+66*n+36)+12

def Good {n : ℕ} (D : Input n) (C ε : ℝ) (extra : ℕ) (state : Ledger)
    (out : EncodedWeightedVertexQuery.Output n × Ledger) : Prop :=
  IsIntegralCut D.graph (selectedSet out.1.mask) (thresholdDemands D.graph D.weight) ∧
    cutCost D.cost (selectedSet out.1.mask) ≤ costBound D C ε ∧
    out.2.operations=state.operations+out.1.sampling ∧ out.1.operations≤chargeBound D extra state

theorem finish_good {n : ℕ} (D : Input n) (C ε : ℝ) (extra : ℕ) (state : Ledger)
    (inner : EncodedWeightedVertexQuery.Output (residual D).size × Ledger)
    (h : StatefulWeightedQuery.Good (residual D).data C ε
      (innerCharge D extra state) state inner) :
    Good D C ε extra state (finish (EncodedHeavyVertexPreparation.prepare D) inner.1,inner.2) := by
  have hp := EncodedHeavyVertexPreparation.proxy_output_spec D (innerFactor D C ε)
    inner.1.mask h.1 h.2.1
  have hw : (EncodedHeavyVertexPreparation.combinedMaskWithCost (residual D) inner.1.mask).2 ≤
      20*n^2+66*n+36 := EncodedHeavyVertexPreparation.build_combinedMask_work D
        (EncodedCubeRootThreshold.threshold n) inner.1.mask
  refine ⟨hp.1,hp.2,h.2.2.1,?_⟩
  have hi := h.2.2.2
  change (EncodedHeavyVertexPreparation.prepare D).2+inner.1.operations+
    (EncodedHeavyVertexPreparation.combinedMaskWithCost (residual D) inner.1.mask).2+12 ≤ _
  dsimp only [chargeBound]
  omega

private theorem push_failure_le {A B : Type} (μ : PMF A) (f : A → B)
    (P : A → Prop) (Q : B → Prop) (h : ∀ a, P a → Q (f a)) :
    (((μ.map f).toOuterMeasure {b | ¬Q b}).toReal) ≤
      (μ.toOuterMeasure {a | ¬P a}).toReal := by
  rw [PMF.toOuterMeasure_map_apply]
  apply ENNReal.toReal_mono
  · rw [PMF.toOuterMeasure_apply]
    exact μ.tsum_coe_indicator_ne_top _
  · apply μ.toOuterMeasure.mono
    intro a ha hp
    exact ha (h a hp)

/-- The actual prepared-heavy query includes zero residuals and arbitrary
entering ledgers; no caller cut-quality or sampler-law hypothesis is needed. -/
theorem uniform_confidence :
    ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧
      ∀ (n : ℕ) (D : Input n) (k : ℕ) (state : Ledger),
      ((((run D (3*k)).run state).toOuterMeasure
        {out | ¬Good D C ε (3*k) state out}).toReal) ≤ ((1 : ℝ)/2)^k := by
  intro ε hε
  obtain ⟨C,hC,hquery⟩ := StatefulWeightedQuery.uniform_run_confidence ε hε
  refine ⟨C,hC,?_⟩
  intro n D k state
  by_cases hz : (residual D).size=0
  · have hi : StatefulWeightedQuery.Good (residual D).data C ε
        (innerCharge D (3*k) state) state (emptyOutput (residual D).size,state) := by
      refine ⟨?_,?_,?_,?_⟩
      · intro s
        have hs := s.isLt
        omega
      · change cutCost (residual D).data.cost
          (selectedSet (Vector.replicate (residual D).size false)) ≤ _
        rw [selectedSet_false]
        simp only [cutCost,Finset.sum_empty]
        exact zero_le
      · exact (Nat.add_zero _).symm
      · simp only [innerCharge,hz,ite_true,emptyOutput,le_refl]
    have hg := finish_good D C ε (3*k) state _ hi
    have he : (run D (3*k)).run state =
        PMF.pure (finish (EncodedHeavyVertexPreparation.prepare D) (emptyOutput (residual D).size),state) := by
      simp only [run,hz,ite_true]
      rfl
    rw [he]
    have hzprob : (PMF.pure
        (finish (EncodedHeavyVertexPreparation.prepare D) (emptyOutput (residual D).size),state)).toOuterMeasure
        {out | ¬Good D C ε (3*k) state out} = 0 := by
      apply (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr
      apply Set.disjoint_left.mpr
      intro out ho hb
      have he := (PMF.mem_support_pure_iff _ _).mp ho
      subst out
      exact hb hg
    rw [hzprob,ENNReal.toReal_zero]
    positivity
  · have hn : 0<(residual D).size := Nat.pos_of_ne_zero hz
    let μ := (EncodedWeightedVertexQuery.run StatefulWeightedQuery.sample (residual D).data (3*k)).run state
    let f := fun inner : EncodedWeightedVertexQuery.Output (residual D).size × Ledger =>
      (finish (EncodedHeavyVertexPreparation.prepare D) inner.1,inner.2)
    have ht := push_failure_le μ f
      (StatefulWeightedQuery.Good (residual D).data C ε (innerCharge D (3*k) state) state)
      (Good D C ε (3*k) state) (fun inner hi => finish_good D C ε (3*k) state inner hi)
    have hq := hquery (residual D).size (residual D).data hn k state
    have he : (run D (3*k)).run state = μ.map f := by
      simp only [run,hz,ite_false]
      rfl
    rw [he]
    apply ht.trans
    simpa only [innerCharge,hz,ite_false] using hq

end
end DirectedFlowCutGap.StatefulHeavyQuery
