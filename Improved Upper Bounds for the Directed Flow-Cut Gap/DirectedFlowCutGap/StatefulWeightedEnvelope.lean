import DirectedFlowCutGap.StatefulWeightedQuery

/-! Explicit square-root mass dependence of the finite weighted envelope.
This is an analytic bound on the existing returned-cut guarantee, not a new
sampler or an assumption about an adaptive oracle. -/
namespace DirectedFlowCutGap.StatefulWeightedEnvelope
noncomputable section
open scoped NNReal
open EncodedUnitCostReplication StatefulWeightedQuery

theorem rounded_ratio_le {X R : ℝ} (hX : 0≤X) (hR : 1≤R) :
    (Nat.ceil (2*max 1 (X*R^((3:ℝ)/2))) : ℝ)/R ≤ (2*X+3)*R^((1:ℝ)/2) := by
  have hR0 : 0<R := by linarith
  have hr : 1≤R^((1:ℝ)/2) := Real.one_le_rpow hR (by norm_num)
  have hp : R^((3:ℝ)/2)=R*R^((1:ℝ)/2) := by
    rw [show (3:ℝ)/2=1+1/2 by norm_num,Real.rpow_add hR0,Real.rpow_one]
  have hB : 0≤X*R^((3:ℝ)/2) := mul_nonneg hX (Real.rpow_nonneg hR0.le _)
  have hm : max 1 (X*R^((3:ℝ)/2)) ≤ 1+X*R^((3:ℝ)/2) :=
    max_le (by linarith) (by linarith)
  have hc := (Nat.ceil_lt_add_one (show 0≤2*max 1 (X*R^((3:ℝ)/2)) by positivity)).le
  apply (div_le_iff₀ hR0).mpr
  have hprod : 1≤R*R^((1:ℝ)/2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr hr)]
  rw [hp] at hm hc ⊢
  nlinarith

theorem alpha_le {C ε : ℝ} (hC : 0≤C) {N L : ℕ} (hL : 0<L) (hLN : L≤N) :
    (alpha C ε N L : ℝ) ≤ (2*C*(N : ℝ)^ε+3)*((N : ℝ)/L)^((1:ℝ)/2) := by
  have hL0 : (0:ℝ)<L := by exact_mod_cast hL
  have hN0 : (0:ℝ)<N := by exact_mod_cast (lt_of_lt_of_le hL hLN)
  have hratio : 1≤(N:ℝ)/L := (le_div_iff₀ hL0).mpr (by
    simpa only [one_mul] using (show (L:ℝ)≤N from by exact_mod_cast hLN))
  have h := rounded_ratio_le (mul_nonneg hC (Real.rpow_nonneg hN0.le ε)) hratio
  have ha : (alpha C ε N L : ℝ) = (threshold C ε N L : ℝ)/((N:ℝ)/L) := by
    change (threshold C ε N L : ℝ)*(L:ℝ)/N = _
    field_simp
  rw [ha]
  simpa only [threshold,AdaptiveCost.sizeFactor,Fintype.card_fin,NNReal.coe_natCast,mul_assoc] using h

def factorBound (C ε : ℝ) (n : ℕ) (B : ℝ≥0) : ℝ :=
  (2*C*((24*n^2 : ℕ):ℝ)^ε+3)*(B:ℝ)^((1:ℝ)/2)

theorem factorBound_nonneg {C ε : ℝ} (hC : 0≤C) (n : ℕ) (B : ℝ≥0) :
    0≤factorBound C ε n B := by unfold factorBound; positivity

theorem factor_le {C ε : ℝ} (hC : 0≤C) (hε : 0≤ε) (n : ℕ) (B : ℝ≥0) :
    (EncodedWeightedEnvelope.factor (alpha C ε) n B : ℝ) ≤ factorBound C ε n B := by
  have hf : EncodedWeightedEnvelope.factor (alpha C ε) n B ≤
      Real.toNNReal (factorBound C ε n B) := by
    apply EncodedWeightedEnvelope.factor_le
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    have hn := (Finset.mem_range.mp (Finset.mem_product.mp
      (Finset.mem_filter.mp hp).1).1)
    have hN : p.1 ≤24*n^2 := by omega
    have hmass : (p.1 : ℝ)/(p.2 : ℝ)≤(B:ℝ) := by exact_mod_cast hp'.2.2.2
    have hpow := Real.rpow_le_rpow (Nat.cast_nonneg p.1)
      (by exact_mod_cast hN : (p.1:ℝ)≤((24*n^2:ℕ):ℝ)) hε
    have hroot := Real.rpow_le_rpow (div_nonneg (Nat.cast_nonneg p.1) (Nat.cast_nonneg p.2))
      hmass (by norm_num : (0:ℝ)≤1/2)
    have hleft : 2*C*(p.1:ℝ)^ε+3 ≤ 2*C*((24*n^2:ℕ):ℝ)^ε+3 := by
      nlinarith [mul_le_mul_of_nonneg_left hpow (show 0≤2*C by positivity)]
    have h := (alpha_le hC hp'.2.1 hp'.2.2.1).trans
      (mul_le_mul hleft hroot (Real.rpow_nonneg (by positivity) _)
        (by positivity))
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ (factorBound_nonneg hC n B)]
    exact h
  have h := (NNReal.coe_le_coe.mpr hf)
  simpa only [Real.coe_toNNReal _ (factorBound_nonneg hC n B)] using h

theorem costBound_le {n : ℕ} (D : Input n) {C ε : ℝ} (hC : 0≤C) (hε : 0≤ε) :
    (StatefulWeightedQuery.costBound D C ε : ℝ) ≤
      12*factorBound C ε n (6*totalWeight D.weight)*(weightedCost D.cost D.weight : ℝ) := by
  have hf := factor_le hC hε n (6*totalWeight D.weight)
  have hp := mul_le_mul_of_nonneg_left hf (by norm_num : (0:ℝ)≤12)
  have h := mul_le_mul_of_nonneg_right hp (NNReal.coe_nonneg (weightedCost D.cost D.weight))
  exact h

/-- Original-cost guarantee with an explicit square-root weight factor. -/
def Good {n : ℕ} (D : Input n) (C ε : ℝ) (bound : ℕ)
    (state : BinarySamplerMetadata.Ledger)
    (out : EncodedWeightedVertexQuery.Output n × BinarySamplerMetadata.Ledger) : Prop :=
  IsIntegralCut D.graph (selectedSet out.1.mask) (thresholdDemands D.graph D.weight) ∧
    (cutCost D.cost (selectedSet out.1.mask) : ℝ) ≤
      12*factorBound C ε n (6*totalWeight D.weight)*(weightedCost D.cost D.weight : ℝ) ∧
    out.2.operations=state.operations+out.1.sampling ∧ out.1.operations≤bound

/-- The square-root mass factor is uniform across every current penalized
cost row and every entering ledger of the actual concrete query. -/
theorem uniform_query_confidence :
    ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧
      ∀ (n : ℕ) (_hn : 0<n) (adjacency : RetainedGridState.PairFlags n)
        (weights costs : Vector RawNonnegativeRational.Code n) (k : ℕ)
        (state : BinarySamplerMetadata.Ledger),
      let D := EncodedWeightedVertexQuery.queryInput adjacency weights costs
      ((((EncodedWeightedVertexQuery.query sample adjacency weights costs (3*k)).run state).toOuterMeasure
        {out | ¬Good D C ε (chargeBound D (3*k) state+4) state out}).toReal) ≤ ((1 : ℝ)/2)^k := by
  intro ε hε
  obtain ⟨C,hC,hq⟩ := StatefulWeightedQuery.uniform_query_confidence ε hε
  refine ⟨C,hC,?_⟩
  intro n hn adjacency weights costs k state
  let D := EncodedWeightedVertexQuery.queryInput adjacency weights costs
  let μ := (EncodedWeightedVertexQuery.query sample adjacency weights costs (3*k)).run state
  have hgood (out : EncodedWeightedVertexQuery.Output n × BinarySamplerMetadata.Ledger)
      (ho : StatefulWeightedQuery.Good D C ε (chargeBound D (3*k) state+4) state out) :
      Good D C ε (chargeBound D (3*k) state+4) state out := by
    refine ⟨ho.1,?_,ho.2.2⟩
    have hc : (cutCost D.cost (selectedSet out.1.mask) : ℝ) ≤ costBound D C ε := by
      exact_mod_cast ho.2.1
    exact hc.trans (costBound_le D hC.le hε.le)
  have hprob : μ.toOuterMeasure {out | ¬Good D C ε (chargeBound D (3*k) state+4) state out} ≤
      μ.toOuterMeasure {out | ¬StatefulWeightedQuery.Good D C ε
        (chargeBound D (3*k) state+4) state out} := by
    apply μ.toOuterMeasure.mono
    intro out hb ho
    exact hb (hgood out ho)
  have ht := ENNReal.toReal_mono
    (by rw [PMF.toOuterMeasure_apply];exact μ.tsum_coe_indicator_ne_top _) hprob
  exact ht.trans (hq n hn adjacency weights costs k state)

end
end DirectedFlowCutGap.StatefulWeightedEnvelope
