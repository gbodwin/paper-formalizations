import DirectedFlowCutGap.StatefulHeavyQuery
import DirectedFlowCutGap.StatefulWeightedEnvelope

/-! Source-shaped cube-root cost factor for the actual shared-ledger heavy
query. The same returned cut and declared charge are retained. Binary input
and fuel construction, physical storage/runtime, and the adaptive packing
provider remain outside this theorem. -/
namespace DirectedFlowCutGap.StatefulHeavyRate
noncomputable section
open scoped NNReal
open EncodedUnitCostReplication StatefulHeavyQuery BinarySamplerMetadata


theorem root_mass {N q B : ℝ} (_hN : 0≤N) (hq : 0<q) (hB : 0≤B)
    (hcube : N≤q^3) (hmass : B≤3*N/q) : B^((1:ℝ)/2) ≤ 2*q := by
  have hb : B≤(2*q)^2 := by
    have h := (div_le_iff₀ hq).mpr (show 3*N≤(3*q^2)*q by nlinarith)
    nlinarith
  have h := Real.rpow_le_rpow hB hb (by norm_num : (0:ℝ)≤1/2)
  have he : ((2*q)^2)^((1:ℝ)/2)=2*q := by
    simpa [one_div] using Real.pow_rpow_inv_natCast (by positivity : 0≤2*q) (by decide : (2:ℕ)≠0)
  rwa [he] at h

theorem proxy_upper {N q : ℝ} (hN : 0≤N) (hq : 0≤q) (hcube : q^3≤8*N) :
    q≤2*N^((1:ℝ)/3) := by
  have h := Real.rpow_le_rpow (pow_nonneg hq 3) hcube (by norm_num : (0:ℝ)≤1/3)
  have he : (q^3)^((1:ℝ)/3)=q := by
    simpa [one_div] using Real.pow_rpow_inv_natCast hq (by decide : (3:ℕ)≠0)
  have hn : 8*N=(2*N^((1:ℝ)/3))^3 := by
    have hr : (N^((1:ℝ)/3))^3=N := by
      simpa [one_div] using Real.rpow_inv_natCast_pow hN (by decide : (3:ℕ)≠0)
    rw [mul_pow,hr]
    norm_num
  rw [he,hn] at h
  have he' : ((2*N^((1:ℝ)/3))^3)^((1:ℝ)/3)=2*N^((1:ℝ)/3) := by
    simpa [one_div] using Real.pow_rpow_inv_natCast (by positivity : 0≤2*N^((1:ℝ)/3)) (by decide : (3:ℕ)≠0)
  rwa [he'] at h

theorem heavy_rate {N q B F C ε : ℝ} (hN : 1≤N) (hq : 0<q)
    (hB : 0≤B) (hC : 0≤C) (hε : 0≤ε)
    (hlo : N≤q^3) (hhi : q^3≤8*N) (hmass : B≤3*N/q)
    (hF : F≤12*(2*C*(24*N^2)^ε+3)*B^((1:ℝ)/2)) :
    4*q+2*F ≤ (296+192*C*24^ε)*N^((1:ℝ)/3+2*ε) := by
  have hN0 : 0<N := by linarith
  have hr := root_mass hN0.le hq hB hlo hmass
  have hq' := proxy_upper hN0.le hq.le hhi
  have hA : (24*N^2)^ε=24^ε*N^(2*ε) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤24) (sq_nonneg N),
      ← Real.rpow_natCast_mul hN0.le 2 ε]
    norm_num
  have hE : 1≤N^(2*ε) := Real.one_le_rpow hN (by positivity)
  have hP : 0≤2*C*(24*N^2)^ε+3 := by positivity
  have hi : F≤24*(2*C*(24*N^2)^ε+3)*q := by
    have h := mul_le_mul_of_nonneg_left hr (show 0≤12*(2*C*(24*N^2)^ε+3) by positivity)
    exact hF.trans (by nlinarith)
  have hcoef : 4+48*(2*C*(24*N^2)^ε+3) ≤
      (148+96*C*24^ε)*N^(2*ε) := by
    rw [hA]
    nlinarith
  have hfac : 4*q+2*F ≤ q*((148+96*C*24^ε)*N^(2*ε)) := by
    have h := mul_le_mul_of_nonneg_left hcoef hq.le
    nlinarith
  have hqmul := mul_le_mul_of_nonneg_right hq'
    (show 0≤(148+96*C*24^ε)*N^(2*ε) by positivity)
  apply hfac.trans
  apply hqmul.trans
  rw [Real.rpow_add hN0]
  ring_nf
  exact le_rfl

theorem innerFactor_le {n : ℕ} (D : Input n) {C ε : ℝ} (hC : 0≤C) (hε : 0≤ε) :
    (innerFactor D C ε : ℝ) ≤
      12*(2*C*(24*(n:ℝ)^2)^ε+3)*
        (6*(totalWeight (residual D).data.weight : ℝ))^((1:ℝ)/2) := by
  have hf := StatefulWeightedEnvelope.factor_le hC hε (residual D).size
    (6*totalWeight (residual D).data.weight)
  have hs := EncodedHeavyVertexPreparation.build_size_le D (EncodedCubeRootThreshold.threshold n)
  have hs' : ((residual D).size : ℝ)≤n := by exact_mod_cast hs
  have hsq : (24*(residual D).size^2 : ℝ)≤24*(n:ℝ)^2 := by
    nlinarith [Nat.cast_nonneg (residual D).size]
  have hp := Real.rpow_le_rpow (by positivity : (0:ℝ)≤24*(residual D).size^2) hsq hε
  have hl : 2*C*(24*(residual D).size^2 : ℝ)^ε+3 ≤ 2*C*(24*(n:ℝ)^2)^ε+3 := by
    nlinarith [mul_le_mul_of_nonneg_left hp (show 0≤2*C by positivity)]
  have hprod := mul_le_mul_of_nonneg_right hl
    (Real.rpow_nonneg (by positivity : (0:ℝ)≤6*(totalWeight (residual D).data.weight : ℝ)) ((1:ℝ)/2))
  have h := hf.trans (by simpa [StatefulWeightedEnvelope.factorBound] using hprod)
  exact mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤12)

theorem costBound_le {n : ℕ} (hn : 0<n) (D : Input n) {C ε : ℝ}
    (hC : 0≤C) (hε : 0≤ε) :
    (StatefulHeavyQuery.costBound D C ε : ℝ) ≤
      (296+192*C*24^ε)*(n:ℝ)^((1:ℝ)/3+2*ε)*(weightedCost D.cost D.weight : ℝ) := by
  let q := EncodedCubeRootThreshold.ceilCube n
  have hq : (0:ℝ)<q := by exact_mod_cast EncodedCubeRootThreshold.ceilCube_positive n
  have hlo : (n:ℝ)≤(q:ℝ)^3 := by
    have h := EncodedCubeRootThreshold.le_cube_ceilCube n
    simpa [EncodedCubeRootThreshold.cube,pow_succ] using (show (n:ℝ)≤(q:ℝ)*(q:ℝ)*(q:ℝ) from by exact_mod_cast h)
  have hhi : (q:ℝ)^3≤8*(n:ℝ) := by
    have h := EncodedCubeRootThreshold.cube_ceilCube_le n hn
    simpa [pow_succ] using (show (q:ℝ)*(q:ℝ)*(q:ℝ)≤8*(n:ℝ) from by exact_mod_cast h)
  have hm := EncodedHeavyVertexPreparation.build_totalWeight_le D
    (EncodedCubeRootThreshold.threshold n)
  rw [EncodedCubeRootThreshold.threshold_value] at hm
  have hm' : (totalWeight (residual D).data.weight : ℝ) ≤ 2*(n:ℝ)*(1/(4*(q:ℝ))) := by
    exact_mod_cast hm
  have hmass : 6*(totalWeight (residual D).data.weight : ℝ)≤3*(n:ℝ)/(q:ℝ) := by
    calc
      _ ≤ 6*(2*(n:ℝ)*(1/(4*(q:ℝ)))) := mul_le_mul_of_nonneg_left hm' (by norm_num)
      _ = _ := by field_simp;ring
  have h := heavy_rate (by exact_mod_cast hn : (1:ℝ)≤n) hq
    (by positivity) hC hε hlo hhi hmass (innerFactor_le D hC hε)
  exact mul_le_mul_of_nonneg_right h (NNReal.coe_nonneg (weightedCost D.cost D.weight))

def Good {n : ℕ} (D : Input n) (K δ : ℝ) (extra : ℕ) (state : Ledger)
    (out : EncodedWeightedVertexQuery.Output n × Ledger) : Prop :=
  IsIntegralCut D.graph (selectedSet out.1.mask) (thresholdDemands D.graph D.weight) ∧
    (cutCost D.cost (selectedSet out.1.mask) : ℝ) ≤
      K*(n:ℝ)^((1:ℝ)/3+δ)*(weightedCost D.cost D.weight : ℝ) ∧
    out.2.operations=state.operations+out.1.sampling ∧ out.1.operations≤chargeBound D extra state

/-- Uniform n^(1/3+delta) weighted-cut guarantee for the actual heavy query,
with failure at most 2^-k and the same returned ledger/declared charge. -/
theorem uniform_confidence :
    ∀ δ : ℝ, 0<δ → ∃ K : ℝ, 0<K ∧
      ∀ (n : ℕ) (hn : 0<n) (D : Input n) (k : ℕ) (state : Ledger),
      ((((StatefulHeavyQuery.run D (3*k)).run state).toOuterMeasure
        {out | ¬Good D K δ (3*k) state out}).toReal) ≤ ((1:ℝ)/2)^k := by
  intro δ hδ
  obtain ⟨C,hC,hq⟩ := StatefulHeavyQuery.uniform_confidence (δ/2) (by positivity)
  refine ⟨296+192*C*24^(δ/2),by positivity,?_⟩
  intro n hn D k state
  let μ := (StatefulHeavyQuery.run D (3*k)).run state
  have hg (out : EncodedWeightedVertexQuery.Output n × Ledger)
      (ho : StatefulHeavyQuery.Good D C (δ/2) (3*k) state out) :
      Good D (296+192*C*24^(δ/2)) δ (3*k) state out := by
    refine ⟨ho.1,?_,ho.2.2⟩
    have hc : (cutCost D.cost (selectedSet out.1.mask) : ℝ)≤StatefulHeavyQuery.costBound D C (δ/2) := by
      exact_mod_cast ho.2.1
    have h := hc.trans (costBound_le hn D hC.le (by positivity))
    simpa only [show 2*(δ/2)=δ by ring] using h
  have hp : μ.toOuterMeasure {out | ¬Good D (296+192*C*24^(δ/2)) δ (3*k) state out} ≤
      μ.toOuterMeasure {out | ¬StatefulHeavyQuery.Good D C (δ/2) (3*k) state out} := by
    apply μ.toOuterMeasure.mono
    intro out hb ho
    exact hb (hg out ho)
  exact (ENNReal.toReal_mono
    (by rw [PMF.toOuterMeasure_apply];exact μ.tsum_coe_indicator_ne_top _) hp).trans (hq n D k state)

end
end DirectedFlowCutGap.StatefulHeavyRate
