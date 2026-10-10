import DirectedFlowCutGap.StatefulHeavyValidity
import DirectedFlowCutGap.StatefulHeavyRate

/-! Declared charges and sampler accounting hold for every supported heavy
query result, including bad-quality outcomes. This is the existing annotated
operation model; raw/fuel construction and physical execution are separate. -/
namespace DirectedFlowCutGap.StatefulHeavyPathwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
open EncodedUnitCostReplication EncodedWeightedVertexQuery BinarySamplerMetadata
open BinaryArithmetic

theorem ready_charge {n : ℕ} {D : Input n} (r : Ready D) (hn : 0<n)
    (extra : ℕ) (state : Ledger)
    {core : EncodedRoundingRepetition.Result r.chain.size × Ledger}
    (hc : core∈((EncodedRoundingRepetition.run
      (StatefulWeightedQuery.sample r.chain.size r.chain.cutoff r.cutoff_positive)
      r.chain.data.adjacency r.cutoff_positive extra).run state).support) :
    core.2.operations=state.operations+(finish r core.1).sampling ∧
      (finish r core.1).operations≤StatefulWeightedQuery.readyCharge r extra state := by
  let : NeZero r.chain.cutoff := ⟨r.cutoff_positive.ne'⟩
  have hj := StatefulRoundingCertificate.run_certificate
    (StatefulBoundedRoundingQuality.canonicalFuel r.chain.size)
    r.chain.cutoff.bits (value_bits r.chain.cutoff)
    r.chain.data.adjacency r.cutoff_positive extra state hc
  have hp := r.pullback_work hn core.1.selected.flags
  have hr := r.operations_bound hn
  refine ⟨hj.2.2.2.1,?_⟩
  have hop := hj.2.2.2.2.2
  change r.operations+core.1.operations+(r.pullback core.1.selected.flags).2+16≤_
  dsimp only [StatefulWeightedQuery.readyCharge]
  omega

theorem weighted_charge {n : ℕ} (D : Input n) (hn : 0<n) (extra : ℕ) (state : Ledger)
    {out : Output n × Ledger}
    (hout : out∈((run StatefulWeightedQuery.sample D extra).run state).support) :
    out.2.operations=state.operations+out.1.sampling ∧
      out.1.operations≤StatefulWeightedQuery.chargeBound D extra state := by
  unfold run at hout
  unfold StatefulWeightedQuery.chargeBound
  cases h : prepare D with
  | inl done =>
      rw [h] at hout
      have he := (PMF.mem_support_pure_iff _ _).mp hout
      subst out
      exact ⟨(Nat.add_zero _).symm,le_rfl⟩
  | inr r =>
      rw [h] at hout
      have he : ((runReady StatefulWeightedQuery.sample r extra).run state)=
          (((EncodedRoundingRepetition.run
            (StatefulWeightedQuery.sample r.chain.size r.chain.cutoff r.cutoff_positive)
            r.chain.data.adjacency r.cutoff_positive extra).run state).map
            (fun core => (finish r core.1,core.2))) := rfl
      rw [he] at hout
      obtain ⟨core,hc,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
      exact ready_charge r hn extra state hc

/-- The complete heavy result carries its actual cumulative sampler charge
and the deterministic declared-operation envelope, on every sample path. -/
theorem heavy_charge {n : ℕ} (D : Input n) (extra : ℕ) (state : Ledger)
    {out : Output n × Ledger}
    (hout : out∈((StatefulHeavyQuery.run D extra).run state).support) :
    out.2.operations=state.operations+out.1.sampling ∧
      out.1.operations≤StatefulHeavyQuery.chargeBound D extra state := by
  have finish_bound (inner : Output (StatefulHeavyQuery.residual D).size × Ledger)
      (hi : inner.2.operations=state.operations+inner.1.sampling ∧
        inner.1.operations≤StatefulHeavyQuery.innerCharge D extra state) :
      inner.2.operations=state.operations+
          (StatefulHeavyQuery.finish (EncodedHeavyVertexPreparation.prepare D) inner.1).sampling ∧
        (StatefulHeavyQuery.finish (EncodedHeavyVertexPreparation.prepare D) inner.1).operations≤
          StatefulHeavyQuery.chargeBound D extra state := by
    have hw := EncodedHeavyVertexPreparation.build_combinedMask_work D
      (EncodedCubeRootThreshold.threshold n) inner.1.mask
    change (EncodedHeavyVertexPreparation.combinedMaskWithCost
      (StatefulHeavyQuery.residual D) inner.1.mask).2≤20*n^2+66*n+36 at hw
    refine ⟨hi.1,?_⟩
    have hop := hi.2
    change (EncodedHeavyVertexPreparation.prepare D).2+inner.1.operations+
      (EncodedHeavyVertexPreparation.combinedMaskWithCost (StatefulHeavyQuery.residual D) inner.1.mask).2+12≤_
    dsimp only [StatefulHeavyQuery.chargeBound]
    omega
  by_cases hz : (StatefulHeavyQuery.residual D).size=0
  · have he : (StatefulHeavyQuery.run D extra).run state=PMF.pure
        (StatefulHeavyQuery.finish (EncodedHeavyVertexPreparation.prepare D)
          (StatefulHeavyQuery.emptyOutput (StatefulHeavyQuery.residual D).size),state) := by
      simp only [StatefulHeavyQuery.run,hz,ite_true]
      rfl
    rw [he] at hout
    have ho := (PMF.mem_support_pure_iff _ _).mp hout
    subst out
    apply finish_bound (StatefulHeavyQuery.emptyOutput (StatefulHeavyQuery.residual D).size,state)
    exact ⟨(Nat.add_zero _).symm,by simp only [StatefulHeavyQuery.innerCharge,hz,ite_true,
      StatefulHeavyQuery.emptyOutput,le_refl]⟩
  · have he : (StatefulHeavyQuery.run D extra).run state=
        (((run StatefulWeightedQuery.sample (StatefulHeavyQuery.residual D).data extra).run state).map
          (fun inner => (StatefulHeavyQuery.finish (EncodedHeavyVertexPreparation.prepare D) inner.1,inner.2))) := by
      simp only [StatefulHeavyQuery.run,hz,ite_false]
      rfl
    rw [he] at hout
    obtain ⟨inner,hi,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
    apply finish_bound inner
    have hc := weighted_charge (StatefulHeavyQuery.residual D).data (Nat.pos_of_ne_zero hz) extra state hi
    simpa only [StatefulHeavyQuery.innerCharge,hz,ite_false] using hc

end
end DirectedFlowCutGap.StatefulHeavyPathwise
