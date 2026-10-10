import DirectedFlowCutGap.StatefulHeavyQuery

/-! Structural cut validity of every supported actual weighted/heavy output.
This removes no size or runtime condition by fiat: it uses the actual retained
selected flags and deterministic pullback. No favorable approximation event or
physical failure-bit assumption is needed. -/
namespace DirectedFlowCutGap.StatefulHeavyValidity
noncomputable section
open EncodedUnitCostReplication EncodedWeightedVertexQuery BinarySamplerMetadata
open scoped NNReal
set_option backward.isDefEq.respectTransparency false

theorem finish_valid {n : ℕ} {D : Input n} (r : Ready D) (extra : ℕ) (state : Ledger)
    {core : EncodedRoundingRepetition.Result r.chain.size × Ledger}
    (hc : core ∈ ((EncodedRoundingRepetition.run
      (StatefulWeightedQuery.sample r.chain.size r.chain.cutoff r.cutoff_positive)
      r.chain.data.adjacency r.cutoff_positive extra).run state).support) :
    IsIntegralCut D.graph (selectedSet (finish r core.1).mask)
      (thresholdDemands D.graph D.weight) := by
  let : NeZero r.chain.cutoff := ⟨r.cutoff_positive.ne'⟩
  have hs := StatefulOutputShape.selected_shape
    (StatefulWeightedQuery.sample r.chain.size r.chain.cutoff r.cutoff_positive)
    r.chain.data.adjacency r.cutoff_positive extra state hc
  have hv := StatefulRoundingCertificate.run_valid
    (StatefulBoundedRoundingQuality.canonicalFuel r.chain.size)
    r.chain.cutoff.bits (BinaryArithmetic.value_bits r.chain.cutoff)
    r.chain.data.adjacency r.cutoff_positive extra state hc
  apply r.pullback_valid core.1.selected.flags
  have he : selectedSet core.1.selected.flags = core.1.selected.vertices.toFinset := hs.2.symm
  rw [he]
  exact hv

theorem ready_valid {n : ℕ} {D : Input n} (r : Ready D) (extra : ℕ) (state : Ledger)
    {out : EncodedWeightedVertexQuery.Output n × Ledger}
    (hout : out ∈ ((runReady StatefulWeightedQuery.sample r extra).run state).support) :
    IsIntegralCut D.graph (selectedSet out.1.mask) (thresholdDemands D.graph D.weight) := by
  change out ∈ (PMF.bind _ _).support at hout
  obtain ⟨core,hcore,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  have he := (PMF.mem_support_pure_iff _ _).mp hout
  subst out
  exact finish_valid r extra state hcore

theorem weighted_valid {n : ℕ} (D : Input n) (extra : ℕ) (state : Ledger)
    {out : EncodedWeightedVertexQuery.Output n × Ledger}
    (hout : out ∈ ((run StatefulWeightedQuery.sample D extra).run state).support) :
    IsIntegralCut D.graph (selectedSet out.1.mask) (thresholdDemands D.graph D.weight) := by
  unfold run at hout
  cases h : prepare D with
  | inl done =>
    rw [h] at hout
    have he := (PMF.mem_support_pure_iff _ _).mp hout
    subst out
    exact done.valid
  | inr r =>
    rw [h] at hout
    exact ready_valid r extra state hout

theorem heavy_finish_valid {n : ℕ} (D : Input n)
    (inner : EncodedWeightedVertexQuery.Output (StatefulHeavyQuery.residual D).size)
    (hi : IsIntegralCut (StatefulHeavyQuery.residual D).data.graph (selectedSet inner.mask)
      (thresholdDemands (StatefulHeavyQuery.residual D).data.graph
        (StatefulHeavyQuery.residual D).data.weight)) :
    IsIntegralCut D.graph
      (selectedSet (StatefulHeavyQuery.finish (EncodedHeavyVertexPreparation.prepare D) inner).mask)
      (thresholdDemands D.graph D.weight) :=
  EncodedHeavyVertexPreparation.combinedMask_correct D (EncodedCubeRootThreshold.threshold n)
    (EncodedCubeRootThreshold.threshold_le_quarter n) inner.mask hi

/-- Every returned mask is an original valid cut, including bounded-rejection
fallbacks and the deterministic empty-residual branch. -/
theorem heavy_valid {n : ℕ} (D : Input n) (extra : ℕ) (state : Ledger)
    {out : EncodedWeightedVertexQuery.Output n × Ledger}
    (hout : out ∈ ((StatefulHeavyQuery.run D extra).run state).support) :
    IsIntegralCut D.graph (selectedSet out.1.mask) (thresholdDemands D.graph D.weight) := by
  by_cases hz : (StatefulHeavyQuery.residual D).size=0
  · have he : (StatefulHeavyQuery.run D extra).run state = PMF.pure
        (StatefulHeavyQuery.finish (EncodedHeavyVertexPreparation.prepare D)
          (StatefulHeavyQuery.emptyOutput (StatefulHeavyQuery.residual D).size),state) := by
      simp only [StatefulHeavyQuery.run,hz,ite_true]
      rfl
    rw [he] at hout
    have ho := (PMF.mem_support_pure_iff _ _).mp hout
    subst out
    apply heavy_finish_valid
    intro s
    have hs := s.isLt
    omega
  · have he : (StatefulHeavyQuery.run D extra).run state =
        (((run StatefulWeightedQuery.sample (StatefulHeavyQuery.residual D).data extra).run state).map
          (fun inner => (StatefulHeavyQuery.finish (EncodedHeavyVertexPreparation.prepare D) inner.1,inner.2))) := by
      simp only [StatefulHeavyQuery.run,hz,ite_false]
      rfl
    rw [he] at hout
    obtain ⟨inner,hi,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
    exact heavy_finish_valid D inner.1 (weighted_valid _ extra state hi)

end
end DirectedFlowCutGap.StatefulHeavyValidity
