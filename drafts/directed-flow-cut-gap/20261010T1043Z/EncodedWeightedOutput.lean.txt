import DirectedFlowCutGap.EncodedWeightedEnvelope

/-!
# Composition of retained weighted-reduction output masks

The executable pullback consumes already retained preparation, replication,
size, and chain records. It neither rebuilds the transformed graph nor invokes
an implicit clone enumeration. Uniform chains use the any-copy mask; parallel
replication then uses full fibers; permanent ports finally map to original
cores. The concrete factor is twelve. The heavy wrapper adds the proved
`4*ceilCube n` charge and doubles the remaining factor.

These are selected-output and declared word-operation statements. The integer
rounding program, its probability law, and the common storage/address-bit
accounting are joined separately.
-/
namespace DirectedFlowCutGap.EncodedWeightedOutput

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped BigOperators NNReal
open RawNonnegativeRational EncodedUnitCostReplication EncodedWeightedEnvelope

/-- Actual retained records are arguments, so this function performs only
output scans and the erased size cast. -/
def pullback {n : ℕ} (P : EncodedUnitCostPreparation.Prepared n)
    (k : Vector ℕ P.size) (R : Replica k)
    (S : EncodedInputSizing.SizedInput (cloneList k).length)
    {q : Vector ℕ (3*S.size)} (U : EncodedUniformChain.Chain q)
    (selected : Vector Bool U.size) : Vector Bool n :=
  P.pullbackSample k R (S.restoreMask (EncodedUniformOutput.originalMask U selected))

/-- Every constituent's existing scan charge is included once. -/
def pullbackWithCost {n : ℕ} (P : EncodedUnitCostPreparation.Prepared n)
    (k : Vector ℕ P.size) (R : Replica k)
    (S : EncodedInputSizing.SizedInput (cloneList k).length)
    {q : Vector ℕ (3*S.size)} (U : EncodedUniformChain.Chain q)
    (selected : Vector Bool U.size) : Vector Bool n × ℕ :=
  let uniform := EncodedUniformOutput.originalMaskWithCost U selected
  let restored := S.restoreMaskWithCost uniform.1
  let original := P.pullbackSampleWithCost k R restored.1
  (original.1,uniform.2+restored.2+original.2+8)

@[simp] theorem pullbackWithCost_value {n : ℕ}
    (P : EncodedUnitCostPreparation.Prepared n) (k : Vector ℕ P.size) (R : Replica k)
    (S : EncodedInputSizing.SizedInput (cloneList k).length)
    {q : Vector ℕ (3*S.size)} (U : EncodedUniformChain.Chain q)
    (selected : Vector Bool U.size) :
    (pullbackWithCost P k R S U selected).1 = pullback P k R S U selected := rfl

/-- The specialization used in statements; callers retain these records and
pass them to `pullback` rather than evaluating this expression repeatedly. -/
abbrev originalMask {n : ℕ} (D : Input n) (selected : Vector Bool (expanded D).size) :
    Vector Bool n :=
  pullback (prepared D) (prepared D).data.counts (replicated D) (retained D) (expanded D) selected

private theorem restored_card {m : ℕ} (S : EncodedInputSizing.SizedInput m)
    (selected : Vector Bool S.size) :
    (selectedSet (S.restoreMask selected)).card = (selectedSet selected).card := by
  rcases S with ⟨N,hN,data,work⟩
  subst N
  rfl

private theorem restored_replica_cut {m : ℕ} {k : Vector ℕ m} (R : Replica k)
    (selected : Vector Bool (EncodedInputSizing.retainReplica R).size)
    (h : IsIntegralCut (EncodedInputSizing.retainReplica R).data.graph (selectedSet selected)
      (thresholdDemands (EncodedInputSizing.retainReplica R).data.graph
        (EncodedInputSizing.retainReplica R).data.weight)) :
    IsIntegralCut R.input.graph
      (selectedSet ((EncodedInputSizing.retainReplica R).restoreMask selected))
      (thresholdDemands R.input.graph R.input.weight) :=
  EncodedInputSizing.retain_cut R.input selected h

/-- Any actual integer-threshold cut pulls through the complete chain of
retained arrays to an original threshold cut. No size assumption is needed. -/
theorem originalMask_correct {n : ℕ} (D : Input n)
    (hU : EncodedUniformWeightParameters.nontrivial (retained D).data=true)
    (selected : Vector Bool (expanded D).size)
    (hcut : IsIntegralCut (expanded D).data.graph (selectedSet selected)
      (CandidateSchedule.unweightedDemands (expanded D).data.graph ((expanded D).cutoff : ℝ≥0) :
        Set (Fin (expanded D).size × Fin (expanded D).size))) :
    IsIntegralCut D.graph (selectedSet (originalMask D selected))
      (thresholdDemands D.graph D.weight) := by
  have hu := EncodedUniformOutput.integer_cut_correct (retained D).data hU selected hcut
  have hs := EncodedUniformOutput.originalMask_correct (retained D).data
    (uniform_positive (retained D).data hU) selected hu
  have hr := restored_replica_cut (replicated D) _ hs
  have hp := fullFiberCut_actual_correct (prepared D).data (prepared D).data.counts
    (Input.counts_pos (prepared D).data) _ hr
  exact EncodedUnitCostPreparation.pullbackCut_correct D _ hp

/-- Factor twelve for the original cost. The hypotheses refer to the actual
integer graph and its exact retained uniform weight, with no parameter
monotonicity assumption. -/
theorem originalMask_cost_le {n : ℕ} (D : Input n)
    (hC : (prepared D).data.totals.objective.num≠0)
    (hU : EncodedUniformWeightParameters.nontrivial (retained D).data=true)
    (α : ℝ≥0) (selected : Vector Bool (expanded D).size)
    (hcut : IsIntegralCut (expanded D).data.graph (selectedSet selected)
      (CandidateSchedule.unweightedDemands (expanded D).data.graph ((expanded D).cutoff : ℝ≥0) :
        Set (Fin (expanded D).size × Fin (expanded D).size)))
    (hsize : ((selectedSet selected).card : ℝ≥0) ≤ α*totalWeight (expanded D).data.weight) :
    cutCost D.cost (selectedSet (originalMask D selected)) ≤
      12*α*weightedCost D.cost D.weight := by
  obtain ⟨hs,hcard⟩ := EncodedUniformOutput.integer_original_output_spec
    (retained D).data hU α selected hcut hsize
  have hr := restored_replica_cut (replicated D) _ hs
  have hcard' : ((selectedSet ((retained D).restoreMask
      (EncodedUniformOutput.originalMask (expanded D) selected))).card : ℝ≥0) ≤
      (2*α)*totalWeight (replicated D).input.weight := by
    rw [restored_card]
    change ((selectedSet (EncodedUniformOutput.originalMask (expanded D) selected)).card : ℝ≥0) ≤
      (2*α)*totalWeight (retained D).data.weight at hcard
    rw [retained_mass_eq D] at hcard
    exact hcard
  have h := EncodedUnitCostPreparation.sampled_original_output_spec D hC (2*α)
    ((retained D).restoreMask (EncodedUniformOutput.originalMask (expanded D) selected)) hr hcard'
  have hc := h.2
  change cutCost D.cost (selectedSet (originalMask D selected)) ≤ _ at hc
  nlinarith [hc]

/-- The core can use its integer normalized mass `N/L` directly. -/
theorem originalMask_integer_cost_le {n : ℕ} (D : Input n)
    (hC : (prepared D).data.totals.objective.num≠0)
    (hU : EncodedUniformWeightParameters.nontrivial (retained D).data=true)
    (α : ℝ≥0) (selected : Vector Bool (expanded D).size)
    (hcut : IsIntegralCut (expanded D).data.graph (selectedSet selected)
      (CandidateSchedule.unweightedDemands (expanded D).data.graph ((expanded D).cutoff : ℝ≥0) :
        Set (Fin (expanded D).size × Fin (expanded D).size)))
    (hsize : ((selectedSet selected).card : ℝ≥0) ≤
      α*((expanded D).size : ℝ≥0)/(expanded D).cutoff) :
    cutCost D.cost (selectedSet (originalMask D selected)) ≤
      12*α*weightedCost D.cost D.weight := by
  apply originalMask_cost_le D hC hU α selected hcut
  calc
    _ ≤ α*((expanded D).size : ℝ≥0)/(expanded D).cutoff := hsize
    _ = α*(((expanded D).size : ℝ≥0)/(expanded D).cutoff) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integer_mass_le_uniform (retained D).data hU) zero_le

/-- The mass-restricted finite envelope is fixed before choosing the costs. -/
theorem originalMask_envelope_cost_le {n : ℕ} (D : Input n) (hn : 0<n)
    (hC : (prepared D).data.totals.objective.num≠0)
    (hU : EncodedUniformWeightParameters.nontrivial (retained D).data=true)
    (α : ℕ → ℕ → ℝ≥0) (selected : Vector Bool (expanded D).size)
    (hcut : IsIntegralCut (expanded D).data.graph (selectedSet selected)
      (CandidateSchedule.unweightedDemands (expanded D).data.graph ((expanded D).cutoff : ℝ≥0) :
        Set (Fin (expanded D).size × Fin (expanded D).size)))
    (hsize : ((selectedSet selected).card : ℝ≥0) ≤
      α (expanded D).size (expanded D).cutoff * ((expanded D).size : ℝ≥0)/(expanded D).cutoff) :
    cutCost D.cost (selectedSet (originalMask D selected)) ≤
      12*factor α n (6*totalWeight D.weight)*weightedCost D.cost D.weight := by
  exact (originalMask_integer_cost_le D hC hU _ selected hcut hsize).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mass_sensitive_factor D hn hC hU α) zero_le) zero_le)

/-- A polynomial scan bound in original n, retaining both transformed sizes
instead of silently executing a type-index expression to recover them. -/
theorem pullback_work_bound {n : ℕ} (D : Input n) (hn : 0<n)
    (hC : (prepared D).data.totals.objective.num≠0)
    (hU : EncodedUniformWeightParameters.nontrivial (retained D).data=true)
    (selected : Vector Bool (expanded D).size) :
    (pullbackWithCost (prepared D) (prepared D).data.counts (replicated D)
      (retained D) (expanded D) selected).2 ≤
      1920*n^4+108*n^3+1012*n^2+122*n+59 := by
  have hu := EncodedUniformOutput.computed_originalMask_work (retained D).data
    (uniform_positive (retained D).data hU) selected
  have hs := retained_size D hn hC
  have hsq := Nat.mul_le_mul hs hs
  have hp := EncodedUnitCostPreparation.pullbackSample_work_bound D hn hC
    ((retained D).restoreMask (EncodedUniformOutput.originalMask (expanded D) selected))
  change (EncodedUniformOutput.originalMaskWithCost (expanded D) selected).2+3+
    ((prepared D).pullbackSampleWithCost (prepared D).data.counts (replicated D)
      ((retained D).restoreMask (EncodedUniformOutput.originalMask (expanded D) selected))).2+8 ≤ _
  nlinarith

/-- Actual heavy-mask union after the weighted/uniform pullback. -/
abbrev heavyOriginalMask {n : ℕ} (D : Input n)
    (selected : Vector Bool (expanded (heavy D).data).size) : Vector Bool n :=
  EncodedHeavyVertexPreparation.combinedMask (heavy D) (originalMask (heavy D).data selected)

theorem heavyOriginalMask_spec {n : ℕ} (D : Input n)
    (hC : (prepared (heavy D).data).data.totals.objective.num≠0)
    (hU : EncodedUniformWeightParameters.nontrivial (retained (heavy D).data).data=true)
    (α : ℝ≥0) (selected : Vector Bool (expanded (heavy D).data).size)
    (hcut : IsIntegralCut (expanded (heavy D).data).data.graph (selectedSet selected)
      (CandidateSchedule.unweightedDemands (expanded (heavy D).data).data.graph
        ((expanded (heavy D).data).cutoff : ℝ≥0) :
        Set (Fin (expanded (heavy D).data).size × Fin (expanded (heavy D).data).size)))
    (hsize : ((selectedSet selected).card : ℝ≥0) ≤
      α*((expanded (heavy D).data).size : ℝ≥0)/(expanded (heavy D).data).cutoff) :
    IsIntegralCut D.graph (selectedSet (heavyOriginalMask D selected))
      (thresholdDemands D.graph D.weight) ∧
      cutCost D.cost (selectedSet (heavyOriginalMask D selected)) ≤
        (4*(EncodedCubeRootThreshold.ceilCube n : ℝ≥0)+24*α)*weightedCost D.cost D.weight := by
  have hi := originalMask_correct (heavy D).data hU selected hcut
  have hc := originalMask_integer_cost_le (heavy D).data hC hU α selected hcut hsize
  have h := EncodedHeavyVertexPreparation.proxy_output_spec D (12*α)
    (originalMask (heavy D).data selected) hi hc
  refine ⟨h.1,?_⟩
  have he : 4*(EncodedCubeRootThreshold.ceilCube n : ℝ≥0)+2*(12*α) =
      4*(EncodedCubeRootThreshold.ceilCube n : ℝ≥0)+24*α := by ring
  simpa only [he] using h.2

end DirectedFlowCutGap.EncodedWeightedOutput
