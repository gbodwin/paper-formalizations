import DirectedFlowCutGap.EncodedUnitCostReplication
import DirectedFlowCutGap.FiniteGraphRelabeling

/-!
# Pulling back a sampled cut of the actual encoded clone graph

The hypothesis concerns the retained Boolean matrix and rational arrays indexed
by `Fin`, not an abstract construction graph. Relabeling is used only in proofs;
the returned Boolean mask is the full-fiber scan through retained labels.
-/

namespace DirectedFlowCutGap.EncodedUnitCostReplication

open scoped BigOperators NNReal

def Replica.input {m : ℕ} {k : Vector ℕ m} (out : Replica k) :
    Input (cloneList k).length := ⟨out.adjacency,out.weights,out.costs⟩

def selectedSet {N : ℕ} (selected : Vector Bool N) : Finset (Fin N) :=
  Finset.univ.filter fun i => selected[i.val] = true

theorem selectedClones_eq_image {m : ℕ} (k : Vector ℕ m)
    (selected : Vector Bool (cloneList k).length) :
    selectedClones k selected = (selectedSet selected).image (cloneEquiv k) := rfl

theorem selectedClones_card {m : ℕ} (k : Vector ℕ m)
    (selected : Vector Bool (cloneList k).length) :
    (selectedClones k selected).card = (selectedSet selected).card := by
  rw [selectedClones_eq_image]
  exact Finset.card_image_of_injective _ (cloneEquiv k).injective

theorem actual_graph_adj {m : ℕ} (D : Input m) (k : Vector ℕ m)
    (i j : Fin (cloneList k).length) :
    (materialize D k).input.graph.Adj i j ↔
      (VertexReplication.graph D.graph (fun v => k[v.val])).Adj
        ((cloneEquiv k) i) ((cloneEquiv k) j) :=
  materialize_graph_refines D k i j

theorem actual_weight {m : ℕ} (D : Input m) (k : Vector ℕ m)
    (i : Fin (cloneList k).length) :
    (materialize D k).input.weight i =
      VertexReplication.weight (fun v => k[v.val]) D.weight ((cloneEquiv k) i) :=
  materialize_weight_refines D k i

theorem actual_totalWeight {m : ℕ} (D : Input m) (k : Vector ℕ m) :
    totalWeight (materialize D k).input.weight =
      totalWeight (VertexReplication.weight (fun v => k[v.val]) D.weight) := by
  unfold totalWeight
  simp_rw [actual_weight]
  exact (cloneEquiv k).sum_comp _

/-- Relabel the actual sampled Boolean cut to the mathematical clone type.
The reverse of the indexing equivalence is used only in this proof. -/
theorem selectedClones_correct {m : ℕ} (D : Input m) (k : Vector ℕ m)
    (selected : Vector Bool (cloneList k).length)
    (h : IsIntegralCut (materialize D k).input.graph (selectedSet selected)
      (thresholdDemands (materialize D k).input.graph (materialize D k).input.weight)) :
    IsIntegralCut (VertexReplication.graph D.graph (fun v => k[v.val]))
      (selectedClones k selected)
      (thresholdDemands (VertexReplication.graph D.graph (fun v => k[v.val]))
        (VertexReplication.weight (fun v => k[v.val]) D.weight)) := by
  have hadj (a b : Clone k) :
      (VertexReplication.graph D.graph (fun v => k[v.val])).Adj a b ↔
        (materialize D k).input.graph.Adj ((cloneEquiv k).symm a) ((cloneEquiv k).symm b) := by
    simpa only [Equiv.apply_symm_apply] using
      (actual_graph_adj D k ((cloneEquiv k).symm a) ((cloneEquiv k).symm b)).symm
  have hw : (fun a => (materialize D k).input.weight ((cloneEquiv k).symm a)) =
      VertexReplication.weight (fun v => k[v.val]) D.weight := by
    funext a
    rw [actual_weight,Equiv.apply_symm_apply]
  have hr := FiniteGraphRelabeling.threshold_cut_pullback (cloneEquiv k).symm hadj
    (materialize D k).input.weight (selectedSet selected) h
  rw [hw] at hr
  simpa only [Equiv.symm_symm,← selectedClones_eq_image] using hr

theorem fullFiberCut_actual_correct {m : ℕ} (D : Input m) (k : Vector ℕ m)
    (hk : ∀ v : Fin m, 0 < k[v.val])
    (selected : Vector Bool (cloneList k).length)
    (h : IsIntegralCut (materialize D k).input.graph (selectedSet selected)
      (thresholdDemands (materialize D k).input.graph (materialize D k).input.weight)) :
    IsIntegralCut D.graph (fullFiberCut k selected) (thresholdDemands D.graph D.weight) :=
  fullFiberCut_correct D k hk selected (selectedClones_correct D k selected h)

namespace Input
variable {m : ℕ}

abbrev counts (D : Input m) : Vector ℕ m := copyCounts (D.normalized D.totals)

theorem counts_pos (D : Input m) (v : Fin m) : 0 < D.counts[v.val] := by
  simp only [counts,copyCounts,Vector.getElem_ofFn]
  omega

theorem actual_normalized_totalWeight (D : Input m) :
    totalWeight (materialize D D.counts).input.weight =
      totalWeight (UnitCostReduction.replicatedWeight D.cost D.weight) := by
  rw [actual_totalWeight,VertexReplication.totalWeight_weight]
  unfold UnitCostReduction.replicatedWeight
  rw [VertexReplication.totalWeight_weight]
  apply Finset.sum_congr rfl
  intro v _
  rw [D.copyCounts_eq]

/-- The exact normalization cancellation for the actual sampled mask. -/
theorem fullFiberCut_cost (D : Input m) (hC : D.totals.objective.num ≠ 0)
    (α : ℝ≥0) (selected : Vector Bool (cloneList D.counts).length)
    (hsize : ((selectedSet selected).card : ℝ≥0) ≤
      α*totalWeight (materialize D D.counts).input.weight) :
    cutCost D.cost (fullFiberCut D.counts selected) ≤ 3*α*weightedCost D.cost D.weight := by
  have hpos : 0 < weightedCost D.cost D.weight := by
    rw [← D.totals_objective]
    change (0 : ℝ≥0) < (D.totals.objective.value : ℝ≥0)
    exact_mod_cast (RawNonnegativeRational.Code.value_pos _).mpr (Nat.pos_of_ne_zero hC)
  have hcost := VertexReplication.cutCost_fullFibers_le_card
    (UnitCostReduction.normalizedCost D.cost D.weight)
    (fun v => show UnitCostReduction.normalizedCost D.cost D.weight v ≤
        (D.counts[v.val] : ℝ≥0) from by
      rw [D.copyCounts_eq]
      exact UnitCostReduction.cost_le_copies _ v)
    (selectedClones D.counts selected)
  have he : cutCost (UnitCostReduction.normalizedCost D.cost D.weight)
      (VertexReplication.fullFibers (selectedClones D.counts selected)) =
      UnitCostReduction.scale D.cost D.weight *
        cutCost D.cost (fullFiberCut D.counts selected) := by
    rw [fullFiberCut_eq]
    simp only [cutCost,UnitCostReduction.normalizedCost,Finset.mul_sum]
  rw [he,selectedClones_card] at hcost
  refine le_of_mul_le_mul_left ?_ (UnitCostReduction.scale_pos D.cost D.weight hpos)
  calc
    _ ≤ ((selectedSet selected).card : ℝ≥0) := hcost
    _ ≤ α*totalWeight (materialize D D.counts).input.weight := hsize
    _ = α*totalWeight (UnitCostReduction.replicatedWeight D.cost D.weight) := by
      rw [actual_normalized_totalWeight]
    _ ≤ α*(3*(UnitCostReduction.scale D.cost D.weight*weightedCost D.cost D.weight)) :=
      mul_le_mul_of_nonneg_left (UnitCostReduction.normalized_copied_weight_le _ _ hpos) zero_le
    _ = _ := by ring

/-- A valid bounded-size cut from the actual indexed output yields the actual
full-fiber mask, with the prepared problem's factor-three cost guarantee. -/
theorem sampled_output_spec (D : Input m) (hC : D.totals.objective.num ≠ 0)
    (α : ℝ≥0) (selected : Vector Bool (cloneList D.counts).length)
    (hcut : IsIntegralCut (materialize D D.counts).input.graph (selectedSet selected)
      (thresholdDemands (materialize D D.counts).input.graph
        (materialize D D.counts).input.weight))
    (hsize : ((selectedSet selected).card : ℝ≥0) ≤
      α*totalWeight (materialize D D.counts).input.weight) :
    IsIntegralCut D.graph (fullFiberCut D.counts selected) (thresholdDemands D.graph D.weight) ∧
      cutCost D.cost (fullFiberCut D.counts selected) ≤ 3*α*weightedCost D.cost D.weight :=
  ⟨fullFiberCut_actual_correct D D.counts D.counts_pos selected hcut,
    D.fullFiberCut_cost hC α selected hsize⟩

end Input
end DirectedFlowCutGap.EncodedUnitCostReplication
