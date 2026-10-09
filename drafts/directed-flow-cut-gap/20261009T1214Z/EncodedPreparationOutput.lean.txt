import DirectedFlowCutGap.EncodedUnitCostPreparation

/-!
# Executable original-vertex pullback through retained port labels

Only selected surviving cores are returned. The algorithm scans the actual
retained port vector; the proof-side survivor equivalence and its inverse are
never evaluated. Zero-objective and sampled positive-objective guarantees both
refer to the original input graph and original rational costs.
-/

namespace DirectedFlowCutGap.EncodedUnitCostPreparation

open scoped BigOperators NNReal
open RawNonnegativeRational EncodedUnitCostReplication EncodedPortPreparation

namespace Prepared

def coreScan {n : ℕ} (out : Prepared n) (selected : Vector Bool out.size)
    (v : Fin n) : List (Fin out.size) → Bool × ℕ
  | [] => (false,1)
  | i::is =>
    let r := coreScan out selected v is
    ((selected[i.val] && decide (out.ports[i.val] = encodePort (TerminalPorts.core v))) || r.1,
      r.2+20)

theorem coreScan_value {n : ℕ} (out : Prepared n) (selected : Vector Bool out.size)
    (v : Fin n) (is : List (Fin out.size)) :
    (coreScan out selected v is).1 = true ↔
      ∃ i∈is, selected[i.val] = true ∧ out.ports[i.val] = encodePort (TerminalPorts.core v) := by
  induction is with
  | nil => simp [coreScan]
  | cons i is ih => simp [coreScan,ih,or_and_right,exists_or]

theorem coreScan_work {n : ℕ} (out : Prepared n) (selected : Vector Bool out.size)
    (v : Fin n) (is : List (Fin out.size)) :
    (coreScan out selected v is).2 = 20*is.length+1 := by
  induction is <;> simp [coreScan, *]
  omega

def pullbackMask {n : ℕ} (out : Prepared n) (selected : Vector Bool out.size) : Vector Bool n :=
  let indices := retainedIndices selected
  Vector.ofFn (n := n) fun v => (coreScan out selected v indices).1

/-- All lists are derived from the retained selected-array size. The charge
pays both array reads, port comparison, Boolean operations, recursion/cons
inspection, one shared index-list generation/map and the output-vector loop.
The counter pair itself is ghost instrumentation. -/
def pullbackMaskWithCost {n : ℕ} (out : Prepared n) (selected : Vector Bool out.size) :
    Vector Bool n × ℕ :=
  (pullbackMask out selected,n*(20*selected.toArray.size+20)+14*selected.toArray.size+10)

theorem pullbackMaskWithCost_work {n : ℕ} (out : Prepared n) (selected : Vector Bool out.size) :
    (pullbackMaskWithCost out selected).2 = 20*n*out.size+20*n+14*out.size+10 := by
  simp [pullbackMaskWithCost]
  ring

def pullbackCut {n : ℕ} (out : Prepared n) (selected : Vector Bool out.size) : Finset (Fin n) :=
  selectedSet (pullbackMask out selected)

@[simp] theorem mem_pullbackCut {n : ℕ} (out : Prepared n)
    (selected : Vector Bool out.size) (v : Fin n) :
    v∈pullbackCut out selected ↔
      ∃ i : Fin out.size, selected[i.val] = true ∧
        out.ports[i.val] = encodePort (TerminalPorts.core v) := by
  simp [pullbackCut,selectedSet,pullbackMask,coreScan_value]

/-- `replica` is the retained materialized clone record. Runtime pullback uses
its label vector directly, with no clone-list regeneration. -/
def pullbackSample {n : ℕ} (out : Prepared n) (k : Vector ℕ out.size) (replica : Replica k)
    (selected : Vector Bool (cloneList k).length) : Vector Bool n :=
  out.pullbackMask (fullFiberMask k replica.labels selected)

def pullbackSampleWithCost {n : ℕ} (out : Prepared n) (k : Vector ℕ out.size) (replica : Replica k)
    (selected : Vector Bool (cloneList k).length) : Vector Bool n × ℕ :=
  let full := fullFiberMaskWithCost k replica.labels selected
  let original := out.pullbackMaskWithCost full.1
  (original.1,full.2+original.2+4)

@[simp] theorem pullbackSampleWithCost_value {n : ℕ} (out : Prepared n)
    (k : Vector ℕ out.size) (replica : Replica k) (selected : Vector Bool (cloneList k).length) :
    (out.pullbackSampleWithCost k replica selected).1 = out.pullbackSample k replica selected := rfl

end Prepared

theorem pullback_work_bound {n : ℕ} (D : Input n) (selected : Vector Bool (build D).size) :
    ((build D).pullbackMaskWithCost selected).2 ≤ 60*n^2+62*n+10 := by
  rw [Prepared.pullbackMaskWithCost_work]
  have hs := build_size_le D
  have hm := Nat.mul_le_mul_left (20*n) hs
  nlinarith

theorem pullbackSample_work_bound {n : ℕ} (D : Input n) (hn : 0<n)
    (hC : (build D).data.totals.objective.num ≠ 0)
    (selected : Vector Bool (cloneList (build D).data.counts).length) :
    ((build D).pullbackSampleWithCost (build D).data.counts
      (materialize (build D).data (build D).data.counts) selected).2 ≤
      108*n^3+116*n^2+122*n+24 := by
  have hf := fullFiberMask_work_bound (build D).data n (build_preparedBounds D hn) hC selected
  change (fullFiberMaskWithCost (build D).data.counts
    (materialize (build D).data (build D).data.counts).labels selected).2 ≤
      108*n^3+56*n^2+60*n+10 at hf
  have hp := pullback_work_bound D (fullFiberMask (build D).data.counts
    (materialize (build D).data (build D).data.counts).labels selected)
  change (fullFiberMaskWithCost (build D).data.counts
    (materialize (build D).data (build D).data.counts).labels selected).2+
    ((build D).pullbackMaskWithCost (fullFiberMask (build D).data.counts
      (materialize (build D).data (build D).data.counts).labels selected)).2+4 ≤ _
  omega

private theorem core_label_iff {n : ℕ} (D : Input n) (i : Fin (build D).size) (v : Fin n) :
    (preparedEquiv D i).val = TerminalPorts.core v ↔
      (build D).ports[i.val] = encodePort (TerminalPorts.core v) := by
  rw [preparedEquiv_val]
  constructor
  · intro h
    simpa only [encode_decode] using congrArg encodePort h
  · intro h
    rw [h,decode_encode]

theorem pullbackCut_eq {n : ℕ} (D : Input n) (selected : Vector Bool (build D).size) :
    (build D).pullbackCut selected = UnitCostReduction.pullback D.weight
      ((selectedSet selected).image (preparedEquiv D)) := by
  ext v
  rw [Prepared.mem_pullbackCut,UnitCostReduction.pullback,TerminalPorts.mem_corePreimage]
  constructor
  · rintro ⟨i,hi,hv⟩
    refine Finset.mem_image.mpr ⟨preparedEquiv D i,?_,(core_label_iff D i v).mpr hv⟩
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,rfl⟩
  · intro h
    obtain ⟨a,ha,hv⟩ := Finset.mem_image.mp h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact ⟨i,(Finset.mem_filter.mp hi).2,(core_label_iff D i v).mp hv⟩

theorem pullbackCut_cost {n : ℕ} (D : Input n) (selected : Vector Bool (build D).size) :
    cutCost D.cost ((build D).pullbackCut selected) =
      cutCost (build D).data.cost (selectedSet selected) := by
  rw [pullbackCut_eq,UnitCostReduction.prepared_cutCost]
  unfold cutCost
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i _
    exact (build_cost D i).symm
  · intro a _ b _ he
    exact (preparedEquiv D).injective he

theorem selected_prepared_correct {n : ℕ} (D : Input n)
    (selected : Vector Bool (build D).size)
    (h : IsIntegralCut (build D).data.graph (selectedSet selected)
      (thresholdDemands (build D).data.graph (build D).data.weight)) :
    IsIntegralCut (UnitCostReduction.preparedGraph D.graph D.weight)
      ((selectedSet selected).image (preparedEquiv D))
      (thresholdDemands (UnitCostReduction.preparedGraph D.graph D.weight)
        (UnitCostReduction.preparedWeight D.weight)) := by
  have hadj (a b : UnitCostReduction.PreparedVertex D.weight) :
      (UnitCostReduction.preparedGraph D.graph D.weight).Adj a b ↔
        (build D).data.graph.Adj ((preparedEquiv D).symm a) ((preparedEquiv D).symm b) := by
    simpa only [Equiv.apply_symm_apply] using
      (build_graph D ((preparedEquiv D).symm a) ((preparedEquiv D).symm b)).symm
  have hw : (fun a => (build D).data.weight ((preparedEquiv D).symm a)) =
      UnitCostReduction.preparedWeight D.weight := by
    funext a
    rw [build_weight,Equiv.apply_symm_apply]
  have hr := FiniteGraphRelabeling.threshold_cut_pullback (preparedEquiv D).symm hadj
    (build D).data.weight (selectedSet selected) h
  rw [hw] at hr
  simpa only [Equiv.symm_symm] using hr

/-- A threshold cut of the actual prepared Boolean graph gives a threshold cut
of the original graph, with exactly the original surviving-core cost. -/
theorem pullbackCut_correct {n : ℕ} (D : Input n)
    (selected : Vector Bool (build D).size)
    (h : IsIntegralCut (build D).data.graph (selectedSet selected)
      (thresholdDemands (build D).data.graph (build D).data.weight)) :
    IsIntegralCut D.graph ((build D).pullbackCut selected) (thresholdDemands D.graph D.weight) := by
  rw [pullbackCut_eq]
  apply UnitCostReduction.prepared_integral_pullback
  have hf := UnitCostReduction.prepared_fractional (isFractionalCut_thresholdDemands D.graph D.weight)
  have hi := selected_prepared_correct D selected h
  intro s t hst
  exact hi s t (hf s t hst)

theorem zero_output_spec {n : ℕ} (D : Input n)
    (hz : (build D).data.totals.objective.num = 0) :
    IsIntegralCut D.graph ((build D).pullbackCut (build D).data.zeroMask)
      (thresholdDemands D.graph D.weight) ∧
      cutCost D.cost ((build D).pullbackCut (build D).data.zeroMask) = 0 := by
  obtain ⟨hi,hc⟩ := (build D).data.zeroCut_correct hz
  refine ⟨pullbackCut_correct D _ hi,?_⟩
  rw [pullbackCut_cost]
  exact hc

/-- Factor six for the actual original mask: factor three in the normalized
unit-cost replica, followed by the prepared objective's factor two. The sampled
cut hypotheses concern the actual materialized array graph and weights. -/
theorem sampled_original_output_spec {n : ℕ} (D : Input n)
    (hC : (build D).data.totals.objective.num ≠ 0) (α : ℝ≥0)
    (selected : Vector Bool (cloneList (build D).data.counts).length)
    (hcut : IsIntegralCut (materialize (build D).data (build D).data.counts).input.graph
      (selectedSet selected)
      (thresholdDemands (materialize (build D).data (build D).data.counts).input.graph
        (materialize (build D).data (build D).data.counts).input.weight))
    (hsize : ((selectedSet selected).card : ℝ≥0) ≤
      α*totalWeight (materialize (build D).data (build D).data.counts).input.weight) :
    let result := (build D).pullbackSample (build D).data.counts
      (materialize (build D).data (build D).data.counts) selected
    IsIntegralCut D.graph (selectedSet result) (thresholdDemands D.graph D.weight) ∧
      cutCost D.cost (selectedSet result) ≤ 6*α*weightedCost D.cost D.weight := by
  obtain ⟨hi,hc⟩ := (build D).data.sampled_output_spec hC α selected hcut hsize
  change IsIntegralCut D.graph
    ((build D).pullbackCut (fullFiberMask (build D).data.counts
      (labelVector (build D).data.counts) selected)) (thresholdDemands D.graph D.weight) ∧ _
  refine ⟨pullbackCut_correct D _ hi,?_⟩
  change cutCost D.cost ((build D).pullbackCut (fullFiberMask (build D).data.counts
    (labelVector (build D).data.counts) selected)) ≤ _
  rw [pullbackCut_cost]
  have hp := build_weightedCost_le_double D
  calc
    _ ≤ 3*α*weightedCost (build D).data.cost (build D).data.weight := hc
    _ ≤ 3*α*(2*weightedCost D.cost D.weight) := mul_le_mul_of_nonneg_left hp zero_le
    _ = _ := by ring

end DirectedFlowCutGap.EncodedUnitCostPreparation
