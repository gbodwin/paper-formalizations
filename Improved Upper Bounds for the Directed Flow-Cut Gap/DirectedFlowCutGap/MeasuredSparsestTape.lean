import DirectedFlowCutGap.MeasuredCutSparsity
import DirectedFlowCutGap.MeasuredTapeSelection
import DirectedFlowCutGap.MeasuredTapeTrials
import DirectedFlowCutGap.AmplifiedSparsestEdgeTape
import DirectedFlowCutGap.AmplifiedSparsestVertexTape
import DirectedFlowCutGap.BinaryEdgeProjection

/-! Run the paid rounding attempts on the original literal tape and compare
the exact sparsity scores once all attempts have returned. -/
namespace DirectedFlowCutGap.MeasuredSparsestTape

open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency)
open BinaryRational (StoredBounded)
open ConcurrentEdgeOracle (Edge)
open ConcurrentEdgeCoverWidths (MatrixFits)
open RationalEdgeThresholds (Weights)
open RationalSparsestEdgeRound (Mask)
open RetainedGridState (Flags)
open ChargedVertexModes (Mode)
open PhysicalCoverAccess (Read)
open Polynomial

variable {n m : ℕ}

private def vertexSample (D : EncodedUnitCostReplication.Input n) (mode : Mode)
    (trials : ℕ) (bits : Bits) : Read ((Flags n × ℕ) × Bits) :=
  let round := PaidVertexRounding.runner mode trials D bits
  (round.1.map fun result => ((result.mask,result.paid),result.suffix),round.2)

private theorem vertexSample_value (D : EncodedUnitCostReplication.Input n) (mode : Mode)
    (trials : ℕ) (bits : Bits) :
    (vertexSample D mode trials bits).1.map (fun ((a,_),rest) => (a,rest)) =
      LiteralTapeComposition.execute trials (RationalSparsestVertexRound.tree D mode) bits := by
  rw [← RationalSparsestVertexRound.round_reference]
  simp only [vertexSample,RationalSparsestVertexRound.round,Option.map_map,Function.comp_def]
  rfl

noncomputable def sampleBudget (p : Polynomial ℕ) (n B trials : ℕ) : ℕ :=
  PhysicalVertexRoundingCost.sizeBudget p n trials+PhysicalBinaryVertexRounding.sizeBudget n B

private theorem sampleBudget_mono (p : Polynomial ℕ) {n N B : ℕ} (smaller : n ≤ N) (trials : ℕ) :
    sampleBudget p n B trials ≤ sampleBudget p N B trials := by
  have legacy := PhysicalVertexRoundingCost.weightedBudget_mono p smaller trials
  have binary := PhysicalBinaryVertexRounding.sizeBudget_mono smaller (Nat.le_refl B)
  unfold sampleBudget
  apply Nat.add_le_add _ binary
  unfold PhysicalVertexRoundingCost.sizeBudget
  gcongr

attribute [local irreducible] PaidVertexRounding.size PaidVertexRounding.weighted
  PhysicalVertexRoundingCost.sizeBudget PhysicalBinaryVertexRounding.sizeBudget in
private theorem runner_paid (p : Polynomial ℕ) (cutoff : ∀ n L T, GuardedCutoffWork.budget n L T ≤ p.eval (n+T))
    (D : EncodedUnitCostReplication.Input n) {B : ℕ} (fits : VertexReductionWidths.InputFits D B)
    (mode : Mode) (trials : ℕ) (bits : Bits) :
    (PaidVertexRounding.runner mode trials D bits).2 ≤ sampleBudget p n B trials := by
  cases mode with
  | mass =>
    have legacy : PhysicalVertexRoundingCost.weightedBudget p n trials ≤
        PhysicalVertexRoundingCost.sizeBudget p n trials := by
      unfold PhysicalVertexRoundingCost.sizeBudget
      exact Nat.le_add_left ..
    have binary : PhysicalBinaryVertexRounding.weightedBudget n B ≤ PhysicalBinaryVertexRounding.sizeBudget n B :=
      (PhysicalBinaryVertexRounding.weightedBudget_mono (Nat.le_refl _) (Nat.le_succ _)).trans (by
        unfold PhysicalBinaryVertexRounding.sizeBudget
        exact Nat.le_add_left ..)
    exact (PaidVertexRounding.weighted_paid p cutoff trials D fits bits).trans (Nat.add_le_add legacy binary)
  | size =>
    simpa only [PaidVertexRounding.runner,sampleBudget] using PaidVertexRounding.size_paid p cutoff trials D fits bits

def vertexTrials (n extra confidence : ℕ) : ℕ :=
  FairBitConfidence.trials ((extra+1)*RationalSparsestVertexRound.drawBound n) confidence

def vertex (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) (D : EncodedUnitCostReplication.Input n) (mode : Mode)
    (extra confidence : ℕ) (bits : Bits) : Read (Flags n × Bits) :=
  let trials := MeasuredTapeTrials.prepare (RationalSparsestVertexRound.drawBound n) extra confidence
  let result := MeasuredTapeSelection.run (vertexSample D mode trials.1)
    (MeasuredCutSparsity.vertexScore A c P) extra bits
  (result.1,trials.2+result.2)

theorem vertex_value (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) (D : EncodedUnitCostReplication.Input n) (mode : Mode)
    (extra confidence : ℕ) (bits : Bits) :
    (vertex A c P D mode extra confidence bits).1 =
      AmplifiedSparsestVertexTape.round A c P D mode extra confidence bits := by
  simp only [vertex,MeasuredTapeTrials.prepare_value]
  exact MeasuredTapeSelection.run_value _ _ (RationalVertexSparsityCode.score A c P)
    (MeasuredCutSparsity.vertexScore_value A c P) (RationalSparsestVertexRound.tree D mode)
    (vertexTrials n extra confidence) extra (vertexSample_value D mode _) bits

noncomputable def vertexWork (p : Polynomial ℕ) (n m B width extra confidence : ℕ) : ℕ :=
  MeasuredTapeTrials.work (RationalSparsestVertexRound.drawBound n) extra confidence+
    (MeasuredTapeSelection.sampleWork (extra+1) (sampleBudget p n width (vertexTrials n extra confidence))+
      MeasuredTapeSelection.work extra (MeasuredCutSparsity.vertexPriceWidth n B+m.size)
        (MeasuredCutSparsity.vertexWork n m B))

theorem vertex_charge (p : Polynomial ℕ) (cutoff : ∀ n L T, GuardedCutoffWork.budget n L T ≤ p.eval (n+T))
    (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) (D : EncodedUnitCostReplication.Input n) (mode : Mode)
    (extra confidence : ℕ) (bits : Bits) {B width : ℕ} (fits : ∀ i, StoredBounded (c.get i) B)
    (roundFits : VertexReductionWidths.InputFits D width) :
    (vertex A c P D mode extra confidence bits).2 ≤ vertexWork p n m B width extra confidence := by
  have paid := MeasuredTapeTrials.prepare_charge (RationalSparsestVertexRound.drawBound n) extra confidence
  have sampled := MeasuredTapeSelection.run_charge (vertexSample D mode (vertexTrials n extra confidence))
    (MeasuredCutSparsity.vertexScore A c P) extra bits
    (fun tape => runner_paid p cutoff D roundFits mode _ tape)
    (fun cut => MeasuredCutSparsity.vertexScore_bounds A c P cut fits)
  simpa only [vertex,vertexWork,MeasuredTapeTrials.prepare_value,vertexTrials] using Nat.add_le_add paid sampled

private def edgeSample {D : EncodedEdgeGadget.Input n} (gadget : EncodedEdgeGadget.Prepared D)
    (mode : Mode) (trials : ℕ) (bits : Bits) : Read ((Mask n × ℕ) × Bits) :=
  let round := PaidVertexRounding.runner mode trials gadget.data bits
  match round.1 with
  | none => (none,round.2)
  | some result =>
    let projected := BinaryEdgeProjection.originalMask gadget result.mask
    (some ((projected.1,result.paid),result.suffix),round.2+projected.2)

attribute [local irreducible] PaidVertexRounding.runner BinaryEdgeGadget.build in
private theorem edgeSample_value (D : EncodedEdgeGadget.Input n) (mode : Mode) (trials : ℕ) (bits : Bits) :
    (edgeSample (BinaryEdgeGadget.build D).1 mode trials bits).1.map (fun ((a,_),rest) => (a,rest)) =
      LiteralTapeComposition.execute trials (RationalSparsestEdgeRound.tree D mode) bits := by
  rw [← RationalSparsestEdgeRound.round_reference]
  let g := (BinaryEdgeGadget.build D).1
  change (edgeSample g mode trials bits).1.map (fun ((a,_),rest) => (a,rest)) =
    (PaidVertexRounding.runner mode trials g.data bits).1.map
      (fun result => (EncodedEdgeRounding.pullback g result.mask,result.suffix))
  cases h : (PaidVertexRounding.runner mode trials g.data bits).1 with
  | none => simp only [edgeSample,h,Option.map_none]
  | some r => simp only [edgeSample,h,Option.map_some,BinaryEdgeProjection.originalMask_value]

private def projectionBudget (n N : ℕ) : ℕ :=
  BinaryEdgeProjection.pullbackBudget n N+BinaryEdgeProjection.pullbackControlBudget n N

private theorem projectionBudget_mono (n : ℕ) {N M : ℕ} (size : N ≤ M) :
    projectionBudget n N ≤ projectionBudget n M := by
  have a : BinaryEdgeProjection.maskBudget n N ≤ BinaryEdgeProjection.maskBudget n M := by
    unfold BinaryEdgeProjection.maskBudget
    gcongr
  exact Nat.add_le_add (Nat.add_le_add_right a _)
    (BinaryEdgeProjection.pullbackControlBudget_mono (Nat.le_refl n) size)

attribute [local irreducible] PaidVertexRounding.runner BinaryEdgeProjection.originalMask in
private theorem edgeSample_paid (p : Polynomial ℕ)
    (cutoff : ∀ n L T, GuardedCutoffWork.budget n L T ≤ p.eval (n+T))
    {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D) {B N : ℕ}
    (fits : VertexReductionWidths.InputFits g.data B) (size : g.size ≤ N)
    (mode : Mode) (trials : ℕ) (bits : Bits) :
    (edgeSample g mode trials bits).2 ≤ sampleBudget p N B trials+projectionBudget n N := by
  have paid := (runner_paid p cutoff g.data fits mode trials bits).trans (sampleBudget_mono p size trials)
  cases h : (PaidVertexRounding.runner mode trials g.data bits).1 with
  | none =>
    simpa only [edgeSample,h] using paid.trans (Nat.le_add_right _ (projectionBudget n N))
  | some result =>
    have projected := (BinaryEdgeProjection.originalMask_paid g result.mask).trans (projectionBudget_mono n size)
    simpa only [edgeSample,h] using Nat.add_le_add paid projected

def edgeTrials (n extra confidence : ℕ) : ℕ :=
  FairBitConfidence.trials ((extra+1)*RationalSparsestEdgeRound.drawBound n) confidence

def edge (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) (D : EncodedEdgeGadget.Input n)
    (mode : Mode) (extra confidence : ℕ) (bits : Bits) : Read (Mask n × Bits) :=
  let built := BinaryEdgeGadget.buildWithControl D
  let trials := MeasuredTapeTrials.prepare (RationalSparsestEdgeRound.drawBound n) extra confidence
  let result := MeasuredTapeSelection.run (edgeSample built.1.1 mode trials.1)
    (MeasuredCutSparsity.edgeScore A c P) extra bits
  (result.1,built.1.2+built.2+(trials.2+result.2))

attribute [local irreducible] BinaryEdgeGadget.buildWithControl BinaryEdgeGadget.build in
theorem edge_value (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) (D : EncodedEdgeGadget.Input n)
    (mode : Mode) (extra confidence : ℕ) (bits : Bits) :
    (edge A c P D mode extra confidence bits).1 =
      AmplifiedSparsestEdgeTape.round A c P D mode extra confidence bits := by
  simp only [edge,BinaryEdgeGadget.build_control_projection,MeasuredTapeTrials.prepare_value]
  exact MeasuredTapeSelection.run_value _ _ (RationalEdgeSparsityCode.score A c P)
    (MeasuredCutSparsity.edgeScore_value A c P) (RationalSparsestEdgeRound.tree D mode)
    (edgeTrials n extra confidence) extra (edgeSample_value D mode _) bits

noncomputable def edgeWork (p : Polynomial ℕ) (n m B width extra confidence : ℕ) : ℕ :=
  let size := BinaryEdgeGadget.dimension n
  let reducedWidth := n^2*(width+1)+n+1
  let cap := sampleBudget p size reducedWidth (edgeTrials n extra confidence)+projectionBudget n size
  BinaryEdgeGadget.budget n width+BinaryEdgeGadget.controlBudget n width+
    (MeasuredTapeTrials.work (RationalSparsestEdgeRound.drawBound n) extra confidence+
      (MeasuredTapeSelection.sampleWork (extra+1) cap+MeasuredTapeSelection.work extra
        (MeasuredCutSparsity.edgePriceWidth n B+m.size) (MeasuredCutSparsity.edgeWork n m B)))

attribute [local irreducible] BinaryEdgeGadget.buildWithControl BinaryEdgeGadget.build in
theorem edge_charge (p : Polynomial ℕ) (cutoff : ∀ n L T, GuardedCutoffWork.budget n L T ≤ p.eval (n+T))
    (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) (D : EncodedEdgeGadget.Input n)
    (mode : Mode) (extra confidence : ℕ) (bits : Bits) {B width : ℕ} (fits : MatrixFits c B)
    (roundFits : BinaryEdgeGadget.InputFits D width) :
    (edge A c P D mode extra confidence bits).2 ≤ edgeWork p n m B width extra confidence := by
  let g := (BinaryEdgeGadget.buildWithControl D).1.1
  have equal : (BinaryEdgeGadget.buildWithControl D).1 = BinaryEdgeGadget.build D :=
    BinaryEdgeGadget.build_control_projection D
  have shape : g = (BinaryEdgeGadget.build D).1 := congrArg Prod.fst equal
  have fields : VertexReductionWidths.InputFits g.data (n^2*(width+1)+n+1) := by
    rw [shape]
    exact BinaryEdgeGadget.fields_fit D roundFits
  have size : g.size ≤ BinaryEdgeGadget.dimension n := by
    rw [shape]
    exact BinaryEdgeGadget.size_le D
  have built : (BinaryEdgeGadget.buildWithControl D).1.2 ≤ BinaryEdgeGadget.budget n width := by
    rw [equal]
    exact BinaryEdgeGadget.build_paid D roundFits
  have control := BinaryEdgeGadget.build_control_paid D roundFits
  have trials := MeasuredTapeTrials.prepare_charge (RationalSparsestEdgeRound.drawBound n) extra confidence
  have scored := MeasuredTapeSelection.run_charge (edgeSample g mode (edgeTrials n extra confidence))
    (MeasuredCutSparsity.edgeScore A c P) extra bits
    (edgeSample_paid p cutoff g fields size mode _)
    (fun cut => MeasuredCutSparsity.edgeScore_bounds A c P cut fits)
  simpa only [edge,edgeWork,MeasuredTapeTrials.prepare_value,edgeTrials,g] using
    Nat.add_le_add (Nat.add_le_add built control) (Nat.add_le_add trials scored)

end DirectedFlowCutGap.MeasuredSparsestTape
