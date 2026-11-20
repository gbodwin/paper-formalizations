import DirectedFlowCutGap.RationalSparsestEdgeThreshold
import DirectedFlowCutGap.PaidDirectEdgeWire

/-! Compose threshold selection with the existing literal-tape edge rounding
on the supplied rational lengths and prices. -/
namespace DirectedFlowCutGap.RationalSparsestEdgeRound

open scoped BigOperators NNRat NNReal ENNReal
open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open RationalSparsestEdgeThreshold (actualDistance choose)
open RawNonnegativeRational (Code)
open EncodedEdgeRounding (selectedEdges)
open FiniteDrawTrees (ideal)
open RetainedGridState (Flags)

def scaled {n : ℕ} (A : Adjacency n) (w c : Weights n) (τ : ℚ≥0) : EncodedEdgeGadget.Input n :=
  let threshold := Code.ofNNRat τ
  ⟨A,w.map (fun row => row.map fun q => (BinaryRational.decode q).div threshold),
    c.map (fun row => row.map BinaryRational.decode)⟩

theorem scaled_graph {n : ℕ} (A : Adjacency n) (w c : Weights n) (τ : ℚ≥0) :
    (scaled A w c τ).graph=graph A := rfl

theorem scaled_weight {n : ℕ} (A : Adjacency n) (w c : Weights n) (τ : ℚ≥0) :
    (scaled A w c τ).weight=fun e => weights w e / (τ : ℝ≥0) := by
  funext e
  simp only [scaled,EncodedEdgeGadget.Input.weight,Vector.getElem_map,weights,RationalEdgeThresholds.cost,
    BinaryFractionalWalkOracle.decodeCost,Code.realValue,Code.value_div,Code.value_ofNNRat,NNRat.cast_div]

theorem scaled_price {n : ℕ} (A : Adjacency n) (w c : Weights n) (τ : ℚ≥0) :
    (scaled A w c τ).cost=weights c := by
  funext e
  simp only [scaled,EncodedEdgeGadget.Input.cost,Vector.getElem_map,weights,RationalEdgeThresholds.cost,
    BinaryFractionalWalkOracle.decodeCost,Code.realValue]

theorem threshold_demand {m n : ℕ} (A : Adjacency n) (w c : Weights n)
    (pairs : Vector (Fin n × Fin n) m) {i : Fin m} {τ : ℚ≥0}
    (found : choose A w pairs=.threshold i τ) (j : Fin m) :
    pairs[j.val] ∈ edgeThresholdDemands (scaled A w c τ).graph (scaled A w c τ).weight ↔
      (τ : ℝ≥0) ≤ actualDistance A w pairs j := by
  have spec := RationalSparsestEdgeThreshold.choose_spec A w pairs
  rw [found] at spec
  obtain ⟨finite,_,positive,_,_⟩ := spec
  have pos : (0 : ℝ≥0)<(τ : ℝ≥0) := by exact_mod_cast positive
  rw [scaled_graph,scaled_weight,SparsestEdgeBridge.mem_scaled_threshold _ _ _ pos]
  change (τ : ℝ≥0∞)≤edgeDistance (graph A) (weights w) pairs[j.val].1 pairs[j.val].2 ↔ _
  have represented : ((actualDistance A w pairs j : ℝ≥0) : ℝ≥0∞)=
      edgeDistance (graph A) (weights w) pairs[j.val].1 pairs[j.val].2 :=
    ENNReal.coe_toNNReal (finite j)
  rw [← represented]
  exact (ENNReal.coe_le_coe : (((τ : ℝ≥0) : ℝ≥0∞) ≤
    (actualDistance A w pairs j : ℝ≥0∞)) ↔ (τ : ℝ≥0) ≤ actualDistance A w pairs j)

abbrev Mask (n : ℕ) := Vector (Flags n) n

def round {n : ℕ} (D : EncodedEdgeGadget.Input n) (mode : ChargedVertexModes.Mode)
    (T : ℕ) (tape : Bits) : Option (Mask n × Bits) :=
  let gadget := (BinaryEdgeGadget.build D).1
  let result := PaidVertexRounding.runner mode T gadget.data tape
  result.1.map fun cut => (EncodedEdgeRounding.pullback gadget cut.mask,cut.suffix)

def tree {n : ℕ} (D : EncodedEdgeGadget.Input n) (mode : ChargedVertexModes.Mode) : FiniteDrawTrees.Tree (Mask n) :=
  EncodedEdgeRounding.tree D (fun m => ChargedVertexModes.round m mode)

theorem round_reference {n : ℕ} (D : EncodedEdgeGadget.Input n) (mode : ChargedVertexModes.Mode)
    (T : ℕ) (tape : Bits) :
    round D mode T tape=LiteralTapeComposition.execute T (tree D mode) tape := by
  unfold round
  dsimp only
  rw [PaidVertexRounding.runner_value]
  let gadget := (BinaryEdgeGadget.build D).1
  have reference := PhysicalAmplifiedBinaryVertex.runner_observe mode T gadget.data tape
  have same := congrArg (Option.map fun (flags,rest) => (EncodedEdgeRounding.pullback gadget flags,rest)) reference
  rw [← LiteralTapeComposition.execute_map] at same
  simp only [Option.map_map,Function.comp_def,PhysicalIntegerRounding.Result.observe] at same
  refine same.trans ?_
  rw [show gadget=EncodedEdgeGadget.build D from BinaryEdgeGadget.build_value D]
  rfl

theorem round_valid {n : ℕ} (D : EncodedEdgeGadget.Input n) (mode : ChargedVertexModes.Mode)
    (T : ℕ) {tape rest : Bits} {mask : Mask n}
    (ran : round D mode T tape=some (mask,rest)) :
    selectedEdges mask ⊆ graphEdges D.graph ∧
      IsIntegralEdgeCut D.graph (selectedEdges mask) (edgeThresholdDemands D.graph D.weight) := by
  rw [round_reference,LiteralTapeComposition.execute] at ran
  let binary := LazyFairBitTrees.lower T (tree D mode)
  change (EncodedSolverBits.run binary tape).map _=some (mask,rest) at ran
  cases h : EncodedSolverBits.run binary tape with
  | none => rw [h] at ran; cases ran
  | some result =>
    rcases result with ⟨output,tail,used⟩
    have equal : output=mask := by
      rw [h,Option.map_some] at ran
      exact congrArg Prod.fst (Option.some.inj ran)
    subst output
    have supported := EncodedSolverBits.run_support (LazyFairBitTrees.lower_binary T (tree D mode)) h
    cases mode
    · exact EncodedEdgeRounding.massBit_support_valid T D supported
    · exact EncodedEdgeRounding.sizeBit_support_valid T D supported

def drawBound (n : ℕ) : ℕ := EncodedUniformRounding.drawBound (4*(BinaryEdgeGadget.dimension n)^2)

def widthBound (n : ℕ) : ℕ := EncodedWeightedRounding.drawWidth (BinaryEdgeGadget.dimension n)

def tapeBudget (n T : ℕ) : ℕ := drawBound n*T*widthBound n

attribute [local irreducible] EncodedEdgeGadget.build in
set_option maxHeartbeats 1000000 in
private theorem tree_bounds {n : ℕ} (D : EncodedEdgeGadget.Input n) (mode : ChargedVertexModes.Mode) :
    FiniteDrawTrees.Within (drawBound n) (tree D mode) ∧
      LazyFairBitTrees.WidthsLE (widthBound n) (tree D mode) := by
  let g := EncodedEdgeGadget.build D
  have size : g.size≤BinaryEdgeGadget.dimension n := by
    have h := BinaryEdgeGadget.size_le D
    rw [BinaryEdgeGadget.build_value] at h
    exact h
  have draws : EncodedUniformRounding.drawBound (4*g.size^2)≤drawBound n := by
    unfold drawBound EncodedUniformRounding.drawBound
    gcongr
  have widths : EncodedWeightedRounding.drawWidth g.size≤widthBound n :=
    EncodedWeightedRounding.drawWidth_mono size
  cases mode with
  | mass =>
    exact ⟨FiniteDrawTrees.within_mono (FiniteDrawTrees.within_map
      (EncodedWeightedRounding.tree_within g.data) _) draws,
      EncodedUniformRounding.widths_weaken
        (LazyFairBitTrees.widths_map (EncodedWeightedRounding.tree_widths g.data) _) widths⟩
  | size =>
    exact ⟨FiniteDrawTrees.within_mono (FiniteDrawTrees.within_map
      (EncodedSizeRounding.tree_within g.data) _) draws,
      EncodedUniformRounding.widths_weaken
        (LazyFairBitTrees.widths_map (EncodedSizeRounding.tree_widths g.data) _) widths⟩

theorem round_fairTape {n : ℕ} (D : EncodedEdgeGadget.Input n) (mode : ChargedVertexModes.Mode) (T : ℕ) :
    (EncodedSolverBits.fairTape (tapeBudget n T)).map (fun tape => (round D mode T tape).map Prod.fst)=
      (ideal (LazyFairBitTrees.lower T (tree D mode))).map some := by
  obtain ⟨length,width⟩ := tree_bounds D mode
  have binary := LazyFairBitTrees.lower_binary T (tree D mode)
  have bound : FiniteDrawTrees.Within (tapeBudget n T) (LazyFairBitTrees.lower T (tree D mode)) :=
    LazyFairBitTrees.lower_within length width T
  simp only [round_reference,LiteralTapeComposition.execute,Option.map_map,Function.comp_def]
  exact EncodedSolverBits.run_fairTape bound binary

theorem round_complete {n : ℕ} (D : EncodedEdgeGadget.Input n) (mode : ChargedVertexModes.Mode)
    (T : ℕ) (tape : Bits) (enough : tapeBudget n T≤tape.length) :
    ∃ mask used, round D mode T tape=some (mask,tape.drop used) ∧ used≤tapeBudget n T := by
  obtain ⟨length,width⟩ := tree_bounds D mode
  have binary := LazyFairBitTrees.lower_binary T (tree D mode)
  have bound : FiniteDrawTrees.Within (tapeBudget n T) (LazyFairBitTrees.lower T (tree D mode)) :=
    LazyFairBitTrees.lower_within length width T
  obtain ⟨mask,used,found,within⟩ := EncodedSolverBits.complete bound binary tape enough
  exact ⟨mask,used,by rw [round_reference,LiteralTapeComposition.execute,found]; rfl,within⟩

inductive Result (n : ℕ) where
  | zeroDistance
  | cut (mask : Mask n) (suffix : Bits)

def run {m n : ℕ} (A : Adjacency n) (w c : Weights n) (pairs : Vector (Fin n × Fin n) m)
    (mode : ChargedVertexModes.Mode) (T : ℕ) (tape : Bits) : Option (Result n) :=
  match choose A w pairs with
  | .unreachable _ => some (.cut (Vector.replicate n (Vector.replicate n false)) tape)
  | .zero => some .zeroDistance
  | .threshold _ τ => (round (scaled A w c τ) mode T tape).map (fun (mask,rest) => .cut mask rest)

def demandSet {m n : ℕ} (pairs : Vector (Fin n × Fin n) m) : Finset (Fin n × Fin n) :=
  Finset.univ.image fun i : Fin m => pairs[i.val]

private theorem demanded {m n : ℕ} (pairs : Vector (Fin n × Fin n) m) (i : Fin m) :
    pairs[i.val]∈demandSet pairs :=
  Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

private theorem qualifies {m n : ℕ} (A : Adjacency n) (w c : Weights n)
    (pairs : Vector (Fin n × Fin n) m) {i : Fin m} {τ : ℚ≥0} {X : Finset (Fin n × Fin n)}
    (found : choose A w pairs=.threshold i τ)
    (valid : IsIntegralEdgeCut (scaled A w c τ).graph X
      (edgeThresholdDemands (scaled A w c τ).graph (scaled A w c τ).weight))
    (j : Fin m) (above : (τ : ℝ≥0) ≤ actualDistance A w pairs j) :
    (⟨pairs[j.val],demanded pairs j⟩ : demandSet pairs) ∈ SparsestEdgeBridge.separated (graph A) (demandSet pairs) X := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  have job := (threshold_demand A w c pairs found j).mpr above
  exact valid pairs[j.val].1 pairs[j.val].2 job

theorem count_le {m n : ℕ} (A : Adjacency n) (w c : Weights n)
    (pairs : Vector (Fin n × Fin n) m) (unique : Function.Injective fun j : Fin m => pairs[j.val])
    {i : Fin m} {τ : ℚ≥0} {X : Finset (Fin n × Fin n)}
    (found : choose A w pairs=.threshold i τ)
    (valid : IsIntegralEdgeCut (scaled A w c τ).graph X
      (edgeThresholdDemands (scaled A w c τ).graph (scaled A w c τ).weight)) :
    (FiniteHarmonicThreshold.above (actualDistance A w pairs) (τ : ℝ≥0)).card ≤
      (SparsestEdgeBridge.separated (graph A) (demandSet pairs) X).card := by
  let includePair (j : Fin m) : demandSet pairs := ⟨pairs[j.val],demanded pairs j⟩
  have injective : Function.Injective includePair := fun _ _ same => unique (congrArg Subtype.val same)
  apply Finset.card_le_card_of_injOn includePair _ injective.injOn
  intro j reached
  exact qualifies A w c pairs found valid j (Finset.mem_filter.mp reached).2

theorem run_cut {m n : ℕ} (A : Adjacency n) (w c : Weights n)
    (pairs : Vector (Fin n × Fin n) m) (mode : ChargedVertexModes.Mode) (T : ℕ)
    {tape rest : Bits} {mask : Mask n}
    (ran : run A w c pairs mode T tape=some (.cut mask rest)) :
    selectedEdges mask ⊆ graphEdges (graph A) ∧
      0<(SparsestEdgeBridge.separated (graph A) (demandSet pairs) (selectedEdges mask)).card := by
  have spec := RationalSparsestEdgeThreshold.choose_spec A w pairs
  unfold run at ran
  cases chosen : choose A w pairs with
  | unreachable i =>
    rw [chosen] at ran spec
    have shape := Option.some.inj ran
    cases shape
    have empty : selectedEdges (Vector.replicate n (Vector.replicate n false))=∅ := by
      ext e
      simp [selectedEdges,RetainedGridState.flag]
    rw [empty]
    exact ⟨Finset.empty_subset _,(SparsestEdgeBridge.unreachable_zero_sparsity (graph A)
      (weights c) (weights w) (demandSet pairs) pairs[i.val] (demanded pairs i) spec).1⟩
  | zero =>
    rw [chosen] at ran
    cases Option.some.inj ran
  | threshold i τ =>
    rw [chosen] at ran spec
    dsimp only at ran spec
    cases solved : round (scaled A w c τ) mode T tape with
    | none => rw [solved] at ran; cases ran
    | some result =>
      obtain ⟨out,suffix⟩ := result
      rw [solved] at ran
      cases Option.some.inj ran
      obtain ⟨arcs,valid⟩ := round_valid _ mode T solved
      refine ⟨arcs,Finset.card_pos.mpr ?_⟩
      obtain ⟨j,reached⟩ := Finset.card_pos.mp spec.2.2.2.1
      exact ⟨⟨pairs[j.val],demanded pairs j⟩,qualifies A w c pairs chosen valid j
        (Finset.mem_filter.mp reached).2⟩

end DirectedFlowCutGap.RationalSparsestEdgeRound
