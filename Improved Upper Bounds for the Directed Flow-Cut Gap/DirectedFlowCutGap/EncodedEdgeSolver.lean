import DirectedFlowCutGap.EncodedEdgeLineInput
import DirectedFlowCutGap.EncodedVertexAmplification

/-!
# Constructive multicut for rational edge costs and ordered demands

The original input determines the fractional covering instance on the
line graph. Each returned rational row feeds the dyadic rounding program
on the original graph. The controller keeps an actual candidate using
the exact original edge costs, then repeats with bounded fair bits.
-/

namespace DirectedFlowCutGap.EncodedEdgeSolver

open scoped NNReal
open EncodedEdgeLineInput RetainedGridState FiniteDrawTrees FiniteAmplification
open FractionalCoverRawCore

attribute [local instance] EncodedUniformRounding.flagsFintype

private def pairFlagsEquiv (n : ℕ) : PairFlags n ≃ (Fin n → Flags n) where
  toFun a i := a[i.val]
  invFun := Vector.ofFn
  left_inv a := by
    apply Vector.ext
    intro i hi
    simp
  right_inv f := by
    funext i
    simp

local instance (n : ℕ) : Fintype (PairFlags n) :=
  Fintype.ofEquiv (Fin n → Flags n) (pairFlagsEquiv n).symm

abbrev Mode := (m : ℕ) → EncodedEdgeRounding.Rounding m
def massMode : Mode := fun _ => EncodedWeightedRounding.tree
def sizeMode : Mode := fun _ => EncodedSizeRounding.tree

inductive Output (n : ℕ) where
  | infeasible (demand : Option (EncodedEdgeGadget.Pair n))
  | cut (mask : PairFlags n)
  | invalid

private def originalDemand {n : ℕ} (d : Fin (lineSize n) × Fin (lineSize n)) :
    Option (EncodedEdgeGadget.Pair n) :=
  match index n d.1, index n d.2 with
  | .inl (s, true), .inl (t, false) => some (s, t)
  | _, _ => none

def outputFor {n : ℕ} (D : Input n) : EncodedVertexSolver.Output (lineSize n) → Output n
  | .infeasible d => .infeasible (originalDemand d)
  | .cut a => .cut (toEdges D a)
  | .invalid => .invalid

def round {n : ℕ} (D : Input n) (mode : Mode) : EncodedVertexSolver.Rounding (lineSize n) :=
  fun r => map toLine (EncodedEdgeRounding.tree (roundingInput D r.weights) mode)

def tree {n : ℕ} (D : Input n) (mode : Mode) : FiniteDrawTrees.Tree (Output n) :=
  map (outputFor D) (EncodedVertexSolver.tree (lineInput D) (round D mode))

def drawBound (n : ℕ) : ℕ :=
  EncodedUniformRounding.drawBound (4 * (2 * n * (Nat.log2 n + 4)) ^ 2)

private theorem round_within {n : ℕ} (D : Input n) (mode : Mode)
    (h : ∀ m (I : EncodedUnitCostReplication.Input m),
      Within (EncodedUniformRounding.drawBound (4 * m ^ 2)) (mode m I))
    (r : EncodedUnitCostReplication.Input (lineSize n)) : Within (drawBound n) (round D mode r) := by
  let I := roundingInput D r.weights
  let g := EncodedEdgeGadget.build I
  have hg := EncodedEdgeGadget.build_size_le I
  apply within_mono (within_map (within_map (h g.size g.data) _) _)
  unfold drawBound EncodedUniformRounding.drawBound
  gcongr

def drawWidth (n : ℕ) : ℕ :=
  EncodedWeightedRounding.drawWidth (2 * n * (Nat.log2 n + 4))

private theorem round_widths {n : ℕ} (D : Input n) (mode : Mode)
    (h : ∀ m (I : EncodedUnitCostReplication.Input m),
      LazyFairBitTrees.WidthsLE (EncodedWeightedRounding.drawWidth m) (mode m I))
    (r : EncodedUnitCostReplication.Input (lineSize n)) :
    LazyFairBitTrees.WidthsLE (drawWidth n) (round D mode r) := by
  let I := roundingInput D r.weights
  let g := EncodedEdgeGadget.build I
  apply EncodedUniformRounding.widths_weaken (LazyFairBitTrees.widths_map
    (LazyFairBitTrees.widths_map (h g.size g.data) _) _)
  exact EncodedWeightedRounding.drawWidth_mono (EncodedEdgeGadget.build_size_le I)

def bitTree {n : ℕ} (κ : ℕ) (D : Input n) (mode : Mode) : FiniteDrawTrees.Tree (Output n) :=
  let e := EncodedVertexAmplification.confidenceExponent n κ
  map (outputFor D)
    (EncodedVertexAmplification.boundedBitTree (drawBound n) e (e + 1) (lineInput D) (round D mode))

theorem bitTree_binary {n : ℕ} (κ : ℕ) (D : Input n) (mode : Mode) :
    LazyFairBitTrees.Binary (bitTree κ D mode) :=
  LazyFairBitTrees.binary_map (EncodedAmplification.bitTree_binary ..) _

theorem bitTree_within {n : ℕ} (κ : ℕ) (D : Input n) (mode : Mode)
    (hmode : ∀ m (I : EncodedUnitCostReplication.Input m),
      Within (EncodedUniformRounding.drawBound (4 * m ^ 2)) (mode m I))
    (hwidth : ∀ m (I : EncodedUnitCostReplication.Input m),
      LazyFairBitTrees.WidthsLE (EncodedWeightedRounding.drawWidth m) (mode m I)) :
    let e := EncodedVertexAmplification.confidenceExponent n κ + 1
    let Q := e * EncodedVertexSolver.drawBound (lineInput D) (drawBound n)
    Within (Q * FairBitConfidence.trials Q e * drawWidth n) (bitTree κ D mode) :=
  within_map
    (EncodedVertexAmplification.boundedBit_within (drawBound n)
      (EncodedVertexAmplification.confidenceExponent n κ)
      (EncodedVertexAmplification.confidenceExponent n κ + 1) (drawWidth n)
      (lineInput D) (round D mode) (round_within D mode hmode) (round_widths D mode hwidth))
    (outputFor D)

def Valid {n : ℕ} (D : Input n) : Output n → Prop
  | .infeasible _ => ¬ ∃ w : EncodedEdgeGadget.Pair n → ℝ≥0,
      IsFractionalEdgeCut D.graph w {d | d ∈ D.demands}
  | .cut a => EncodedEdgeRounding.selectedEdges a ⊆ graphEdges D.graph ∧
      IsIntegralEdgeCut D.graph (EncodedEdgeRounding.selectedEdges a) {d | d ∈ D.demands}
  | .invalid => False

private theorem valid_outputFor {n : ℕ} (D : Input n) (out : EncodedVertexSolver.Output (lineSize n))
    (h : EncodedVertexSolver.Valid (lineInput D) out) : Valid D (outputFor D out) := by
  cases out with
  | infeasible d =>
    rintro ⟨w, hw⟩
    exact h ⟨_, comparator_feasible D w hw⟩
  | cut a =>
    refine ⟨?_, toEdges_cut D a h⟩
    intro e he
    exact (mem_graphEdges _ _).mpr ((toEdges_mem D a e).mp he).1
  | invalid => exact h

private theorem line_support_valid {n : ℕ} (D : Input n) (mode : Mode)
    (hmode : ∀ m (I : EncodedUnitCostReplication.Input m) (a : Flags m),
      a ∈ (ideal (mode m I)).support →
      IsIntegralCut I.graph (cutSet a) (thresholdDemands I.graph I.weight))
    {out : EncodedVertexSolver.Output (lineSize n)}
    (h : out ∈ (ideal (EncodedVertexSolver.tree (lineInput D) (round D mode))).support) :
    EncodedVertexSolver.Valid (lineInput D) out := by
  apply EncodedVertexSolver.support_valid_on_input (lineInput D) (round D mode) _ h
  intro y a ha hf
  simp only [round, ideal, law_map] at ha
  obtain ⟨b, hb, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
  have hf' := (feasible_lineInput D _).mp hf
  have hcut := (EncodedEdgeRounding.support_valid (roundingInput D y) mode
    (fun I _ hI => hmode _ I _ hI) hb).2
  apply toLine_cut D b
  intro s t hst
  apply hcut s t
  rw [show (s, t) ∈ edgeThresholdDemands (roundingInput D y).graph (roundingInput D y).weight ↔
    1 ≤ edgeDistance D.graph (roundingInput D y).weight s t from Iff.rfl, roundingInput_weight]
  exact hf' s t hst

theorem bit_support_valid {n : ℕ} (κ : ℕ) (D : Input n) (mode : Mode)
    (hmode : ∀ m (I : EncodedUnitCostReplication.Input m) (a : Flags m),
      a ∈ (ideal (mode m I)).support →
      IsIntegralCut I.graph (cutSet a) (thresholdDemands I.graph I.weight))
    {out : Output n} (h : out ∈ (ideal (bitTree κ D mode)).support) : Valid D out := by
  simp only [bitTree, ideal, law_map] at h
  obtain ⟨a, ha, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  have hl := EncodedVertexAmplification.boundedBit_support_subset (drawBound n)
    (EncodedVertexAmplification.confidenceExponent n κ)
    (EncodedVertexAmplification.confidenceExponent n κ + 1) (lineInput D) (round D mode) ha
  exact valid_outputFor D a (line_support_valid D mode hmode hl)

theorem mass_support_valid {n : ℕ} (κ : ℕ) (D : Input n) {out : Output n}
    (h : out ∈ (ideal (bitTree κ D massMode)).support) : Valid D out :=
  bit_support_valid κ D massMode (fun _ I _ ha => EncodedWeightedRounding.support_valid I ha) h

theorem size_support_valid {n : ℕ} (κ : ℕ) (D : Input n) {out : Output n}
    (h : out ∈ (ideal (bitTree κ D sizeMode)).support) : Valid D out :=
  bit_support_valid κ D sizeMode (fun _ I _ ha => EncodedSizeRounding.support_valid I ha) h

def outputEdges {n : ℕ} : Output n → Finset (EncodedEdgeGadget.Pair n)
  | .cut a => EncodedEdgeRounding.selectedEdges a
  | .infeasible _ | .invalid => ∅

noncomputable def outputPrice {n : ℕ} (D : Input n) (out : Output n) : ℝ :=
  edgeCutCost D.graph D.cost (outputEdges out)

noncomputable def expectedPrice {n : ℕ} (D : Input n) (mode : Mode) : ℝ :=
  expectedCost ((ideal (tree D mode)).map outputEdges) (fun X => (edgeCutCost D.graph D.cost X : ℝ))

private theorem cutPrice_toEdges {n : ℕ} (D : Input n) (a : Flags (lineSize n)) :
    (edgeCutCost D.graph D.cost (EncodedEdgeRounding.selectedEdges (toEdges D a)) : ℝ) =
      EncodedCutSelection.cutPrice (lineInput D).costs a := by
  exact congrArg (fun v : ℝ≥0 => (v : ℝ)) (toEdges_cost D a)

private theorem outputPrice_for {n : ℕ} (D : Input n) (a : EncodedVertexSolver.Output (lineSize n)) :
    outputPrice D (outputFor D a) = EncodedVertexSolver.outputPrice (lineInput D) a := by
  cases a with
  | cut a => exact cutPrice_toEdges D a
  | infeasible _ | invalid =>
    simp [outputPrice, outputFor, outputEdges, edgeCutCost, EncodedVertexSolver.outputPrice,
      EncodedVertexSolver.outputMask, EncodedCutSelection.optionPrice]

theorem expectedPrice_line {n : ℕ} (D : Input n) (mode : Mode) :
    expectedPrice D mode = EncodedVertexSolver.expectedPrice (lineInput D) (round D mode) := by
  let f : Option (Flags (lineSize n)) → Finset (EncodedEdgeGadget.Pair n) :=
    fun a => a.elim ∅ (fun b => EncodedEdgeRounding.selectedEdges (toEdges D b))
  have he : outputEdges ∘ outputFor D = f ∘ EncodedVertexSolver.outputMask := by
    funext a
    cases a <;> rfl
  simp only [expectedPrice, EncodedVertexSolver.expectedPrice, tree, ideal, law_map, PMF.map_comp, he]
  rw [← PMF.map_comp, expectedCost_map]
  congr 1
  funext a
  cases a with
  | none => simp [f, edgeCutCost, EncodedCutSelection.optionPrice]
  | some a => exact cutPrice_toEdges D a

theorem zero_price_on_support {n : ℕ} (κ : ℕ) (D : Input n) (mode : Mode)
    (hcost : expectedPrice D mode ≤ 0) {out : Output n}
    (hout : out ∈ (ideal (bitTree κ D mode)).support) : outputPrice D out = 0 := by
  simp only [bitTree, ideal, law_map] at hout
  obtain ⟨o, ho, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  rw [outputPrice_for]
  apply EncodedVertexAmplification.bounded_zero_price_on_support (drawBound n) _ _
    (lineInput D) (round D mode) _ ho
  rwa [expectedPrice_line] at hcost

private theorem expected_round {n : ℕ} (D : Input n) (mode : Mode) (y : RawRow (lineSize n)) :
    expectedCost (ideal (round D mode (EncodedVertexSolver.roundingInput (lineInput D) y)))
      (EncodedCutSelection.cutPrice (lineInput D).costs) =
      EncodedEdgeRounding.expectedPrice (roundingInput D y) mode := by
  simp only [round, EncodedVertexSolver.roundingInput, EncodedEdgeRounding.expectedPrice,
    ideal, law_map, expectedCost_map]
  congr 1
  funext a
  exact congrArg (fun v : ℝ≥0 => (v : ℝ)) (toLine_cost D a)

private theorem expected_comparison {n : ℕ} (D : Input n) (mode : Mode)
    (w : EncodedEdgeGadget.Pair n → ℝ≥0) (hw : IsFractionalEdgeCut D.graph w {d | d ∈ D.demands})
    (B : ℝ) (hB : 0 ≤ B)
    (bound : ∀ I : EncodedEdgeGadget.Input n,
      (weightedEdgeCost I.graph I.cost I.weight : ℝ) ≤ 6 * (weightedEdgeCost D.graph D.cost w : ℝ) →
      (totalEdgeWeight I.graph I.weight : ℝ) ≤ 12 * (totalEdgeWeight D.graph w : ℝ) →
      EncodedEdgeRounding.expectedPrice I mode ≤ B) :
    expectedPrice D mode ≤ B := by
  rw [expectedPrice_line]
  apply EncodedVertexSolver.expected_comparison (lineInput D) (round D mode) (comparator D w)
    (comparator_feasible D w hw) B hB
  intro y hy hm
  rw [expected_round]
  apply bound
  · have hcomp : weightedEdgeCost D.graph D.cost (projectWeight (comparator D w)) =
        weightedEdgeCost D.graph D.cost w := by
      unfold weightedEdgeCost
      apply Finset.sum_congr rfl
      intro e he
      rw [projectWeight_comparator, actualEdgeWeight_of_adj _ _ ((mem_graphEdges _ _).mp he)]
    simp only [weightedCost_lineInput, hcomp] at hy
    change (weightedEdgeCost D.graph D.cost (roundingInput D y).weight : ℝ) ≤ _
    have hy' : (EncodedVertexSolver.roundingInput (lineInput D) y).weight =
        (fun i => (get y i).realValue) := by
      funext i
      rfl
    rw [hy'] at hy
    simpa only [roundingInput_weight] using hy
  · have hp := totalEdgeWeight_project_le D (fun i => (get y i).realValue)
    rw [totalWeight_comparator] at hm
    change (totalEdgeWeight D.graph (roundingInput D y).weight : ℝ) ≤ _
    rw [roundingInput_weight]
    exact (NNReal.coe_le_coe.mpr hp).trans hm

theorem size_expected_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
      ∀ (n : ℕ) (D : Input n) (w : EncodedEdgeGadget.Pair n → ℝ≥0),
        IsFractionalEdgeCut D.graph w {d | d ∈ D.demands} →
        expectedPrice D sizeMode ≤
          K * (n : ℝ) ^ (1 / 3 + ε) * (weightedEdgeCost D.graph D.cost w : ℝ) := by
  intro ε hε
  obtain ⟨K, hK, hround⟩ := EncodedEdgeRounding.size_expected_uniform ε hε
  refine ⟨6 * K, by positivity, ?_⟩
  intro n D w hw
  apply expected_comparison D sizeMode w hw _ (by positivity)
  intro I hcost _
  apply (hround n I).trans
  calc
    _ ≤ K * (n : ℝ) ^ (1 / 3 + ε) * (6 * (weightedEdgeCost D.graph D.cost w : ℝ)) :=
      mul_le_mul_of_nonneg_left hcost (by positivity)
    _ = _ := by ring

theorem mass_expected_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
      ∀ (n : ℕ) (D : Input n) (w : EncodedEdgeGadget.Pair n → ℝ≥0),
        IsFractionalEdgeCut D.graph w {d | d ∈ D.demands} →
        expectedPrice D massMode ≤
          K * (n : ℝ) ^ ε * (totalEdgeWeight D.graph w : ℝ) ^ (1 / 2 : ℝ) *
            (weightedEdgeCost D.graph D.cost w : ℝ) := by
  intro ε hε
  obtain ⟨K, hK, hround⟩ := EncodedEdgeRounding.mass_expected_uniform ε hε
  refine ⟨6 * (12 : ℝ) ^ (1 / 2 : ℝ) * K, by positivity, ?_⟩
  intro n D w hw
  apply expected_comparison D massMode w hw _ (by positivity)
  intro I hcost hmass
  apply (hround n I).trans
  have hm : (totalEdgeWeight I.graph I.weight : ℝ) ^ (1 / 2 : ℝ) ≤
      (12 : ℝ) ^ (1 / 2 : ℝ) * (totalEdgeWeight D.graph w : ℝ) ^ (1 / 2 : ℝ) :=
    (Real.rpow_le_rpow (by positivity) hmass (by norm_num)).trans_eq
      (Real.mul_rpow (by norm_num) (by positivity))
  calc
    _ ≤ K * (n : ℝ) ^ ε * ((12 : ℝ) ^ (1 / 2 : ℝ) * (totalEdgeWeight D.graph w : ℝ) ^ (1 / 2 : ℝ)) *
          (6 * (weightedEdgeCost D.graph D.cost w : ℝ)) := by gcongr
    _ = _ := by ring

theorem polynomial_failure_le {n : ℕ} (κ : ℕ) (D : Input n) (mode : Mode)
    (hmode : ∀ m (I : EncodedUnitCostReplication.Input m),
      Within (EncodedUniformRounding.drawBound (4 * m ^ 2)) (mode m I))
    (B : ℝ) (hB : 0 < B) (he : expectedPrice D mode ≤ B) :
    probability (ideal (bitTree κ D mode)) (fun a => 2 * B < outputPrice D a) ≤
      ((max 1 n : ℕ) : ℝ) ^ (-(κ : ℝ)) := by
  let e := EncodedVertexAmplification.confidenceExponent n κ
  let t := EncodedVertexAmplification.boundedBitTree (drawBound n) e (e + 1) (lineInput D) (round D mode)
  have hmap : probability (ideal (bitTree κ D mode)) (fun a => 2 * B < outputPrice D a) =
      probability (ideal t) (fun a => 2 * B < EncodedVertexSolver.outputPrice (lineInput D) a) := by
    have event : (outputFor D) ⁻¹' {a | 2 * B < outputPrice D a} =
        {a | 2 * B < EncodedVertexSolver.outputPrice (lineInput D) a} := by
      ext a
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, outputPrice_for]
    unfold probability
    rw [show ideal (bitTree κ D mode) = (ideal t).map (outputFor D) by
      simp only [bitTree, ideal, law_map, t, e],
      PMF.toOuterMeasure_map_apply, event]
  rw [hmap]
  have h := EncodedVertexAmplification.bounded_failure_le (drawBound n) e (e + 1)
    (lineInput D) (round D mode) (round_within D mode hmode) B hB ((expectedPrice_line D mode) ▸ he)
  calc
    _ ≤ ((1 : ℝ) / 2) ^ (e + 1) + ((1 : ℝ) / 2) ^ (e + 1) := h
    _ = ((1 : ℝ) / 2) ^ e := by rw [pow_succ]; ring
    _ ≤ _ := EncodedVertexAmplification.confidence_power n κ

end DirectedFlowCutGap.EncodedEdgeSolver
