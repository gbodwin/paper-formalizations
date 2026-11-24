import DirectedFlowCutGap.RationalEdgeSparsityCode
import DirectedFlowCutGap.EncodedAmplification

/-! Repeat the finite sparsest-edge round and keep the returned cut with
the smallest exact sparsity. The bounded tree consumes literal fair bits. -/
namespace DirectedFlowCutGap.AmplifiedSparsestEdgeTape

open scoped NNReal NNRat ENNReal
open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open ConcurrentEdgeOracle (Edge)
open RationalSparsestEdgeRound (Mask Result scaled tree drawBound widthBound demandSet)
open RationalSparsestEdgeThreshold (choose)
open RationalEdgeSparsityCode (score)
open FiniteDrawTrees (ideal Within)
open FiniteAmplification (probability expectedCost)

variable {m n : ℕ}

attribute [local irreducible] EncodedEdgeGadget.build in
set_option maxHeartbeats 1000000 in
theorem base_bounds (D : EncodedEdgeGadget.Input n) (mode : ChargedVertexModes.Mode) :
    Within (drawBound n) (tree D mode) ∧ LazyFairBitTrees.WidthsLE (widthBound n) (tree D mode) := by
  let g := EncodedEdgeGadget.build D
  have size : g.size ≤ BinaryEdgeGadget.dimension n := by
    have h := BinaryEdgeGadget.size_le D
    rw [BinaryEdgeGadget.build_value] at h
    exact h
  have draws : EncodedUniformRounding.drawBound (4*g.size^2) ≤ drawBound n := by
    unfold drawBound EncodedUniformRounding.drawBound
    gcongr
  have widths : EncodedWeightedRounding.drawWidth g.size ≤ widthBound n :=
    EncodedWeightedRounding.drawWidth_mono size
  cases mode
  · exact ⟨FiniteDrawTrees.within_mono (FiniteDrawTrees.within_map
      (EncodedWeightedRounding.tree_within g.data) _) draws,
      EncodedUniformRounding.widths_weaken
        (LazyFairBitTrees.widths_map (EncodedWeightedRounding.tree_widths g.data) _) widths⟩
  · exact ⟨FiniteDrawTrees.within_mono (FiniteDrawTrees.within_map
      (EncodedSizeRounding.tree_within g.data) _) draws,
      EncodedUniformRounding.widths_weaken
        (LazyFairBitTrees.widths_map (EncodedSizeRounding.tree_widths g.data) _) widths⟩

def budget (n extra confidence : ℕ) : ℕ :=
  let Q := (extra+1)*drawBound n
  Q * FairBitConfidence.trials Q confidence * widthBound n

theorem polynomial_budget (n extra confidence : ℕ) :
    let replicas := 4*(BinaryEdgeGadget.dimension n)^2
    let Q := (extra+1)*drawBound n
    budget n extra confidence ≤ Q*(Q+1+confidence)*((6*replicas)^2+3*replicas+1) := by
  dsimp only
  unfold budget widthBound EncodedWeightedRounding.drawWidth RetainedDrawTrees.sampleWidth FairBitWords.width
  have logarithm := Nat.log_le_self 2
    (max ((6 * (4 * (BinaryEdgeGadget.dimension n)^2))^2) (3 * (4 * (BinaryEdgeGadget.dimension n)^2)))
  have widths :
      (max (6*(4*(BinaryEdgeGadget.dimension n)^2)*(6*(4*(BinaryEdgeGadget.dimension n)^2)))
        (3*(4*(BinaryEdgeGadget.dimension n)^2))).log2+1 ≤
      (6*(4*(BinaryEdgeGadget.dimension n)^2))^2+3*(4*(BinaryEdgeGadget.dimension n)^2)+1 := by
    rw [← pow_two,Nat.log2_eq_log_two]
    exact Nat.add_le_add_right (logarithm.trans (max_le (Nat.le_add_right ..) (Nat.le_add_left ..))) _
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (FairBitConfidence.trials_le ..)) widths

def program (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (D : EncodedEdgeGadget.Input n) (mode : ChargedVertexModes.Mode) (extra confidence : ℕ) :
    FiniteDrawTrees.Tree (Mask n) :=
  EncodedAmplification.bitTree (score A c P) (tree D mode) (drawBound n) extra confidence

def round (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (D : EncodedEdgeGadget.Input n) (mode : ChargedVertexModes.Mode) (extra confidence : ℕ)
    (bits : Bits) : Option (Mask n × Bits) :=
  (EncodedSolverBits.run (program A c P D mode extra confidence) bits).map
    fun (mask,(rest,_)) => (mask,rest)

theorem binary (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (D : EncodedEdgeGadget.Input n) (mode : ChargedVertexModes.Mode) (extra confidence : ℕ) :
    LazyFairBitTrees.Binary (program A c P D mode extra confidence) :=
  EncodedAmplification.bitTree_binary ..

theorem within (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (D : EncodedEdgeGadget.Input n) (mode : ChargedVertexModes.Mode) (extra confidence : ℕ) :
    Within (budget n extra confidence) (program A c P D mode extra confidence) :=
  EncodedAmplification.bitTree_within _ _ _ _ _ _
    (base_bounds D mode).1 (base_bounds D mode).2

theorem complete (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (D : EncodedEdgeGadget.Input n) (mode : ChargedVertexModes.Mode) (extra confidence : ℕ) (bits : Bits)
    (enough : budget n extra confidence ≤ bits.length) :
    ∃ mask used, round A c P D mode extra confidence bits = some (mask,bits.drop used) ∧
      used ≤ budget n extra confidence := by
  obtain ⟨mask,used,found,paid⟩ := EncodedSolverBits.complete (within A c P D mode extra confidence)
    (binary A c P D mode extra confidence) bits enough
  exact ⟨mask,used,by rw [round,found]; rfl,paid⟩

theorem fairTape (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (D : EncodedEdgeGadget.Input n) (mode : ChargedVertexModes.Mode) (extra confidence : ℕ) :
    (EncodedSolverBits.fairTape (budget n extra confidence)).map
      (fun bits => (round A c P D mode extra confidence bits).map Prod.fst) =
        (ideal (program A c P D mode extra confidence)).map some := by
  simp only [round, Option.map_map, Function.comp_def]
  exact EncodedSolverBits.run_fairTape (within A c P D mode extra confidence)
    (binary A c P D mode extra confidence)

section Proof

local instance maskFintype (n : ℕ) : Fintype (Mask n) :=
  let _ : Fintype (RetainedGridState.Flags n) := EncodedUniformRounding.flagsFintype n
  Fintype.ofEquiv (Fin n → RetainedGridState.Flags n)
    { toFun := Vector.ofFn, invFun := Vector.get
      left_inv := by intro f; funext i; exact Vector.getElem_ofFn i.isLt
      right_inv := by intro v; apply Vector.ext; intro i hi; exact Vector.getElem_ofFn hi }

theorem supported (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (D : EncodedEdgeGadget.Input n) (mode : ChargedVertexModes.Mode) (extra confidence : ℕ)
    {bits rest : Bits} {mask : Mask n} (ran : round A c P D mode extra confidence bits = some (mask,rest)) :
    mask ∈ (ideal (tree D mode)).support := by
  unfold round at ran
  obtain ⟨⟨out,receipt⟩,found,same⟩ := Option.map_eq_some_iff.mp ran
  have equal : out = mask := congrArg Prod.fst same
  subst out
  apply EncodedAmplification.support_selected (score A c P) (tree D mode) (drawBound n) extra confidence
  exact EncodedSolverBits.run_support (binary A c P D mode extra confidence) found

noncomputable section

theorem failure (A : Adjacency n) (c w : Weights n) (P : Vector (Edge n) m) (τ : ℚ≥0)
    (distinct : Function.Injective fun j : Fin m => P[j.val])
    (mode : ChargedVertexModes.Mode) (extra confidence : ℕ) (B : ℝ) (Bpos : 0 < B)
    (expect : RationalSparsestEdgeExpectation.expectedSparsity (scaled A w c τ) (demandSet P) mode ≤ B) :
    let D := scaled A w c τ
    probability ((EncodedSolverBits.fairTape (budget n extra confidence)).map
      (fun bits => (round A c P D mode extra confidence bits).map Prod.fst))
      (RationalSparsestFairTape.bad D (demandSet P) (2*B)) ≤
        ((1 : ℝ)/2)^(extra+1)+((1 : ℝ)/2)^confidence := by
  let D := scaled A w c τ
  have cost (mask : Mask n) :
      (score A c P mask).realValue =
        SparsestEdgeBridge.sparsity D.graph D.cost (demandSet P) (EncodedEdgeRounding.selectedEdges mask) := by
    simp only [D, RationalSparsestEdgeRound.scaled_graph, RationalSparsestEdgeRound.scaled_price,
      RationalEdgeSparsityCode.score_eq A c P _ distinct]
  have expected : expectedCost (ideal (tree D mode)) (fun mask => ((score A c P mask).realValue : ℝ)) ≤ B := by
    unfold RationalSparsestEdgeExpectation.expectedSparsity RationalSparsestEdgeExpectation.law at expect
    rw [FiniteAmplification.expectedCost_map] at expect
    simp only [cost]
    exact expect
  have h := EncodedAmplification.failure_le (score A c P) (tree D mode)
    (drawBound n) extra confidence (base_bounds D mode).1 B Bpos expected
  dsimp only
  rw [fairTape]
  unfold probability at h ⊢
  rw [PMF.toOuterMeasure_map_apply]
  refine Eq.trans_le ?_ h
  congr 2
  ext mask
  change RationalSparsestFairTape.bad D (demandSet P) (2*B) (some mask) ↔ 2*B < ((score A c P mask).realValue : ℝ)
  rw [cost]
  constructor
  · rintro ⟨x,same,paid⟩
    obtain rfl := Option.some.inj same
    exact paid
  · exact fun paid => ⟨mask,rfl,paid⟩

end
end Proof
end DirectedFlowCutGap.AmplifiedSparsestEdgeTape
