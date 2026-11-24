import DirectedFlowCutGap.RationalVertexSparsityCode
import DirectedFlowCutGap.RationalSparsestVertexFairTape
import DirectedFlowCutGap.EncodedAmplification

/-! Repeat the endpoint-safe vertex round and retain the smallest exact
sparsity on a finite literal tape. -/
namespace DirectedFlowCutGap.AmplifiedSparsestVertexTape

open scoped NNReal NNRat ENNReal
open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency)
open BinaryFractionalRows (Row)
open RetainedGridState (Flags)
open EncodedUnitCostReplication (Input selectedSet)
open RationalSparsestVertexRound (scaled tree drawBound)
open RationalSparsestEdgeRound (demandSet)
open RationalVertexSparsityCode (score)
open FiniteDrawTrees (ideal Within)
open FiniteAmplification (probability expectedCost)

attribute [local instance] EncodedUniformRounding.flagsFintype

variable {m n : ℕ}

theorem base_bounds (D : Input n) (mode : ChargedVertexModes.Mode) :
    Within (drawBound n) (tree D mode) ∧
      LazyFairBitTrees.WidthsLE (EncodedWeightedRounding.drawWidth n) (tree D mode) := by
  cases mode
  · exact ⟨EncodedWeightedRounding.tree_within D,EncodedWeightedRounding.tree_widths D⟩
  · exact ⟨EncodedSizeRounding.tree_within D,EncodedSizeRounding.tree_widths D⟩

def budget (n extra confidence : ℕ) : ℕ :=
  let Q := (extra+1)*drawBound n
  Q * FairBitConfidence.trials Q confidence * EncodedWeightedRounding.drawWidth n

theorem polynomial_budget (n extra confidence : ℕ) :
    let replicas := 4*n^2
    let Q := (extra+1)*drawBound n
    budget n extra confidence ≤ Q*(Q+1+confidence)*((6*replicas)^2+3*replicas+1) := by
  dsimp only
  unfold budget EncodedWeightedRounding.drawWidth RetainedDrawTrees.sampleWidth FairBitWords.width
  have widths :
      (max (6*(4*n^2)*(6*(4*n^2))) (3*(4*n^2))).log2+1 ≤ (6*(4*n^2))^2+3*(4*n^2)+1 := by
    rw [← pow_two,Nat.log2_eq_log_two]
    exact Nat.add_le_add_right ((Nat.log_le_self 2 _).trans
      (max_le (Nat.le_add_right ..) (Nat.le_add_left ..))) _
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (FairBitConfidence.trials_le ..)) widths

def program (A : Adjacency n) (c : Row n) (P : Vector (Fin n × Fin n) m)
    (D : Input n) (mode : ChargedVertexModes.Mode) (extra confidence : ℕ) : FiniteDrawTrees.Tree (Flags n) :=
  EncodedAmplification.bitTree (score A c P) (tree D mode) (drawBound n) extra confidence

def round (A : Adjacency n) (c : Row n) (P : Vector (Fin n × Fin n) m)
    (D : Input n) (mode : ChargedVertexModes.Mode) (extra confidence : ℕ) (bits : Bits) :
    Option (Flags n × Bits) :=
  (EncodedSolverBits.run (program A c P D mode extra confidence) bits).map fun (mask,(rest,_)) => (mask,rest)

theorem binary (A : Adjacency n) (c : Row n) (P : Vector (Fin n × Fin n) m)
    (D : Input n) (mode : ChargedVertexModes.Mode) (extra confidence : ℕ) :
    LazyFairBitTrees.Binary (program A c P D mode extra confidence) :=
  EncodedAmplification.bitTree_binary ..

theorem within (A : Adjacency n) (c : Row n) (P : Vector (Fin n × Fin n) m)
    (D : Input n) (mode : ChargedVertexModes.Mode) (extra confidence : ℕ) :
    Within (budget n extra confidence) (program A c P D mode extra confidence) :=
  EncodedAmplification.bitTree_within _ _ _ _ _ _ (base_bounds D mode).1 (base_bounds D mode).2

theorem complete (A : Adjacency n) (c : Row n) (P : Vector (Fin n × Fin n) m)
    (D : Input n) (mode : ChargedVertexModes.Mode) (extra confidence : ℕ) (bits : Bits)
    (enough : budget n extra confidence ≤ bits.length) :
    ∃ mask used, round A c P D mode extra confidence bits = some (mask,bits.drop used) ∧
      used ≤ budget n extra confidence := by
  obtain ⟨mask,used,found,paid⟩ := EncodedSolverBits.complete (within A c P D mode extra confidence)
    (binary A c P D mode extra confidence) bits enough
  exact ⟨mask,used,by rw [round,found]; rfl,paid⟩

theorem fairTape (A : Adjacency n) (c : Row n) (P : Vector (Fin n × Fin n) m)
    (D : Input n) (mode : ChargedVertexModes.Mode) (extra confidence : ℕ) :
    (EncodedSolverBits.fairTape (budget n extra confidence)).map
      (fun bits => (round A c P D mode extra confidence bits).map Prod.fst) =
        (ideal (program A c P D mode extra confidence)).map some := by
  simp only [round,Option.map_map,Function.comp_def]
  exact EncodedSolverBits.run_fairTape (within A c P D mode extra confidence)
    (binary A c P D mode extra confidence)

theorem supported (A : Adjacency n) (c : Row n) (P : Vector (Fin n × Fin n) m)
    (D : Input n) (mode : ChargedVertexModes.Mode) (extra confidence : ℕ)
    {bits rest : Bits} {mask : Flags n} (ran : round A c P D mode extra confidence bits = some (mask,rest)) :
    mask ∈ (ideal (tree D mode)).support := by
  unfold round at ran
  obtain ⟨⟨out,receipt⟩,found,same⟩ := Option.map_eq_some_iff.mp ran
  have equal : out = mask := congrArg Prod.fst same
  subst out
  apply EncodedAmplification.support_selected (score A c P) (tree D mode) (drawBound n) extra confidence
  exact EncodedSolverBits.run_support (binary A c P D mode extra confidence) found

theorem cut_support (D : Input n) (mode : ChargedVertexModes.Mode)
    {mask : Flags n} (supported : mask ∈ (ideal (tree D mode)).support) :
    IsIntegralCut D.graph (selectedSet mask) (thresholdDemands D.graph D.weight) := by
  cases mode
  · exact EncodedWeightedRounding.support_valid D supported
  · exact EncodedSizeRounding.support_valid D supported

noncomputable section

theorem failure (A : Adjacency n) (w c : Row n) (P : Vector (Fin n × Fin n) m) (τ : ℚ≥0)
    (distinct : Function.Injective fun j : Fin m => P[j.val])
    (mode : ChargedVertexModes.Mode) (extra confidence : ℕ) (B : ℝ) (Bpos : 0 < B)
    (expect : RationalSparsestVertexExpectation.expectedSparsity (scaled A w c τ) (demandSet P) mode ≤ B) :
    let D := scaled A w c τ
    probability ((EncodedSolverBits.fairTape (budget n extra confidence)).map
      (fun bits => (round A c P D mode extra confidence bits).map Prod.fst))
      (RationalSparsestVertexFairTape.bad D (demandSet P) (2*B)) ≤
        ((1 : ℝ)/2)^(extra+1)+((1 : ℝ)/2)^confidence := by
  let D := scaled A w c τ
  have cost (mask : Flags n) :
      (score A c P mask).realValue =
        SparsestVertexBridge.sparsity D.graph D.cost (demandSet P) (selectedSet mask) := by
    simp only [D,RationalSparsestVertexRound.scaled_graph,RationalSparsestVertexRound.scaled_price,
      RationalVertexSparsityCode.score_eq A c P _ distinct]
  have expected : expectedCost (ideal (tree D mode)) (fun mask => ((score A c P mask).realValue : ℝ)) ≤ B := by
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
  change RationalSparsestVertexFairTape.bad D (demandSet P) (2*B) (some mask) ↔ 2*B < ((score A c P mask).realValue : ℝ)
  rw [cost]
  constructor
  · rintro ⟨x,same,paid⟩
    obtain rfl := Option.some.inj same
    exact paid
  · exact fun paid => ⟨mask,rfl,paid⟩

end
end DirectedFlowCutGap.AmplifiedSparsestVertexTape
