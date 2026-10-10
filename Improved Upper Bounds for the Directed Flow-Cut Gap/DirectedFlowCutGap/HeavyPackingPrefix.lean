import DirectedFlowCutGap.BinaryHeavyProviderTrees
import DirectedFlowCutGap.BinaryWeightedPackingTrees
import DirectedFlowCutGap.HeavyPackingEntry

/-! One finite bit stream for the complete original-weight entry, including
all actual adaptive heavy queries and the final weighted ticket selection.
Each provider keeps its specified fresh local ledger inside the returned
answer. The independent prefix has a structural finite-tree length; an
explicit polynomial bound and efficient construction of that length remain
separate, as do raw decoding and physical storage/runtime. -/
namespace DirectedFlowCutGap.HeavyPackingPrefix
noncomputable section
set_option backward.isDefEq.respectTransparency false
open BinaryArithmetic BinaryFractionalRows BinarySamplerMetadata
open HeavyCutProvider FiniteDrawTrees LazyFairBitTrees

/-- This is the literal existing packing entry instantiated with callback trees. -/
def tree {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n) (B : ℕ)
    (resources width : Bits) : FiniteDrawTrees.Tree (HeavyPackingEntry.Output adjacency w) :=
  let decision := WeightedEmptyCutDecision.vertexDecision adjacency w
  if h : decision.1=true then pure (none,decision.2+4) else do
    let packed ← BinaryWeightedPackingConfidence.run w (columns adjacency w)
      (HeavyPackingJoin.support_valid adjacency w)
      (fun he => h ((HeavyPackingEntry.empty_correct adjacency w).mpr he))
      (BinaryHeavyProviderTrees.draw adjacency w (3*HeavyPackingJoin.oracleExponent n B) empty)
      BinarySamplerTrees.bit resources width
    pure (some packed,decision.2+packed.operations+4)

theorem binary {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n) (B : ℕ)
    (resources width : Bits) : Binary (tree adjacency w B resources width) := by
  unfold tree
  dsimp only []
  split_ifs
  · exact .pure _
  · apply binary_bind (BinaryWeightedPackingTrees.confidence_binary _ _ _ _ _
      (fun c => BinaryHeavyProviderTrees.binary adjacency w c _ empty) resources width)
    intro packed
    exact .pure _

/-- Exact full-record law, including every actual provider answer and its
metadata, stopped scans, original-weight ticket and operation annotation. -/
theorem ideal_eq {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n) (B : ℕ)
    (resources width : Bits) :
    ideal (tree adjacency w B resources width)=HeavyPackingEntry.run adjacency w B resources width := by
  unfold tree HeavyPackingEntry.run
  dsimp only []
  split_ifs with h
  · rfl
  · change ideal (FiniteDrawTrees.bind _ _)=_
    change FiniteDrawTrees.law uniformDraw (FiniteDrawTrees.bind _ _)=_
    rw [FiniteDrawTrees.law_bind]
    have hempty : (∅ : FractionalCover.Column n)∉columns adjacency w :=
      fun he => h ((HeavyPackingEntry.empty_correct adjacency w).mpr he)
    have he := BinaryWeightedPackingTrees.confidence_execute w (columns adjacency w)
      (HeavyPackingJoin.support_valid adjacency w) hempty
      (BinaryHeavyProviderTrees.draw adjacency w (3*HeavyPackingJoin.oracleExponent n B) empty)
      uniformDraw resources width
    simp_rw [execute_pmf_eq_law,BinaryHeavyProviderTrees.ideal_eq] at he
    change FiniteDrawTrees.law uniformDraw
      (BinaryWeightedPackingConfidence.run w (columns adjacency w) _ _ _
        BinarySamplerTrees.bit resources width)=HeavyPackingJoin.run adjacency w B hempty resources width at he
    rw [he]
    rfl

/-- The finite maximum is a proof-side budget, not an efficient runtime claim. -/
def budget {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n) (B : ℕ)
    (resources width : Bits) : ℕ := FiniteSupportTrees.depth (tree adjacency w B resources width)

def read {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n) (B : ℕ)
    (resources width : Bits) : StateM (List (Fin 2)) (HeavyPackingEntry.Output adjacency w) :=
  FiniteBinaryPrefix.run (tree adjacency w B resources width)

/-- Direct execution of the original body with one shared finite-list reader.
The provider's specified local ledger does not reset this outer reader state. -/
def direct {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n) (B : ℕ)
    (resources width : Bits) : StateM (List (Fin 2)) (HeavyPackingEntry.Output adjacency w) :=
  let decision := WeightedEmptyCutDecision.vertexDecision adjacency w
  if h : decision.1=true then pure (none,decision.2+4) else do
    let packed ← BinaryWeightedPackingConfidence.run w (columns adjacency w)
      (HeavyPackingJoin.support_valid adjacency w)
      (fun he => h ((HeavyPackingEntry.empty_correct adjacency w).mpr he))
      (fun c => BinaryHeavyProviderTrees.read adjacency w c
        (3*HeavyPackingJoin.oracleExponent n B) empty)
      BinaryTrackedPrefix.next resources width
    pure (some packed,decision.2+packed.operations+4)

theorem same_stream {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n) (B : ℕ)
    (resources width : Bits) : read adjacency w B resources width=direct adjacency w B resources width := by
  unfold read FiniteBinaryPrefix.run tree direct
  dsimp only []
  split_ifs
  · rfl
  · change execute (MonadicBitSampler.liftBit FiniteBinaryPrefix.next) (FiniteDrawTrees.bind _ _)=_
    rw [MonadicBitSampler.execute_bind,BinaryWeightedPackingTrees.confidence_execute]
    have hb : execute (MonadicBitSampler.liftBit FiniteBinaryPrefix.next) BinarySamplerTrees.bit=
        BinaryTrackedPrefix.next := by
      simp only [BinarySamplerTrees.bit,execute,MonadicBitSampler.liftBit_two]
      rfl
    rw [hb]
    rfl

theorem output_law {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n) (B : ℕ)
    (resources width : Bits) :
    (FiniteBinaryPrefix.prefixLaw (budget adjacency w B resources width)).map
      (fun xs => ((read adjacency w B resources width).run xs).1)=
      HeavyPackingEntry.run adjacency w B resources width := by
  rw [budget,read,FiniteBinaryPrefix.output_law (FiniteSupportTrees.depth_within _)
    (binary adjacency w B resources width),ideal_eq]

theorem suffix {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n) (B : ℕ)
    (resources width : Bits) (xs : List (Fin 2))
    (hlen : budget adjacency w B resources width≤xs.length) :
    ∃ used≤budget adjacency w B resources width,
      ((read adjacency w B resources width).run xs).2=xs.drop used :=
  FiniteBinaryPrefix.suffix (FiniteSupportTrees.depth_within _)
    (binary adjacency w B resources width) xs hlen

/-- A short supplied list may be biased, but legal zero fallbacks preserve
actual original-cut validity and zero avoidance on every execution. -/
theorem pathwise_valid {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n) (B : ℕ)
    (resources width : Bits) (xs : List (Fin 2)) :
    let out := ((read adjacency w B resources width).run xs).1
    HeavyPackingEntry.cut out∈columns adjacency w ∧
      ∀ i∈HeavyPackingEntry.cut out,0<(BinaryRational.decode (get w i)).value := by
  have h := BinaryFullPrefixCost.run_supported (binary adjacency w B resources width) xs
  rw [ideal_eq] at h
  exact HeavyPackingEntry.run_valid adjacency w B resources width h

/-- The previously proved uniform graph-size factor transfers to this one
finite stream, with the same complete adaptive history and selected label. -/
theorem uniform_marginal :
    ∀ δ : ℝ,0<δ → ∃ K : ℝ,0<K ∧
      ∀ (n : ℕ) (adjacency : RetainedGridState.PairFlags n) (w : Row n)
        (B : ℕ) (_hwidth : ∀ i,(BinaryRational.decode (get w i)).Bounded B)
        (resources width : Bits) (_hm : value resources=n) (_hB : value width=B) (i : Fin n),
      ((FiniteBinaryPrefix.prefixLaw (budget adjacency w B resources width)).toOuterMeasure
        {xs | (HeavyPackingEntry.label ((read adjacency w B resources width).run xs).1).any
          (BinaryApproximatePackingSampling.coordinate i)=true}).toReal ≤
        K*(n:ℝ)^((1:ℝ)/3+δ)*(FractionalCover.value (BinaryApproximatePacking.capacities w) i : ℝ) := by
  intro δ hδ
  obtain ⟨K,hK,h⟩ := HeavyPackingEntry.uniform_marginal δ hδ
  refine ⟨K,hK,?_⟩
  intro n adjacency w B hwidth resources width hm hB i
  have hi := h n adjacency w B hwidth resources width hm hB i
  rw [← output_law adjacency w B resources width,PMF.toOuterMeasure_map_apply] at hi
  exact hi

end
end DirectedFlowCutGap.HeavyPackingPrefix
