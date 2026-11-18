import DirectedFlowCutGap.EncodedEdgeGadget
import DirectedFlowCutGap.EncodedSizeRounding
import DirectedFlowCutGap.AdaptiveEdgeBound

/-!
# Rounding a rational edge instance on the retained dyadic gadget

The weighted vertex program receives the actual gadget arrays. Its output
is pulled back using the selected incident labels of each original edge.
-/

namespace DirectedFlowCutGap.EncodedEdgeRounding

open scoped NNReal
open EncodedEdgeGadget FiniteDrawTrees FiniteAmplification RetainedGridState

attribute [local instance] EncodedUniformRounding.flagsFintype

private def selectedNode {n : ℕ} {D : Input n} (g : Prepared D) (mask : Flags g.size)
    (x : RawNode n) : Bool :=
  (List.finRange g.size).any fun i => mask[i.val] && decide (g.vertices[i.val].val = x)

def pullback {n : ℕ} {D : Input n} (g : Prepared D) (mask : Flags g.size) : PairFlags n :=
  Vector.ofFn fun s => Vector.ofFn fun t =>
    D.adjacency[s.val][t.val] &&
      (selectedNode g mask (EdgeToVertex.right (labelAt g.labels) (s, t)) ||
       selectedNode g mask (EdgeToVertex.left (labelAt g.labels) (s, t)))

def selectedEdges {n : ℕ} (mask : PairFlags n) : Finset (EncodedEdgeGadget.Pair n) :=
  Finset.univ.filter fun e => flag mask e = true

private theorem selectedNode_iff {n : ℕ} (D : Input n) (mask : Flags (build D).size)
    (x : RawNode n) :
    selectedNode (build D) mask x = true ↔
      x ∈ ((cutSet mask).image (indexEquiv D)).image Subtype.val := by
  rw [Finset.image_image]
  simp only [selectedNode, List.any_eq_true, List.mem_finRange, true_and,
    Bool.and_eq_true, decide_eq_true_eq, Finset.mem_image, Function.comp_apply, mem_cutSet,
    indexEquiv_apply]

theorem pullback_eq {n : ℕ} (D : Input n) (mask : Flags (build D).size) :
    selectedEdges (pullback (build D) mask) =
      EdgeToVertex.pullback D.graph (labelAt (labelTable D)) ((cutSet mask).image (indexEquiv D)) := by
  ext e
  rw [selectedEdges, Finset.mem_filter]
  have hl : (build D).labels = labelTable D := rfl
  simp only [Finset.mem_univ, true_and, flag, pullback, hl,
    Vector.getElem_ofFn, Bool.and_eq_true, Bool.or_eq_true, EdgeToVertex.mem_pullback, mem_graphEdges,
    Input.graph, selectedNode_iff]
  rfl

theorem pullback_cut {n : ℕ} (D : Input n) (mask : Flags (build D).size)
    (h : IsIntegralCut (build D).data.graph (cutSet mask)
      (thresholdDemands (build D).data.graph (build D).data.weight)) :
    IsIntegralEdgeCut D.graph (selectedEdges (pullback (build D) mask))
      (edgeThresholdDemands D.graph D.weight) := by
  let e := indexEquiv D
  have hg := FiniteGraphRelabeling.inverse_adj e (build_adj D)
  have hc := FiniteGraphRelabeling.threshold_cut_pullback e.symm hg (build D).data.weight
    (cutSet mask) h
  have he : (fun x => (build D).data.weight (e.symm x)) =
      EdgeToVertex.weight D.graph (labelAt (labelTable D)) (DyadicEdgeWeights.value n) := by
    funext x
    rw [build_weight D (e.symm x)]
    change EdgeToVertex.weight _ _ _ (e (e.symm x)) = _
    rw [Equiv.apply_symm_apply]
  rw [he] at hc
  rw [pullback_eq]
  intro s t hst
  apply EdgeToVertex.pullback_cutsPair
  exact hc _ _ (threshold_transfer D hst)

theorem pullback_cost_le {n : ℕ} (D : Input n) (mask : Flags (build D).size) :
    edgeCutCost D.graph D.cost (selectedEdges (pullback (build D) mask)) ≤
      cutCost (build D).data.cost (cutSet mask) := by
  rw [pullback_eq]
  apply (EdgeToVertex.pullback_cost_le ..).trans_eq
  unfold cutCost
  rw [Finset.sum_image]
  · exact Finset.sum_congr rfl (fun i _ => (build_cost D i).symm)
  · exact (indexEquiv D).injective.injOn

abbrev Rounding (m : ℕ) := EncodedUnitCostReplication.Input m → FiniteDrawTrees.Tree (Flags m)

def tree {n : ℕ} (D : Input n) (round : (m : ℕ) → Rounding m) :
    FiniteDrawTrees.Tree (PairFlags n) :=
  let g := build D
  map (pullback g) (round g.size g.data)

def massBitTree {n : ℕ} (T : ℕ) (D : Input n) : FiniteDrawTrees.Tree (PairFlags n) :=
  LazyFairBitTrees.lower T (tree D (fun _ => EncodedWeightedRounding.tree))

def sizeBitTree {n : ℕ} (T : ℕ) (D : Input n) : FiniteDrawTrees.Tree (PairFlags n) :=
  LazyFairBitTrees.lower T (tree D (fun _ => EncodedSizeRounding.tree))

theorem support_valid {n : ℕ} (D : Input n) (round : (m : ℕ) → Rounding m)
    (hround : ∀ {m : ℕ} (I : EncodedUnitCostReplication.Input m) {a : Flags m},
      a ∈ (ideal (round m I)).support →
      IsIntegralCut I.graph (cutSet a) (thresholdDemands I.graph I.weight))
    {out : PairFlags n} (hout : out ∈ (ideal (tree D round)).support) :
    selectedEdges out ⊆ graphEdges D.graph ∧
      IsIntegralEdgeCut D.graph (selectedEdges out) (edgeThresholdDemands D.graph D.weight) := by
  simp only [tree, ideal, law_map] at hout
  obtain ⟨a, ha, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  refine ⟨?_, pullback_cut D a (hround _ ha)⟩
  intro e he
  rw [pullback_eq] at he
  exact (EdgeToVertex.mem_pullback .. |>.mp he).1

theorem massBit_support_valid {n : ℕ} (T : ℕ) (D : Input n)
    {out : PairFlags n} (hout : out ∈ (ideal (massBitTree T D)).support) :
    selectedEdges out ⊆ graphEdges D.graph ∧
      IsIntegralEdgeCut D.graph (selectedEdges out) (edgeThresholdDemands D.graph D.weight) :=
  support_valid D (fun _ => EncodedWeightedRounding.tree)
    (fun I _ h => EncodedWeightedRounding.support_valid I h)
    (LazyFairBitTrees.lowered_support_subset_ideal T _ hout)

theorem sizeBit_support_valid {n : ℕ} (T : ℕ) (D : Input n)
    {out : PairFlags n} (hout : out ∈ (ideal (sizeBitTree T D)).support) :
    selectedEdges out ⊆ graphEdges D.graph ∧
      IsIntegralEdgeCut D.graph (selectedEdges out) (edgeThresholdDemands D.graph D.weight) :=
  support_valid D (fun _ => EncodedSizeRounding.tree)
    (fun I _ h => EncodedSizeRounding.support_valid I h)
    (LazyFairBitTrees.lowered_support_subset_ideal T _ hout)

noncomputable def expectedPrice {n : ℕ} (D : Input n) (round : (m : ℕ) → Rounding m) : ℝ :=
  expectedCost ((ideal (tree D round)).map selectedEdges)
    (fun X => (edgeCutCost D.graph D.cost X : ℝ))

theorem expected_price_le {n : ℕ} (D : Input n) (round : (m : ℕ) → Rounding m) :
    expectedPrice D round ≤
      expectedCost (ideal (round (build D).size (build D).data))
        (fun X => (cutCost (build D).data.cost (cutSet X) : ℝ)) := by
  simp only [expectedPrice, tree, ideal, law_map, PMF.map_comp, expectedCost_map]
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  exact NNReal.coe_le_coe.mpr (pullback_cost_le D a)

private theorem expected_price_empty (D : Input 0) (round : (m : ℕ) → Rounding m) :
    expectedPrice D round = 0 := by
  have hz (X : Finset (EncodedEdgeGadget.Pair 0)) : edgeCutCost D.graph D.cost X = 0 := by
    unfold edgeCutCost
    exact Finset.sum_eq_zero (fun e _ => Fin.elim0 e.1)
  simp [expectedPrice, expectedCost, hz]

private theorem size_power_le {n : ℕ} (D : Input n) (a b : ℝ) (ha : 0 ≤ a) (C : ℝ≥0)
    (h : (AdaptiveEdgeBound.gadgetSize n : ℝ≥0) ^ a ≤ C * (n : ℝ≥0) ^ b) :
    ((build D).size : ℝ) ^ a ≤ (C : ℝ) * (n : ℝ) ^ b := by
  have hs : (build D).size ≤ AdaptiveEdgeBound.gadgetSize n := by
    rw [AdaptiveEdgeBound.gadgetSize_eq]
    exact build_size_le D
  have hp := NNReal.rpow_le_rpow (by exact_mod_cast hs :
    ((build D).size : ℝ≥0) ≤ (AdaptiveEdgeBound.gadgetSize n : ℝ≥0)) ha
  exact_mod_cast hp.trans h

theorem size_expected_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
      ∀ (n : ℕ) (D : Input n),
        expectedPrice D (fun _ => EncodedSizeRounding.tree) ≤
          K * (n : ℝ) ^ (1 / 3 + ε) * (weightedEdgeCost D.graph D.cost D.weight : ℝ) := by
  intro ε hε
  obtain ⟨K, hK, hv⟩ := EncodedSizeRounding.expected_cost_uniform (ε / 2) (by positivity)
  obtain ⟨C, hC, hs⟩ := AdaptiveEdgeBound.gadget_power_uniform (1 / 3 + ε / 2) (ε / 2)
    (by positivity)
  refine ⟨4 * K * (C : ℝ), by positivity, ?_⟩
  intro n D
  by_cases hn : n = 0
  · subst n
    rw [expected_price_empty]
    positivity
  · let g := build D
    let obj : ℝ := weightedEdgeCost D.graph D.cost D.weight
    have hn' : 1 ≤ n := by omega
    have hh := hs n hn'
    rw [show (1 / 3 : ℝ) + ε / 2 + ε / 2 = 1 / 3 + ε by ring] at hh
    have hp := size_power_le D _ _ (by positivity) C hh
    have hc : (weightedCost g.data.cost g.data.weight : ℝ) ≤ 4 * obj := by
      change (weightedCost (build D).data.cost (build D).data.weight : ℝ) ≤
        4 * (weightedEdgeCost D.graph D.cost D.weight : ℝ)
      exact_mod_cast build_weightedCost_le D
    calc
      _ ≤ K * (g.size : ℝ) ^ (1 / 3 + ε / 2) * (weightedCost g.data.cost g.data.weight : ℝ) :=
        (expected_price_le D _).trans (hv g.size g.data)
      _ ≤ K * ((C : ℝ) * (n : ℝ) ^ (1 / 3 + ε)) * (4 * obj) := by gcongr
      _ = _ := by ring

theorem mass_expected_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
      ∀ (n : ℕ) (D : Input n),
        expectedPrice D (fun _ => EncodedWeightedRounding.tree) ≤
          K * (n : ℝ) ^ ε * (totalEdgeWeight D.graph D.weight : ℝ) ^ (1 / 2 : ℝ) *
            (weightedEdgeCost D.graph D.cost D.weight : ℝ) := by
  intro ε hε
  obtain ⟨K, hK, hv⟩ := EncodedWeightedRounding.expected_cost_uniform (ε / 2) (by positivity)
  obtain ⟨C, hC, hs⟩ := AdaptiveEdgeBound.gadget_power_uniform (ε / 2) (ε / 2) (by positivity)
  refine ⟨4 * K * (C : ℝ) * (4 : ℝ) ^ (1 / 2 : ℝ), by positivity, ?_⟩
  intro n D
  by_cases hn : n = 0
  · subst n
    rw [expected_price_empty]
    positivity
  · let g := build D
    let W : ℝ := totalEdgeWeight D.graph D.weight
    let obj : ℝ := weightedEdgeCost D.graph D.cost D.weight
    have hn' : 1 ≤ n := by omega
    have hh := hs n hn'
    rw [show ε / 2 + ε / 2 = ε by ring] at hh
    have hp := size_power_le D _ _ (by positivity) C hh
    have hc : (weightedCost g.data.cost g.data.weight : ℝ) ≤ 4 * obj := by
      change (weightedCost (build D).data.cost (build D).data.weight : ℝ) ≤
        4 * (weightedEdgeCost D.graph D.cost D.weight : ℝ)
      exact_mod_cast build_weightedCost_le D
    have hw : (totalWeight g.data.weight : ℝ) ≤ 4 * W := by
      change (totalWeight (build D).data.weight : ℝ) ≤ 4 * (totalEdgeWeight D.graph D.weight : ℝ)
      exact_mod_cast build_totalWeight_le D
    have hr : (totalWeight g.data.weight : ℝ) ^ (1 / 2 : ℝ) ≤
        (4 : ℝ) ^ (1 / 2 : ℝ) * W ^ (1 / 2 : ℝ) :=
      (Real.rpow_le_rpow (by positivity) hw (by norm_num)).trans_eq
        (Real.mul_rpow (by norm_num) (by positivity))
    calc
      _ ≤ K * (g.size : ℝ) ^ (ε / 2) * (totalWeight g.data.weight : ℝ) ^ (1 / 2 : ℝ) *
          (weightedCost g.data.cost g.data.weight : ℝ) :=
        (expected_price_le D _).trans (hv g.size g.data)
      _ ≤ K * ((C : ℝ) * (n : ℝ) ^ ε) * ((4 : ℝ) ^ (1 / 2 : ℝ) * W ^ (1 / 2 : ℝ)) *
          (4 * obj) := by gcongr
      _ = _ := by ring

end DirectedFlowCutGap.EncodedEdgeRounding
