import DirectedFlowCutGap.RationalTwoLayerCertificate
import DirectedFlowCutGap.RationalTwoSideOracle

/-! A checked two-stage graph gets both an exact-factor priced oracle
and a singleton uniform edge-cut family. Neither entry runs the
exhaustive generic cut search. -/
namespace DirectedFlowCutGap.RationalRankedEdgeOracle

open scoped NNReal NNRat
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open RationalEdgeDecomposition (Good originalWeight)
open RationalExactEdgeOracle (Edge)
open RationalInstanceEdgeFactor (emptyCutAccepted least emptyCutAccepted_iff emptyCutAccepted_zero)
open RationalTwoLayerCertificate (assign accepts separates side)

def recognizes {n : ℕ} (A : Adjacency n) (w : Weights n) : Bool :=
  accepts A w (assign A w)

def priceCut {n : ℕ} (A : Adjacency n) (w : Weights n) (price : Edge n → ℚ≥0) :
    Option (Finset (Edge n)) :=
  let ranks := assign A w
  if accepts A w ranks then RationalTwoSideOracle.runSeparated A w (side ranks) price
  else none

theorem priceCut_spec {n : ℕ} (A : Adjacency n) (w : Weights n)
    (recognized : recognizes A w = true) (price : Edge n → ℚ≥0) :
    ∃ X, priceCut A w price = some X ∧ X ⊆ graphEdges (graph A) ∧
      IsIntegralEdgeCut (graph A) X (edgeThresholdDemands (graph A) (weights w)) ∧
      (edgeCutCost (graph A) (fun e => (price e : ℝ≥0)) X : ℝ) ≤
        (least A w : ℝ) *
          (weightedEdgeCost (graph A) (fun e => (price e : ℝ≥0)) (weights w) : ℝ) := by
  change accepts A w (assign A w) = true at recognized
  simpa [priceCut,recognized] using
    RationalTwoSideOracle.runSeparated_spec A w (side (assign A w))
      (fun p => separates A w (assign A w) recognized p) price

def singleCut {n : ℕ} (A : Adjacency n) (w : Weights n) : Option (Finset (Edge n)) :=
  let ranks := assign A w
  if accepts A w ranks then
    if emptyCutAccepted A w then some ∅
    else some (RationalTwoSideOracle.cut A w (side ranks) (1/2))
  else none

theorem singleCut_none_iff {n : ℕ} (A : Adjacency n) (w : Weights n) :
    singleCut A w = none ↔ recognizes A w = false := by
  unfold recognizes singleCut
  dsimp only
  split <;> simp_all
  split <;> simp_all

private theorem singleCut_spec_at_least {n : ℕ} (A : Adjacency n) (w : Weights n)
    (recognized : recognizes A w = true) :
    ∃ X, singleCut A w = some X ∧ Good A w X ∧
      ∀ e ∈ X, 1 ≤ 2*(originalWeight A w e : ℝ)*(least A w : ℝ) := by
  change accepts A w (assign A w) = true at recognized
  by_cases empty : emptyCutAccepted A w = true
  · have valid := (emptyCutAccepted_iff A w).mp empty
    refine ⟨∅,by simp [singleCut,recognized,empty],⟨Finset.empty_subset _,?_⟩,by simp⟩
    exact fun s t h => valid s t ((RationalEdgeThresholds.demands_iff A w _).mp h)
  · let X := RationalTwoSideOracle.cut A w (side (assign A w)) (1/2)
    have bound : (1 : ℝ) ≤ (least A w : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr fun h => empty ((emptyCutAccepted_zero A w).mpr h))
    refine ⟨X,by simp [singleCut,recognized,empty,X],?_⟩
    refine ⟨RationalTwoSideOracle.cut_good A w _
      (fun p => separates A w (assign A w) recognized p) (by norm_num),?_⟩
    intro e mem
    have heavy := RationalTwoSideOracle.cut_half_weight A w _ mem
    calc
      1 ≤ 2*(originalWeight A w e : ℝ) := by linarith
      _ = 2*(originalWeight A w e : ℝ)*1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left bound (by positivity)

theorem singleCut_spec {n : ℕ} (A : Adjacency n) (w : Weights n)
    (recognized : recognizes A w = true) :
    ∃ X, singleCut A w = some X ∧ Good A w X ∧
      ∀ e, (if e ∈ X then (1 : ℝ) else 0) ≤
        2*(originalWeight A w e : ℝ)*
          (ExactFlowCutGap.efg n (totalEdgeWeight (graph A) (weights w)) : ℝ) := by
  obtain ⟨X,found,good,included⟩ := singleCut_spec_at_least A w recognized
  refine ⟨X,found,good,?_⟩
  intro e
  by_cases mem : e ∈ X
  · rw [ite_eq_left mem]
    apply (included e mem).trans
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (RationalInstanceEdgeFactor.least_le_original_factor A w))
      (by positivity)
  · rw [ite_eq_right mem]
    positivity

def family {n : ℕ} (A : Adjacency n) (w : Weights n) : Option (List (Finset (Edge n))) :=
  (singleCut A w).map fun X => [X]

theorem family_spec {n : ℕ} (A : Adjacency n) (w : Weights n)
    (recognized : recognizes A w = true) :
    ∃ L, family A w = some L ∧ L.length = 1 ∧
      (∀ X ∈ L, Good A w X) ∧
      ∀ e, (L.countP (fun X => decide (e ∈ X)) : ℝ) / (L.length : ℝ) ≤
        2*(originalWeight A w e : ℝ)*
          (ExactFlowCutGap.efg n (totalEdgeWeight (graph A) (weights w)) : ℝ) := by
  obtain ⟨X,found,good,marginal⟩ := singleCut_spec A w recognized
  refine ⟨[X], by simp [family,found],rfl,by simpa using good,?_⟩
  intro e
  by_cases mem : e ∈ X <;> simpa [mem] using marginal e

def draw {n : ℕ} (A : Adjacency n) (w : Weights n) (tape : List Bool) :
    Option (Finset (Edge n) × List Bool) :=
  (singleCut A w).map fun X => (X,tape)

theorem draw_spec {n : ℕ} (A : Adjacency n) (w : Weights n) (tape : List Bool)
    (recognized : recognizes A w = true) :
    ∃ X, draw A w tape = some (X,tape) ∧ Good A w X ∧
      ∀ e, (if e ∈ X then (1 : ℝ) else 0) ≤
        2*(originalWeight A w e : ℝ)*
          (ExactFlowCutGap.efg n (totalEdgeWeight (graph A) (weights w)) : ℝ) := by
  obtain ⟨X,found,good,marginal⟩ := singleCut_spec A w recognized
  exact ⟨X,by simp [draw,found],good,marginal⟩

end DirectedFlowCutGap.RationalRankedEdgeOracle
