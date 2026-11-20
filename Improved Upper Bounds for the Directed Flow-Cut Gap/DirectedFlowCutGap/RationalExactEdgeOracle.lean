import DirectedFlowCutGap.RationalEdgeDecomposition
import DirectedFlowCutGap.WeakCutExactMarginal
import DirectedFlowCutGap.RetainedTapeInput

/-! An exhaustive exact rational cost oracle for the original edge demands.
It reuses the verified threshold algorithm to check the indicator of each
candidate cut. Its guarantee is at the original total weight. -/
namespace DirectedFlowCutGap.RationalExactEdgeOracle

open scoped NNRat NNReal BigOperators
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights demands weights far far_iff)
open RationalEdgeDecomposition (Good originalWeight originalWeight_eq)

abbrev Edge (n : ℕ) := Fin n × Fin n

private def indicator {n : ℕ} (X : Finset (Edge n)) : Weights n :=
  Vector.ofFn fun s => Vector.ofFn fun t =>
    if (s,t) ∈ X then BinaryRational.one else BinaryRational.zero

private theorem indicator_eq {n : ℕ} (X : Finset (Edge n)) :
    weights (indicator X) = edgeCutIndicator X := by
  funext e
  obtain ⟨s,t⟩ := e
  by_cases he : (s,t) ∈ X <;>
    simp [indicator, he, weights, RationalEdgeThresholds.cost, BinaryFractionalWalkOracle.decodeCost,
      edgeCutIndicator]

private def checkCut {n : ℕ} (A : Adjacency n) (D : List (Edge n)) (X : Finset (Edge n)) : Bool :=
  decide (∀ e ∈ X, A[e.1.val][e.2.val] = true) &&
    D.all (far A (indicator X))

private theorem checkCut_iff {n : ℕ} (A : Adjacency n) (D : List (Edge n)) (X : Finset (Edge n)) :
    checkCut A D X = true ↔
      X ⊆ graphEdges (graph A) ∧ IsIntegralEdgeCut (graph A) X {e | e ∈ D} := by
  simp only [checkCut, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    isIntegralEdgeCut_iff_indicator, IsFractionalEdgeCut]
  constructor
  · rintro ⟨edges,cut⟩
    refine ⟨fun e he => (mem_graphEdges _ _).mpr (edges e he), fun s t h => ?_⟩
    have farPair := (far_iff A (indicator X) (s,t)).mp (cut (s,t) h)
    simpa only [indicator_eq,edgeThresholdDemands,Set.mem_ofPred_eq] using farPair
  · rintro ⟨edges,cut⟩
    refine ⟨fun e he => (mem_graphEdges _ _).mp (edges he), ?_⟩
    intro ⟨s,t⟩ h
    apply (far_iff A (indicator X) (s,t)).mpr
    simpa only [indicator_eq,edgeThresholdDemands,Set.mem_ofPred_eq] using cut s t h

private def arcs {n : ℕ} (A : Adjacency n) : List (Edge n) :=
  (RetainedTapeInput.allPairs n).filter fun e => A[e.1.val][e.2.val]

private theorem mem_arcs {n : ℕ} (A : Adjacency n) (e : Edge n) :
    e ∈ arcs A ↔ e ∈ graphEdges (graph A) := by
  simp only [arcs,List.mem_filter,RetainedTapeInput.mem_allPairs,true_and,mem_graphEdges]
  rfl

private def candidates {n : ℕ} (A : Adjacency n) (D : List (Edge n)) : List (Finset (Edge n)) :=
  ((arcs A).sublists.map List.toFinset).filter (checkCut A D)

private theorem mem_candidates {n : ℕ} (A : Adjacency n) (D : List (Edge n)) (X : Finset (Edge n)) :
    X ∈ candidates A D ↔ X ⊆ graphEdges (graph A) ∧ IsIntegralEdgeCut (graph A) X {e | e ∈ D} := by
  unfold candidates
  rw [List.mem_filter, checkCut_iff]
  have listed (h : X ⊆ graphEdges (graph A)) : X ∈ (arcs A).sublists.map List.toFinset := by
    refine List.mem_map.mpr ⟨(arcs A).filter (fun e => e ∈ X),
      List.mem_sublists.mpr (List.filter_sublist ..), ?_⟩
    ext e
    simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right, fun he => ⟨(mem_arcs A e).mpr (h he),he⟩⟩
  exact ⟨And.right, fun h => ⟨listed h.1,h⟩⟩

/-- Returns a minimum cost valid edge cut whenever the demand list admits one. -/
def select {n : ℕ} (A : Adjacency n) (D : List (Edge n)) (c : Edge n → ℚ≥0) :
    Option (Finset (Edge n)) :=
  (candidates A D).minOn? fun X => ∑ e ∈ X, c e

theorem select_minimum {n : ℕ} (A : Adjacency n) (D : List (Edge n)) (c : Edge n → ℚ≥0)
    {Y : Finset (Edge n)} (edges : Y ⊆ graphEdges (graph A))
    (valid : IsIntegralEdgeCut (graph A) Y {e | e ∈ D}) :
    ∃ X, select A D c=some X ∧ X ⊆ graphEdges (graph A) ∧
      IsIntegralEdgeCut (graph A) X {e | e ∈ D} ∧ (∑ e ∈ X, c e) ≤ ∑ e ∈ Y, c e := by
  let fee (X : Finset (Edge n)) := ∑ e ∈ X, c e
  have present := (mem_candidates A D Y).mpr ⟨edges,valid⟩
  let h := List.ne_nil_of_mem present
  let X := (candidates A D).minOn fee h
  have hx : X ∈ candidates A D := List.minOn_mem
  obtain ⟨arcs,cuts⟩ := (mem_candidates A D X).mp hx
  exact ⟨X,List.minOn?_eq_some_minOn h,arcs,cuts,List.apply_minOn_le_of_mem (f := fee) present⟩

def run {n : ℕ} (A : Adjacency n) (w : Weights n) (c : Edge n → ℚ≥0) : Finset (Edge n) :=
  (select A (demands A w) c).getD ∅

theorem run_spec {n : ℕ} (A : Adjacency n) (w : Weights n) (c : Edge n → ℚ≥0)
    (k : ℚ≥0) (factor : HasEdgeRoundingFactor (graph A) (weights w) (k : ℝ)) :
    Good A w (run A w c) ∧ (∑ e ∈ run A w c, c e) ≤ k * ∑ e, c e * originalWeight A w e := by
  obtain ⟨Y,⟨edges,valid⟩,fee⟩ := factor.real_cost_round (fun e => (c e : ℝ)) (fun e => NNRat.cast_nonneg _)
  have demandCut : IsIntegralEdgeCut (graph A) Y {e | e ∈ demands A w} :=
    fun s t h => valid s t ((RationalEdgeThresholds.demands_iff A w _).mp h)
  obtain ⟨X,chosen,arcs,cuts,best⟩ := select_minimum A (demands A w) c edges demandCut
  have target : (∑ e ∈ Y, c e) ≤ k * ∑ e, c e * originalWeight A w e := by
    apply (NNRat.cast_le (K := ℝ)).mp
    simp only [NNRat.cast_mul,NNRat.cast_sum]
    have same (e : Edge n) : (originalWeight A w e : ℝ) =
        (actualEdgeWeight (graph A) (weights w) e : ℝ) :=
      congrArg (fun x : ℝ≥0 => (x : ℝ)) (originalWeight_eq A w e)
    simpa only [mwPotential,same] using fee
  rw [run,chosen,Option.getD_some]
  exact ⟨⟨arcs,cuts⟩,best.trans target⟩

/-- The exhaustive oracle realizes the exact bound at the original total. -/
theorem original_factor {n : ℕ} (A : Adjacency n) (w : Weights n) (c : Edge n → ℚ≥0) :
    let k := ExactFlowCutGap.efg n (totalEdgeWeight (graph A) (weights w))
    Good A w (run A w c) ∧
      (∑ e ∈ run A w c, c e) ≤ (k : ℚ≥0) * ∑ e, c e * originalWeight A w e := by
  let W := totalEdgeWeight (graph A) (weights w)
  let k := ExactFlowCutGap.efg n W
  apply run_spec A w c (k : ℚ≥0)
  simpa only [NNRat.cast_natCast] using ExactFlowCutGap.efg_bound n W (graph A) (weights w) rfl

end DirectedFlowCutGap.RationalExactEdgeOracle
