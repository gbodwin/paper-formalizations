import DirectedFlowCutGap.ConcurrentEdgeBudgetRound

/-! Compute the sparsity of the actual original arc mask. Each demand
is tested in the graph with precisely the selected arcs removed. -/
namespace DirectedFlowCutGap.RationalEdgeSparsityCode

open scoped NNRat NNReal
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open RationalSparsestEdgeRound (Mask demandSet)
open EncodedEdgeRounding (selectedEdges)
open ConcurrentEdgeOracle (Edge)
open ConcurrentEdgeZeroPrices (rawPrice rawPrice_eq)
open RetainedGridState (flag)
open RawNonnegativeRational (Code)

variable {m n : ℕ}

def without (A : Adjacency n) (mask : Mask n) : Adjacency n :=
  Vector.ofFn fun u => Vector.ofFn fun v => A[u.val][v.val] && !(flag mask (u,v))

theorem without_eq (A : Adjacency n) (mask : Mask n) :
    graph (without A mask) = edgeDeletedGraph (graph A) (selectedEdges mask) := by
  apply Digraph.ext
  funext u v
  apply propext
  change (without A mask)[u.val][v.val] = true ↔
    A[u.val][v.val] = true ∧ ((u,v) : Edge n) ∉ selectedEdges mask
  simp [without, selectedEdges]

def separates (A : Adjacency n) (c : Weights n) (mask : Mask n) (d : Edge n) : Bool :=
  (RationalSparsestEdgeDistances.distance (without A mask) c d).isNone

theorem separates_eq (A : Adjacency n) (c : Weights n) (mask : Mask n) (d : Edge n) :
    separates A c mask d = true ↔ EdgeCutsPair (graph A) (selectedEdges mask) d.1 d.2 := by
  rw [separates, Option.isNone_iff_eq_none, RationalSparsestEdgeDistances.none_iff,
    without_eq, edgeDistance_eq_top_iff, edgeCutsPair_iff_edgeDeletedGraph]

def count (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) (mask : Mask n) : ℕ :=
  (Finset.univ.filter fun j : Fin m => separates A c mask P[j.val]).card

private theorem demanded (P : Vector (Edge n) m) (j : Fin m) : P[j.val] ∈ demandSet P :=
  Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩

theorem count_eq (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) (mask : Mask n)
    (distinct : Function.Injective fun j : Fin m => P[j.val]) :
    count A c P mask = (SparsestEdgeBridge.separated (graph A) (demandSet P) (selectedEdges mask)).card := by
  classical
  let includePair (j : Fin m) : demandSet P := ⟨P[j.val], demanded P j⟩
  have injective : Function.Injective includePair := fun _ _ same => distinct (congrArg Subtype.val same)
  let indexed := Finset.univ.filter fun j : Fin m => separates A c mask P[j.val]
  have eq : indexed.image includePair = SparsestEdgeBridge.separated (graph A) (demandSet P)
      (selectedEdges mask) := by
    ext d
    simp only [Finset.mem_image, SparsestEdgeBridge.separated, Finset.mem_filter, Finset.mem_univ,
      true_and, indexed, separates_eq]
    constructor
    · rintro ⟨j, separated, rfl⟩
      exact separated
    · intro isCut
      obtain ⟨j,_,representation⟩ := Finset.mem_image.mp d.property
      have eq : includePair j = d := Subtype.ext representation
      exact ⟨j, by rw [← eq] at isCut; exact isCut, eq⟩
  rw [← eq, Finset.card_image_of_injective _ injective]
  rfl

def cutPrice (A : Adjacency n) (c : Weights n) (mask : Mask n) : ℚ≥0 :=
  ∑ e : Edge n, if flag mask e then RationalEdgeDecomposition.originalWeight A c e else 0

theorem cutPrice_eq (A : Adjacency n) (c : Weights n) (mask : Mask n) :
    (cutPrice A c mask : ℝ≥0) = edgeCutCost (graph A) (weights c) (selectedEdges mask) := by
  have cast (e : Edge n) :
      ((if flag mask e then RationalEdgeDecomposition.originalWeight A c e else 0 : ℚ≥0) : ℝ≥0) =
        if flag mask e then actualEdgeWeight (graph A) (weights c) e else 0 := by
    split_ifs <;> simp [RationalEdgeDecomposition.originalWeight_eq]
  simp only [cutPrice, NNRat.cast_sum, cast, edgeCutCost, selectedEdges, Finset.filter_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases picked : flag mask e = true
  · by_cases arc : (graph A).Adj e.1 e.2
    · rw [actualEdgeWeight_of_adj _ _ arc]
      simp [picked, arc]
    · rw [actualEdgeWeight_of_not_adj _ _ arc]
      simp [arc]
  · simp [picked]

def score (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) (mask : Mask n) : Code :=
  Code.ofNNRat (cutPrice A c mask / (count A c P mask : ℚ≥0))

theorem score_eq (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) (mask : Mask n)
    (distinct : Function.Injective fun j : Fin m => P[j.val]) :
    (score A c P mask).realValue =
      SparsestEdgeBridge.sparsity (graph A) (weights c) (demandSet P) (selectedEdges mask) := by
  simp only [score, Code.realValue, Code.value_ofNNRat, NNRat.cast_div, NNRat.cast_natCast,
    cutPrice_eq, count_eq A c P mask distinct, SparsestEdgeBridge.sparsity]

end DirectedFlowCutGap.RationalEdgeSparsityCode
