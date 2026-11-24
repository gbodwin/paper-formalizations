import DirectedFlowCutGap.AmplifiedBudgetedSparsestEdge
import DirectedFlowCutGap.AmplifiedNormalizedVertexSparsest

/-! Dispatch the two amplified sparsest-cut solvers on the original graph.
Already disconnected demands need no deletion. If no pair is separable,
the entry reports that fact and leaves the input tape intact. -/
namespace DirectedFlowCutGap.AmplifiedSparsestDispatch

open scoped NNRat ENNReal
open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency graph)
open BinaryFractionalRows (Row)
open RationalEdgeThresholds (Weights weights)
open ConcurrentEdgeOracle (Edge)
open RationalSparsestEdgeRound (Mask demandSet)
open RetainedGridState (Flags)
open ConcurrentEdgeZeroPrices (detect positiveGraph)

variable {m n : ℕ}

private def unitPrices (n : ℕ) : Weights n :=
  Vector.replicate n (Vector.replicate n BinaryRational.one)

private theorem unit_graph (A : Adjacency n) : positiveGraph A (unitPrices n) = A := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [positiveGraph,unitPrices,ConcurrentEdgeZeroPrices.rawPrice,RationalEdgeThresholds.cost,
    BinaryFractionalWalkOracle.decodeCost,RawNonnegativeRational.Code.value_one]

def unreachable (A : Adjacency n) (P : Vector (Edge n) m) : Option (Fin m) :=
  detect A (unitPrices n) P

theorem unreachable_found (A : Adjacency n) (P : Vector (Edge n) m) {i : Fin m}
    (found : unreachable A P = some i) :
    ¬ Nonempty (SimplePath (graph A) (P.get i).1 (P.get i).2) := by
  have no := ConcurrentEdgeZeroPrices.detected found
  simpa only [unit_graph] using no

theorem reachable_of_none (A : Adjacency n) (P : Vector (Edge n) m) (none : unreachable A P = none) :
    ∀ i : Fin m, Nonempty (SimplePath (graph A) (P.get i).1 (P.get i).2) := by
  have all := ConcurrentEdgeZeroPrices.all_reachable none
  simpa only [unit_graph] using all

theorem unreachable_none (A : Adjacency n) (P : Vector (Edge n) m)
    (reach : ∀ i : Fin m, Nonempty (SimplePath (graph A) (P.get i).1 (P.get i).2)) :
    unreachable A P = none := by
  cases found : unreachable A P with
  | none => rfl
  | some i => exact ((unreachable_found A P found) (reach i)).elim

def edgeTest (P : Vector (Edge n) m) (i : Fin m) : Bool :=
  decide ((P.get i).1 ≠ (P.get i).2)

def vertexTest (A : Adjacency n) (P : Vector (Edge n) m) (i : Fin m) : Bool :=
  edgeTest P i && !(A[(P.get i).1.val][(P.get i).2.val])

def edgeDemand (P : Vector (Edge n) m) : Option (Fin m) :=
  (List.finRange m).find? (edgeTest P)

def vertexDemand (A : Adjacency n) (P : Vector (Edge n) m) : Option (Fin m) :=
  (List.finRange m).find? (vertexTest A P)

private theorem vertexTest_eq (A : Adjacency n) (P : Vector (Edge n) m) (i : Fin m) :
    vertexTest A P i = true ↔
      (P.get i).1 ≠ (P.get i).2 ∧ ¬ (graph A).Adj (P.get i).1 (P.get i).2 := by
  simp only [vertexTest,edgeTest,Bool.and_eq_true,decide_eq_true_eq]
  change _ ∧ (!A[(P.get i).1.val][(P.get i).2.val]) = true ↔
    _ ∧ ¬ A[(P.get i).1.val][(P.get i).2.val] = true
  cases A[(P.get i).1.val][(P.get i).2.val] <;> simp

theorem edgeDemand_found (P : Vector (Edge n) m) {i : Fin m} (found : edgeDemand P = some i) :
    (P.get i).1 ≠ (P.get i).2 := by
  have test := List.find?_some (p := edgeTest P) found
  simpa only [edgeTest,decide_eq_true_eq] using test

theorem vertexDemand_found (A : Adjacency n) (P : Vector (Edge n) m) {i : Fin m}
    (found : vertexDemand A P = some i) :
    (P.get i).1 ≠ (P.get i).2 ∧ ¬ (graph A).Adj (P.get i).1 (P.get i).2 :=
  (vertexTest_eq A P i).mp (List.find?_some (p := vertexTest A P) found)

theorem edgeDemand_absent (A : Adjacency n) (P : Vector (Edge n) m) (none : edgeDemand P = none) :
    ∀ (i : Fin m) (X : Finset (Edge n)), ¬ EdgeCutsPair (graph A) X (P.get i).1 (P.get i).2 := by
  intro i X
  have miss := (List.find?_eq_none.mp none) i (List.mem_finRange i)
  have eq : (P.get i).1 = (P.get i).2 := by
    by_contra diff
    simp [edgeTest,diff] at miss
  rw [← eq]
  exact not_edgeCutsPair_self _ _ _

theorem vertexDemand_absent (A : Adjacency n) (P : Vector (Edge n) m) (none : vertexDemand A P = none) :
    ∀ (i : Fin m) (X : Finset (Fin n)), ¬ CutsPair (graph A) X (P.get i).1 (P.get i).2 := by
  intro i X
  by_cases eq : (P.get i).1 = (P.get i).2
  · rw [← eq]
    exact not_cutsPair_self _ _ _
  · by_cases arc : (graph A).Adj (P.get i).1 (P.get i).2
    · exact not_cutsPair_of_adj X arc
    · have test := (vertexTest_eq A P i).mpr ⟨eq,arc⟩
      have miss := (List.find?_eq_none.mp none) i (List.mem_finRange i)
      simp [test] at miss

inductive Outcome (Cut : Type) where
  | noSeparatingPair (rest : Bits)
  | cut (mask : Cut) (rest : Bits)

def runEdge (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) : Option (Outcome (Mask n)) :=
  match unreachable A P with
  | some _ => some (.cut (Vector.replicate n (Vector.replicate n false)) bits)
  | none =>
    match edgeDemand P with
    | none => some (.noSeparatingPair bits)
    | some i =>
      have hn : 0 < n := (Nat.zero_le _).trans_lt (P.get i).1.isLt
      (AmplifiedBudgetedSparsestEdge.run hn A c P extra confidence bits).map
        fun (mask,rest) => .cut mask rest

def runVertex (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) : Option (Outcome (Flags n)) :=
  match unreachable A P with
  | some _ => some (.cut (Vector.replicate n false) bits)
  | none =>
    match vertexDemand A P with
    | none => some (.noSeparatingPair bits)
    | some _ => (AmplifiedNormalizedVertexSparsest.run A c P extra confidence bits).map
      fun (_,mask,rest) => .cut mask rest

private theorem pair_entry (P : Vector (Edge n) m) (i : Fin m) : P.get i = P[i.val] := by cases i; rfl

private theorem requested (P : Vector (Edge n) m) (i : Fin m) :
    P.get i ∈ demandSet P := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,(pair_entry P i).symm⟩

theorem edge_disconnected (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    {i : Fin m} (found : unreachable A P = some i) (extra confidence : ℕ) (bits : Bits) :
    runEdge A c P extra confidence bits =
        some (.cut (Vector.replicate n (Vector.replicate n false)) bits) ∧
      0 < (SparsestEdgeBridge.separated (graph A) (demandSet P) ∅).card ∧
      SparsestEdgeBridge.sparsity (graph A) (weights c) (demandSet P) ∅ = 0 := by
  have top := (edgeDistance_eq_top_iff (graph A) (weights c) _ _).mpr (unreachable_found A P found)
  exact ⟨by simp only [runEdge,found],
    SparsestEdgeBridge.unreachable_zero_sparsity (graph A) (weights c) (weights c)
      (demandSet P) (P.get i) (requested P i) top⟩

theorem vertex_disconnected (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m)
    {i : Fin m} (found : unreachable A P = some i) (extra confidence : ℕ) (bits : Bits) :
    runVertex A c P extra confidence bits = some (.cut (Vector.replicate n false) bits) ∧
      0 < (SparsestVertexBridge.separated (graph A) (demandSet P) ∅).card ∧
      SparsestVertexBridge.sparsity (graph A) (RationalSparsestVertexDistances.weights c) (demandSet P) ∅ = 0 := by
  let price := RationalSparsestVertexDistances.weights c
  have top := (vertexDistance_eq_top_iff (graph A) price _ _).mpr (unreachable_found A P found)
  exact ⟨by simp only [runVertex,found],
    SparsestVertexBridge.unreachable_zero_sparsity (graph A) price price
      (demandSet P) (P.get i) (requested P i) top⟩

theorem edge_unsupported (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (read : unreachable A P = none) (empty : edgeDemand P = none) (extra confidence : ℕ) (bits : Bits) :
    runEdge A c P extra confidence bits = some (.noSeparatingPair bits) ∧
      ∀ (i : Fin m) (X : Finset (Edge n)), ¬ EdgeCutsPair (graph A) X (P.get i).1 (P.get i).2 :=
  ⟨by simp only [runEdge,read,empty],edgeDemand_absent A P empty⟩

theorem vertex_unsupported (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m)
    (read : unreachable A P = none) (empty : vertexDemand A P = none) (extra confidence : ℕ) (bits : Bits) :
    runVertex A c P extra confidence bits = some (.noSeparatingPair bits) ∧
      ∀ (i : Fin m) (X : Finset (Fin n)), ¬ CutsPair (graph A) X (P.get i).1 (P.get i).2 :=
  ⟨by simp only [runVertex,read,empty],vertexDemand_absent A P empty⟩

def Outcome.suffix {Cut : Type} : Outcome Cut → Bits
  | .noSeparatingPair rest => rest
  | .cut _ rest => rest

theorem edge_active (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (reach : ∀ i : Fin m, Nonempty (SimplePath (graph A) (P.get i).1 (P.get i).2))
    (i : Fin m) (different : (P.get i).1 ≠ (P.get i).2) (extra confidence : ℕ) (bits : Bits) :
    runEdge A c P extra confidence bits =
      (AmplifiedBudgetedSparsestEdge.run hn A c P extra confidence bits).map fun (mask,rest) => .cut mask rest := by
  have all := unreachable_none A P reach
  cases found : edgeDemand P with
  | none =>
    have miss := (List.find?_eq_none.mp found) i (List.mem_finRange i)
    simp [edgeTest,different] at miss
  | some d => simp only [runEdge,all,found]

theorem vertex_active (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m)
    (reach : ∀ i : Fin m, Nonempty (SimplePath (graph A) (P.get i).1 (P.get i).2))
    (i : Fin m) (different : (P.get i).1 ≠ (P.get i).2) (noArc : ¬ (graph A).Adj (P.get i).1 (P.get i).2)
    (extra confidence : ℕ) (bits : Bits) :
    runVertex A c P extra confidence bits =
      (AmplifiedNormalizedVertexSparsest.run A c P extra confidence bits).map fun (_,mask,rest) => .cut mask rest := by
  have all := unreachable_none A P reach
  cases found : vertexDemand A P with
  | none =>
    have test := (vertexTest_eq A P i).mpr ⟨different,noArc⟩
    have miss := (List.find?_eq_none.mp found) i (List.mem_finRange i)
    simp [test] at miss
  | some d => simp only [runVertex,all,found]

theorem edge_complete (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) (enough : AmplifiedSparsestEdgeTape.budget n extra confidence ≤ bits.length) :
    ∃ answer used, runEdge A c P extra confidence bits = some answer ∧
      answer.suffix = bits.drop used ∧ used ≤ AmplifiedSparsestEdgeTape.budget n extra confidence := by
  cases found : unreachable A P with
  | some i => exact ⟨_,0,(edge_disconnected A c P found extra confidence bits).1,rfl,Nat.zero_le _⟩
  | none =>
    cases demand : edgeDemand P with
    | none => exact ⟨_,0,(edge_unsupported A c P found demand extra confidence bits).1,rfl,Nat.zero_le _⟩
    | some i =>
      have hn : 0 < n := (Nat.zero_le _).trans_lt (P.get i).1.isLt
      obtain ⟨mask,used,ran,within⟩ := AmplifiedBudgetedSparsestEdge.complete hn A c P
        (reachable_of_none A P found) i (edgeDemand_found P demand) extra confidence bits enough
      exact ⟨.cut mask (bits.drop used),used,by simp only [runEdge,found,demand,ran,Option.map_some],rfl,within⟩

theorem vertex_complete (A : Adjacency n) (c : Row n) (P : Vector (Edge n) m) (extra confidence : ℕ)
    (bits : Bits) (enough : AmplifiedSparsestVertexTape.budget n extra confidence ≤ bits.length) :
    ∃ answer used, runVertex A c P extra confidence bits = some answer ∧
      answer.suffix = bits.drop used ∧ used ≤ AmplifiedSparsestVertexTape.budget n extra confidence := by
  cases found : unreachable A P with
  | some i => exact ⟨_,0,(vertex_disconnected A c P found extra confidence bits).1,rfl,Nat.zero_le _⟩
  | none =>
    cases demand : vertexDemand A P with
    | none => exact ⟨_,0,(vertex_unsupported A c P found demand extra confidence bits).1,rfl,Nat.zero_le _⟩
    | some i =>
      obtain ⟨different,noArc⟩ := vertexDemand_found A P demand
      obtain ⟨q,mask,used,ran,within⟩ := AmplifiedNormalizedVertexSparsest.complete A c P
        (reachable_of_none A P found) i different noArc extra confidence bits enough
      exact ⟨.cut mask (bits.drop used),used,by simp only [runVertex,found,demand,ran,Option.map_some],rfl,within⟩

end DirectedFlowCutGap.AmplifiedSparsestDispatch
