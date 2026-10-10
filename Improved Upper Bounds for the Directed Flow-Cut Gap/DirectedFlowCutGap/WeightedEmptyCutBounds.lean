import DirectedFlowCutGap.WeightedEmptyCutDecision

/-!
# Composed charge and retained-field contract for the empty-cut decision

The proof follows the actual binary comparison and complete Boolean/list scan.
The only runtime premise is named `PathContract`: every actual shortest call
has the stated charge and returned numerator/denominator lengths. The intended
discharge is `BinaryFractionalWalkBounds.shortest_charge` and `shortest_stored`;
keeping it explicit makes this module independent of that unfinished build.

These are instrumented Boolean/list charges on an already materialized
`RetainedTapeInput.allPairs` list. Its producer, the concrete label/storage
realization of the shortest program, and a fixed-body whole-program simulation
are still separate joins. The field theorem bounds the actual retained binary
fractions and edge list; it does not silently encode Fin labels at unit cost.
-/
namespace DirectedFlowCutGap.WeightedEmptyCutBounds

open BinaryRational BinaryFractionalWalkOracle WeightedEmptyCutDecision
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated
variable {n W K B : ℕ}

/-- Bounds on the actual calls made by this scan, not on an alternative oracle. -/
structure PathContract (adjacency : Adjacency n) (cost : Fin n → Cost n)
    (W K : ℕ) : Prop where
  charge : ∀ s t,
    (shortest (ResidualSearch.Enumeration.fin n) adjacency (cost s) s t).2 ≤ K
  stored : ∀ s t q,
    (shortest (ResidualSearch.Enumeration.fin n) adjacency (cost s) s t).1 = some q →
      StoredBounded q.cost W

def pairBound (W K : ℕ) : ℕ := K + 2048 * (W + 1)^2 + 6
def scanBound (D W K : ℕ) : ℕ := D * (pairBound W K + 4) + 1
def decisionBound (n W K : ℕ) : ℕ := scanBound (n*n) W K

theorem rejectPair_charge (adjacency : Adjacency n) (cost : Fin n → Cost n)
    (h : PathContract adjacency cost W K) (hW : 1 ≤ W) (s t : Fin n) :
    (rejectPair adjacency (cost s) s t).2 ≤ pairBound W K := by
  have hp := h.charge s t
  unfold rejectPair
  dsimp only
  split
  · unfold pairBound
    omega
  · rename_i q hq
    have hs := h.stored s t q hq
    have hone : StoredBounded BinaryRational.one W := by
      simpa only [StoredBounded, BinaryRational.one, List.length_cons,
        List.length_nil, Nat.zero_add] using And.intro hW hW
    have hc := BinaryRational.le_charge hone hs
    unfold pairBound
    omega

theorem scan_charge (adjacency : Adjacency n) (cost : Fin n → Cost n)
    (h : PathContract adjacency cost W K) (hW : 1 ≤ W) (ds : List (Pair n)) :
    (WeightedEmptyCutDecision.scan adjacency cost ds).2 ≤ scanBound ds.length W K := by
  induction ds with
  | nil => simp [WeightedEmptyCutDecision.scan, scanBound]
  | cons d ds ih =>
      have hp := rejectPair_charge adjacency cost h hW d.1 d.2
      simp only [WeightedEmptyCutDecision.scan, List.length_cons]
      unfold scanBound at *
      nlinarith

theorem decideEmpty_charge (adjacency : Adjacency n) (cost : Fin n → Cost n)
    (h : PathContract adjacency cost W K) (hW : 1 ≤ W) :
    (decideEmpty adjacency cost).2 ≤ decisionBound n W K := by
  have hc := scan_charge adjacency cost h hW (RetainedTapeInput.allPairs n)
  simpa only [decideEmpty, decisionBound, RetainedTapeInput.allPairs, List.length_ofFn]
    using hc

/-- The output path is a real simple path, so its retained edge list is short. -/
theorem shortest_edges_length (adjacency : Adjacency n) (cost : Cost n) (s t : Fin n)
    {q : Candidate n}
    (hq : (shortest (ResidualSearch.Enumeration.fin n) adjacency cost s t).1 = some q) :
    q.edges.length < n := by
  obtain ⟨p, he, _hp⟩ := BinaryFractionalWalkOracle.shortest_valid
    (ResidualSearch.Enumeration.fin n) adjacency cost s t hq
  change q.edges = FlowTable.edgeList p at he
  rw [he, FlowTable.edgeList_length]
  simpa only [Fintype.card_fin] using p.edgeLength_lt_card

/-- Stored fraction padding is included. Label width is a semantic size bound;
the fixed-body label representation is not assumed by this theorem. -/
theorem returned_fields (adjacency : Adjacency n) (cost : Fin n → Cost n)
    (h : PathContract adjacency cost W K) (s t : Fin n) {q : Candidate n}
    (hq : (shortest (ResidualSearch.Enumeration.fin n) adjacency (cost s) s t).1 = some q) :
    q.edges.length < n ∧ q.cost.num.length ≤ W ∧ q.cost.den.length ≤ W ∧
      ∀ e ∈ q.edges, Nat.size e.1.val ≤ Nat.size n ∧ Nat.size e.2.val ≤ Nat.size n := by
  exact ⟨shortest_edges_length adjacency (cost s) s t hq, (h.stored s t q hq).1,
    (h.stored s t q hq).2, fun e _ =>
      ⟨Nat.size_le_size e.1.isLt.le, Nat.size_le_size e.2.isLt.le⟩⟩

theorem edgeCost_value (w : EdgeInput n) (e : Pair n) :
    (edgeCost w e).1 = w[e.1.val][e.2.val] := rfl

theorem edgeCost_charge (w : EdgeInput n) (e : Pair n) : (edgeCost w e).2 = 18 := rfl

theorem edgeCost_stored (w : EdgeInput n)
    (hw : ∀ e : Pair n, StoredBounded w[e.1.val][e.2.val] B) (e : Pair n) :
    StoredBounded (edgeCost w e).1 B := hw e

/-- The semantic conclusion and composed charge describe the same edge run. -/
theorem edgeDecision_contract (adjacency : Adjacency n) (w : EdgeInput n)
    (h : PathContract adjacency (fun _ => edgeCost w) W K) (hW : 1 ≤ W) :
    ((edgeDecision adjacency w).1 = true ↔
      IsIntegralEdgeCut (graph adjacency) ∅
        (edgeThresholdDemands (graph adjacency) (edgeWeights (edgeCost w)))) ∧
      (edgeDecision adjacency w).2 ≤ decisionBound n W K :=
  ⟨edgeDecision_correct adjacency w,
    decideEmpty_charge adjacency (fun _ => edgeCost w) h hW⟩

/-- The semantic conclusion and composed charge describe the same vertex run. -/
theorem vertexDecision_contract (adjacency : Adjacency n) (w : BinaryFractionalRows.Row n)
    (h : PathContract adjacency (BinaryFractionalGraphOracle.outgoing w) W K)
    (hW : 1 ≤ W) :
    ((vertexDecision adjacency w).1 = true ↔
      IsIntegralCut (graph adjacency) ∅
        (thresholdDemands (graph adjacency) (vertexWeights w))) ∧
      (vertexDecision adjacency w).2 ≤ decisionBound n W K :=
  ⟨vertexDecision_correct adjacency w,
    decideEmpty_charge adjacency (BinaryFractionalGraphOracle.outgoing w) h hW⟩

theorem edgeEntry_charge (adjacency : Adjacency n) (w : EdgeInput n)
    (h : PathContract adjacency (fun _ => edgeCost w) W K) (hW : 1 ≤ W) :
    (edgeEntry adjacency w).2 ≤ decisionBound n W K + 4 :=
  Nat.add_le_add_right (decideEmpty_charge adjacency (fun _ => edgeCost w) h hW) 4

theorem vertexEntry_charge (adjacency : Adjacency n) (w : BinaryFractionalRows.Row n)
    (h : PathContract adjacency (BinaryFractionalGraphOracle.outgoing w) W K)
    (hW : 1 ≤ W) : (vertexEntry adjacency w).2 ≤ decisionBound n W K + 4 :=
  Nat.add_le_add_right
    (decideEmpty_charge adjacency (BinaryFractionalGraphOracle.outgoing w) h hW) 4

end DirectedFlowCutGap.WeightedEmptyCutBounds
