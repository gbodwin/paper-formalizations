import DirectedFlowCutGap.WeightedEmptyCutBounds
import DirectedFlowCutGap.BinaryFractionalGraphBounds

/-!
# Concrete instrumented bounds for the original-weight empty-cut entry

This companion discharges `PathContract` with the actual binary shortest-path
program and its retained matrix/row reads. The only input hypotheses are bounds
on the supplied numerator and denominator list lengths, including padding.
There is no assumed oracle runtime, minimum witness, positive vertex count,
metric normalization, or replacement of the original total weight.

The resulting bounds count the binary arithmetic and retained Boolean/list
instructions already charged by the imported program. `allPairs` materialization
and the fixed-body label/address/storage simulation remain separate joins. In
particular, this does not turn the constant-charge retained read callback into
a certified physical-machine read or supply a free encoding of Fin labels.
-/
namespace DirectedFlowCutGap.WeightedEmptyCutRuntime

open BinaryRational BinaryFractionalWalkOracle WeightedEmptyCutDecision
open IntegralNetworkFlow
variable {n B : ℕ}

def edgeWidth (n B : ℕ) : ℕ := n * (B + 1) + 1
def vertexWidth (n B : ℕ) : ℕ := n * (B + 2) + 1

def edgeEntryBound (n B : ℕ) : ℕ :=
  WeightedEmptyCutBounds.decisionBound n (edgeWidth n B)
    (BinaryFractionalWalkBounds.shortestBound n B 18) + 4

def vertexEntryBound (n B : ℕ) : ℕ :=
  WeightedEmptyCutBounds.decisionBound n (vertexWidth n B)
    (BinaryFractionalWalkBounds.shortestBound n (B + 1) 13) + 4

@[simp] theorem edgeEntryBound_zero (B : ℕ) : edgeEntryBound 0 B = 5 := by
  simp [edgeEntryBound, WeightedEmptyCutBounds.decisionBound, WeightedEmptyCutBounds.scanBound]

@[simp] theorem vertexEntryBound_zero (B : ℕ) : vertexEntryBound 0 B = 5 := by
  simp [vertexEntryBound, WeightedEmptyCutBounds.decisionBound, WeightedEmptyCutBounds.scanBound]

/-- Two actual retained matrix reads cost 18; all original padded fields have
their supplied bound B. No nonedge weight is introduced into a path. -/
theorem edgePathContract (adjacency : Adjacency n) (w : EdgeInput n)
    (hw : ∀ e : Pair n, StoredBounded w[e.1.val][e.2.val] B) :
    WeightedEmptyCutBounds.PathContract adjacency (fun _ => edgeCost w)
      (edgeWidth n B) (BinaryFractionalWalkBounds.shortestBound n B 18) := by
  constructor
  · intro s t
    exact BinaryFractionalWalkBounds.shortest_charge (ResidualSearch.Enumeration.fin n)
      adjacency (edgeCost w) (WeightedEmptyCutBounds.edgeCost_stored w hw)
      (fun e => (WeightedEmptyCutBounds.edgeCost_charge w e).le) s t
  · intro s t q hq
    exact BinaryFractionalWalkBounds.shortest_stored (ResidualSearch.Enumeration.fin n)
      adjacency (edgeCost w) (WeightedEmptyCutBounds.edgeCost_stored w hw) s t q hq

/-- The existing source-zero adapter uses width B+1 and charge at most 13.
Its recovered path therefore has width n*(B+2)+1. -/
theorem vertexPathContract (adjacency : Adjacency n) (w : BinaryFractionalRows.Row n)
    (hw : ∀ i, StoredBounded (BinaryFractionalRows.get w i) B) :
    WeightedEmptyCutBounds.PathContract adjacency (BinaryFractionalGraphOracle.outgoing w)
      (vertexWidth n B) (BinaryFractionalWalkBounds.shortestBound n (B + 1) 13) := by
  constructor
  · intro s t
    exact BinaryFractionalWalkBounds.shortest_charge (ResidualSearch.Enumeration.fin n)
      adjacency (BinaryFractionalGraphOracle.outgoing w s)
      (BinaryFractionalGraphBounds.outgoing_stored w hw s)
      (BinaryFractionalGraphBounds.outgoing_charge w s) s t
  · intro s t q hq
    exact BinaryFractionalWalkBounds.shortest_stored (ResidualSearch.Enumeration.fin n)
      adjacency (BinaryFractionalGraphOracle.outgoing w s)
      (BinaryFractionalGraphBounds.outgoing_stored w hw s) s t q hq

theorem edgeEntry_charge (adjacency : Adjacency n) (w : EdgeInput n)
    (hw : ∀ e : Pair n, StoredBounded w[e.1.val][e.2.val] B) :
    (edgeEntry adjacency w).2 ≤ edgeEntryBound n B :=
  WeightedEmptyCutBounds.edgeEntry_charge adjacency w (edgePathContract adjacency w hw)
    (by unfold edgeWidth; omega)

theorem vertexEntry_charge (adjacency : Adjacency n) (w : BinaryFractionalRows.Row n)
    (hw : ∀ i, StoredBounded (BinaryFractionalRows.get w i) B) :
    (vertexEntry adjacency w).2 ≤ vertexEntryBound n B :=
  WeightedEmptyCutBounds.vertexEntry_charge adjacency w (vertexPathContract adjacency w hw)
    (by unfold vertexWidth; omega)

/-- Semantic correctness and the concrete charge refer to the very same run. -/
theorem edgeEntry_contract (adjacency : Adjacency n) (w : EdgeInput n)
    (hw : ∀ e : Pair n, StoredBounded w[e.1.val][e.2.val] B) :
    ((edgeEntry adjacency w).1 = some [] ↔
      IsIntegralEdgeCut (graph adjacency) ∅
        (edgeThresholdDemands (graph adjacency) (edgeWeights (edgeCost w)))) ∧
      (edgeEntry adjacency w).2 ≤ edgeEntryBound n B :=
  ⟨edgeEntry_empty_iff adjacency w, edgeEntry_charge adjacency w hw⟩

theorem vertexEntry_contract (adjacency : Adjacency n) (w : BinaryFractionalRows.Row n)
    (hw : ∀ i, StoredBounded (BinaryFractionalRows.get w i) B) :
    ((vertexEntry adjacency w).1 = some [] ↔
      IsIntegralCut (graph adjacency) ∅
        (thresholdDemands (graph adjacency) (vertexWeights w))) ∧
      (vertexEntry adjacency w).2 ≤ vertexEntryBound n B :=
  ⟨vertexEntry_empty_iff adjacency w, vertexEntry_charge adjacency w hw⟩

/-- The stored-field conclusion includes all padding actually returned. -/
theorem edge_returned_fields (adjacency : Adjacency n) (w : EdgeInput n)
    (hw : ∀ e : Pair n, StoredBounded w[e.1.val][e.2.val] B) (s t : Fin n)
    {q : Candidate n}
    (hq : (shortest (ResidualSearch.Enumeration.fin n) adjacency (edgeCost w) s t).1 = some q) :
    q.edges.length < n ∧ q.cost.num.length ≤ edgeWidth n B ∧
      q.cost.den.length ≤ edgeWidth n B ∧
        ∀ e ∈ q.edges, Nat.size e.1.val ≤ Nat.size n ∧ Nat.size e.2.val ≤ Nat.size n :=
  WeightedEmptyCutBounds.returned_fields adjacency (fun _ => edgeCost w)
    (edgePathContract adjacency w hw) s t hq

theorem vertex_returned_fields (adjacency : Adjacency n) (w : BinaryFractionalRows.Row n)
    (hw : ∀ i, StoredBounded (BinaryFractionalRows.get w i) B) (s t : Fin n)
    {q : Candidate n}
    (hq : (shortest (ResidualSearch.Enumeration.fin n) adjacency
      (BinaryFractionalGraphOracle.outgoing w s) s t).1 = some q) :
    q.edges.length < n ∧ q.cost.num.length ≤ vertexWidth n B ∧
      q.cost.den.length ≤ vertexWidth n B ∧
        ∀ e ∈ q.edges, Nat.size e.1.val ≤ Nat.size n ∧ Nat.size e.2.val ≤ Nat.size n :=
  WeightedEmptyCutBounds.returned_fields adjacency (BinaryFractionalGraphOracle.outgoing w)
    (vertexPathContract adjacency w hw) s t hq

/-- No vertex means no shortest-path calls; the literal empty edge entry costs 5. -/
theorem edgeEntry_zero (adjacency : Adjacency 0) (w : EdgeInput 0) :
    edgeEntry adjacency w = (some [], 5) := by
  simp [edgeEntry, edgeDecision, decideEmpty, RetainedTapeInput.allPairs,
    WeightedEmptyCutDecision.scan]

theorem vertexEntry_zero (adjacency : Adjacency 0) (w : BinaryFractionalRows.Row 0) :
    vertexEntry adjacency w = (some [], 5) := by
  simp [vertexEntry, vertexDecision, decideEmpty, RetainedTapeInput.allPairs,
    WeightedEmptyCutDecision.scan]

end DirectedFlowCutGap.WeightedEmptyCutRuntime
