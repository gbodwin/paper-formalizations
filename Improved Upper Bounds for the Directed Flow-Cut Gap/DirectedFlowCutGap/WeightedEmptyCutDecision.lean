import DirectedFlowCutGap.BinaryFractionalGraphOracle
import DirectedFlowCutGap.RetainedTapeInput
import DirectedFlowCutGap.VertexGridDistances

/-!
# Deterministic empty-cut decision at the original weighted threshold

The program scans every ordered pair in the original graph. It rejects the
empty cut precisely when the binary shortest-path program returns a reachable
path of minimum original weight at least one. An unreachable result is ignored,
even though that pair belongs to the extended-distance threshold demands.

The edge and endpoint-excluding vertex entry points use the supplied fractions
unchanged. No scaling, rounding, replication, or normalization of the metric or
its total weight is performed. Rational and real interpretations occur only in
proofs. Charges here instrument the actual calls and Boolean/list scan; the
separate bounds module states exactly which representation joins remain.
-/
namespace DirectedFlowCutGap.WeightedEmptyCutDecision

open scoped BigOperators NNReal
open BinaryRational BinaryFractionalWalkOracle
open IntegralNetworkFlow
open FractionalCoverWalkOracle (pathCost)

variable {n : ℕ}

/-- Exact rational interpretation; never used to control the program. -/
def rationalCost (cost : Cost n) (e : Pair n) : ℚ :=
  FractionalCoverRawCore.rational (decodeCost cost e)

def interpret (q : Candidate n) : FractionalCoverWalkOracle.Candidate (Fin n) :=
  FractionalCoverRawOracle.decode (BinaryFractionalWalkOracle.decode q)

theorem shortest_refines (adjacency : Adjacency n) (cost : Cost n) (s t : Fin n) :
    (shortest (ResidualSearch.Enumeration.fin n) adjacency cost s t).1.map interpret =
      (FractionalCoverPathOracle.shortest (ResidualSearch.Enumeration.fin n)
        (graph adjacency) (rationalCost cost) s t).1 := by
  have hb := shortest_decode (ResidualSearch.Enumeration.fin n) adjacency cost s t
  have hr := congrArg Prod.fst (FractionalCoverRawOracle.shortest_refines
    (ResidualSearch.Enumeration.fin n) (graph adjacency) (decodeCost cost) s t)
  change ((FractionalCoverRawOracle.shortest (ResidualSearch.Enumeration.fin n)
    (graph adjacency) (decodeCost cost) s t).1.map FractionalCoverRawOracle.decode) = _ at hr
  rw [← hb, Option.map_map] at hr
  exact hr

/-- Absence is certified unreachability, including zero-cost graphs. -/
theorem shortest_none_iff (adjacency : Adjacency n) (cost : Cost n) (s t : Fin n) :
    (shortest (ResidualSearch.Enumeration.fin n) adjacency cost s t).1 = none ↔
      ¬Nonempty (SimplePath (graph adjacency) s t) := by
  have h := FractionalCoverPathOracle.shortest_none_iff
    (ResidualSearch.Enumeration.fin n) (graph adjacency) (rationalCost cost)
    (fun e => FractionalCoverRawCore.rational_nonneg (decodeCost cost e)) s t
  rw [← shortest_refines adjacency cost s t] at h
  simpa only [Option.map_eq_none_iff] using h

/-- The cost of the actual retained result is below every original simple path. -/
theorem shortest_minimum (adjacency : Adjacency n) (cost : Cost n) (s t : Fin n)
    {q : Candidate n}
    (hq : (shortest (ResidualSearch.Enumeration.fin n) adjacency cost s t).1 = some q)
    (p : SimplePath (graph adjacency) s t) :
    FractionalCoverRawCore.rational (BinaryRational.decode q.cost) ≤
      pathCost (rationalCost cost) p := by
  have hr := shortest_refines adjacency cost s t
  rw [hq, Option.map_some] at hr
  obtain ⟨r, hr', hle⟩ := FractionalCoverPathOracle.shortest_minimum
    (ResidualSearch.Enumeration.fin n) (graph adjacency) (rationalCost cost)
    (fun e => FractionalCoverRawCore.rational_nonneg (decodeCost cost e)) s t p
  have he : interpret q = r := Option.some.inj (hr.trans hr')
  simpa only [← he, interpret, FractionalCoverRawOracle.decode,
    BinaryFractionalWalkOracle.decode] using hle

/-- True is a reachable rejection witness. None deliberately returns false. -/
def rejectPair (adjacency : Adjacency n) (cost : Cost n) (s t : Fin n) : Bool × ℕ :=
  let p := shortest (ResidualSearch.Enumeration.fin n) adjacency cost s t
  match p.1 with
  | none => (false, p.2 + 4)
  | some q =>
      let test := BinaryRational.le BinaryRational.one q.cost
      (test.1, p.2 + test.2 + 6)

theorem rejectPair_true_iff (adjacency : Adjacency n) (cost : Cost n) (s t : Fin n) :
    (rejectPair adjacency cost s t).1 = true ↔
      Nonempty (SimplePath (graph adjacency) s t) ∧
        ∀ p : SimplePath (graph adjacency) s t, 1 ≤ pathCost (rationalCost cost) p := by
  cases hq : (shortest (ResidualSearch.Enumeration.fin n) adjacency cost s t).1 with
  | none =>
      have hn := (shortest_none_iff adjacency cost s t).mp hq
      simp only [rejectPair, hq, Bool.false_eq_true, false_iff]
      exact fun h => hn h.1
  | some q =>
      obtain ⟨p, _he, hp⟩ := BinaryFractionalWalkOracle.shortest_valid
        (ResidualSearch.Enumeration.fin n) adjacency cost s t hq
      have hcost : FractionalCoverRawCore.rational (BinaryRational.decode q.cost) =
          pathCost (rationalCost cost) p := hp
      simp only [rejectPair, hq, BinaryRational.le_decode, BinaryRational.decode_one,
        FractionalCoverRawCore.code_le_iff, FractionalCoverRawCore.rational_one]
      constructor
      · intro h
        exact ⟨⟨p⟩, fun r => h.trans (shortest_minimum adjacency cost s t hq r)⟩
      · intro h
        rw [hcost]
        exact h.2 p

theorem rejectPair_unreachable (adjacency : Adjacency n) (cost : Cost n) (s t : Fin n)
    (h : ¬Nonempty (SimplePath (graph adjacency) s t)) :
    (rejectPair adjacency cost s t).1 = false := by
  simp only [rejectPair, (shortest_none_iff adjacency cost s t).mpr h]

/-- Every pair is checked once; the accumulator is only one Boolean. -/
def scan (adjacency : Adjacency n) (cost : Fin n → Cost n) :
    List (Pair n) → Bool × ℕ
  | [] => (true, 1)
  | d :: ds =>
      let p := rejectPair adjacency (cost d.1) d.1 d.2
      let tail := scan adjacency cost ds
      (!p.1 && tail.1, p.2 + tail.2 + 4)

theorem scan_true_iff (adjacency : Adjacency n) (cost : Fin n → Cost n)
    (ds : List (Pair n)) :
    (scan adjacency cost ds).1 = true ↔
      ∀ d ∈ ds, (rejectPair adjacency (cost d.1) d.1 d.2).1 ≠ true := by
  induction ds with
  | nil => simp [scan]
  | cons d ds ih =>
      cases hp : (rejectPair adjacency (cost d.1) d.1 d.2).1 <;>
        simp [scan, hp, ih]

/-- The fixed original-label enumeration includes all pairs, including diagonals. -/
def decideEmpty (adjacency : Adjacency n) (cost : Fin n → Cost n) : Bool × ℕ :=
  scan adjacency cost (RetainedTapeInput.allPairs n)

theorem decideEmpty_true_iff (adjacency : Adjacency n) (cost : Fin n → Cost n) :
    (decideEmpty adjacency cost).1 = true ↔
      ∀ s t, ¬(Nonempty (SimplePath (graph adjacency) s t) ∧
        ∀ p : SimplePath (graph adjacency) s t, 1 ≤ pathCost (rationalCost (cost s)) p) := by
  rw [decideEmpty, scan_true_iff]
  constructor
  · intro h s t
    exact fun hr => h (s,t) (RetainedTapeInput.mem_allPairs (s,t))
      ((rejectPair_true_iff adjacency (cost s) s t).mpr hr)
  · intro h d _hd hr
    exact h d.1 d.2 ((rejectPair_true_iff adjacency (cost d.1) d.1 d.2).mp hr)

/-- Semantic view of the original binary fraction. -/
noncomputable def realValue (q : Fraction) : ℝ≥0 :=
  ⟨(FractionalCoverRawCore.rational (BinaryRational.decode q) : ℝ),
    by exact_mod_cast FractionalCoverRawCore.rational_nonneg (BinaryRational.decode q)⟩

noncomputable def edgeWeights (cost : Cost n) : Pair n → ℝ≥0 :=
  fun e => realValue (cost e).1

theorem pathCost_threshold_iff (adjacency : Adjacency n) (cost : Cost n)
    {s t : Fin n} (p : SimplePath (graph adjacency) s t) :
    1 ≤ pathCost (rationalCost cost) p ↔ 1 ≤ p.edgeWeight (edgeWeights cost) := by
  have he : ((p.edgeWeight (edgeWeights cost) : ℝ≥0) : ℝ) =
      (pathCost (rationalCost cost) p : ℝ) := by
    change NNReal.toRealHom (∑ e ∈ p.edges, edgeWeights cost e) =
      ((∑ e ∈ p.edges, rationalCost cost e : ℚ) : ℝ)
    rw [map_sum, Rat.cast_sum]
    rfl
  rw [← NNReal.coe_le_coe, NNReal.coe_one, he]
  exact_mod_cast (Iff.rfl : (1 : ℚ) ≤ pathCost (rationalCost cost) p ↔
    (1 : ℚ) ≤ pathCost (rationalCost cost) p)

theorem rejectPair_metric_iff (adjacency : Adjacency n) (cost : Cost n) (s t : Fin n) :
    (rejectPair adjacency cost s t).1 = true ↔
      Nonempty (SimplePath (graph adjacency) s t) ∧
        (s,t) ∈ edgeThresholdDemands (graph adjacency) (edgeWeights cost) := by
  rw [rejectPair_true_iff]
  change _ ↔ _ ∧ 1 ≤ edgeDistance (graph adjacency) (edgeWeights cost) s t
  rw [← ENNReal.coe_one, coe_le_edgeDistance_iff]
  simp_rw [pathCost_threshold_iff]

/-- Edge weights are read from the original retained matrix, including padding. -/
abbrev EdgeInput (n : ℕ) := Vector (Vector Fraction n) n

def edgeCost (w : EdgeInput n) (e : Pair n) : Fraction × ℕ :=
  let row := EncodedArrayStorage.readCallback w e.1
  let cell := EncodedArrayStorage.readCallback row.1 e.2
  (cell.1, row.2 + cell.2 + 4)

def edgeDecision (adjacency : Adjacency n) (w : EdgeInput n) : Bool × ℕ :=
  decideEmpty adjacency (fun _ => edgeCost w)

theorem edgeDecision_correct (adjacency : Adjacency n) (w : EdgeInput n) :
    (edgeDecision adjacency w).1 = true ↔
      IsIntegralEdgeCut (graph adjacency) ∅
        (edgeThresholdDemands (graph adjacency) (edgeWeights (edgeCost w))) := by
  rw [edgeDecision, decideEmpty, scan_true_iff]
  constructor
  · intro h s t hd p
    exact False.elim (h (s,t) (RetainedTapeInput.mem_allPairs (s,t))
      ((rejectPair_metric_iff adjacency (edgeCost w) s t).mpr ⟨⟨p⟩, hd⟩))
  · intro h d _hd hr
    obtain ⟨⟨p⟩, hd⟩ := (rejectPair_metric_iff adjacency (edgeCost w) d.1 d.2).mp hr
    obtain ⟨e, _he, hx⟩ := h d.1 d.2 hd p
    exact Finset.notMem_empty e hx

noncomputable def vertexWeights (w : BinaryFractionalRows.Row n) : Fin n → ℝ≥0 :=
  fun v => realValue (BinaryFractionalRows.get w v)

theorem outgoing_weights (w : BinaryFractionalRows.Row n) (s : Fin n) :
    edgeWeights (BinaryFractionalGraphOracle.outgoing w s) =
      VertexGridDistances.outgoingWeight (vertexWeights w) s := by
  funext e
  unfold BinaryFractionalGraphOracle.outgoing edgeWeights
  dsimp only
  split
  · simp [VertexGridDistances.outgoingWeight, *, realValue]
    rfl
  · simp [VertexGridDistances.outgoingWeight, *, BinaryFractionalGraphOracle.read_value,
      vertexWeights]

def vertexDecision (adjacency : Adjacency n) (w : BinaryFractionalRows.Row n) : Bool × ℕ :=
  decideEmpty adjacency (BinaryFractionalGraphOracle.outgoing w)

/-- Both demand endpoints are excluded, including direct and diagonal paths. -/
theorem vertexDecision_correct (adjacency : Adjacency n) (w : BinaryFractionalRows.Row n) :
    (vertexDecision adjacency w).1 = true ↔
      IsIntegralCut (graph adjacency) ∅ (thresholdDemands (graph adjacency) (vertexWeights w)) := by
  have hm (s t : Fin n) :
      (rejectPair adjacency (BinaryFractionalGraphOracle.outgoing w s) s t).1 = true ↔
        Nonempty (SimplePath (graph adjacency) s t) ∧
          (s,t) ∈ thresholdDemands (graph adjacency) (vertexWeights w) := by
    rw [rejectPair_metric_iff, outgoing_weights]
    simp only [edgeThresholdDemands, thresholdDemands, Set.mem_ofPred_eq,
      VertexGridDistances.edgeDistance_eq_vertexDistance]
  rw [vertexDecision, decideEmpty, scan_true_iff]
  constructor
  · intro h s t hd p
    exact False.elim (h (s,t) (RetainedTapeInput.mem_allPairs (s,t))
      ((hm s t).mpr ⟨⟨p⟩, hd⟩))
  · intro h d _hd hr
    obtain ⟨⟨p⟩, hd⟩ := (hm d.1 d.2).mp hr
    obtain ⟨v, _hv, hx⟩ := h d.1 d.2 hd p
    exact Finset.notMem_empty v hx

/-- Deterministic entry branch: some [] returns the empty edge cut; none passes
control to the nonempty-cut construction. No random query occurs in this body. -/
def edgeEntry (adjacency : Adjacency n) (w : EdgeInput n) : Option (List (Pair n)) × ℕ :=
  let d := edgeDecision adjacency w
  (if d.1 then some [] else none, d.2 + 4)

theorem edgeEntry_empty_iff (adjacency : Adjacency n) (w : EdgeInput n) :
    (edgeEntry adjacency w).1 = some [] ↔
      IsIntegralEdgeCut (graph adjacency) ∅
        (edgeThresholdDemands (graph adjacency) (edgeWeights (edgeCost w))) := by
  rw [← edgeDecision_correct]
  cases h : (edgeDecision adjacency w).1 <;> simp [edgeEntry, h]

/-- The endpoint-excluding vertex entry uses the same deterministic branch. -/
def vertexEntry (adjacency : Adjacency n) (w : BinaryFractionalRows.Row n) :
    Option (List (Fin n)) × ℕ :=
  let d := vertexDecision adjacency w
  (if d.1 then some [] else none, d.2 + 4)

theorem vertexEntry_empty_iff (adjacency : Adjacency n) (w : BinaryFractionalRows.Row n) :
    (vertexEntry adjacency w).1 = some [] ↔
      IsIntegralCut (graph adjacency) ∅ (thresholdDemands (graph adjacency) (vertexWeights w)) := by
  rw [← vertexDecision_correct]
  cases h : (vertexDecision adjacency w).1 <;> simp [vertexEntry, h]

end DirectedFlowCutGap.WeightedEmptyCutDecision
