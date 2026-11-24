import DirectedFlowCutGap.MeasuredPathMembership
import DirectedFlowCutGap.MeasuredBudgetPrices
import DirectedFlowCutGap.RationalSparsestVertexDistances
import DirectedFlowCutGap.ConcurrentEdgeCoverWidths
import DirectedFlowCutGap.BinaryFractionalWalkBounds

/-! Retain the exact threshold distances in the measured binary form used
to decide free-resource and rounding branches. -/
namespace DirectedFlowCutGap.MeasuredSparsestDistances

open scoped NNRat
open IntegralNetworkFlow
open BinaryFractionalWalkOracle (Adjacency Candidate shortest)
open BinaryFractionalWalkBounds (shortestBound shortest_stored shortest_charge stored_mono zero_stored)
open BinaryRational (StoredBounded zero)
open ConcurrentEdgeOracle (Edge)
open ConcurrentEdgeCoverWidths (MatrixFits)
open RationalEdgeThresholds (Weights cost)
open RawNonnegativeRational (Code)

variable {n m : ℕ}

private def readPath (path : Option (Candidate n) × ℕ) : Option Code × ℕ :=
  match path.1 with
  | none => (none,path.2+1)
  | some p =>
    let read := BinaryRawRational.decode p.cost
    (some read.1,path.2+read.2+1)

def edge (A : Adjacency n) (w : Weights n) (d : Edge n) : Option Code × ℕ :=
  readPath (shortest (ResidualSearch.Enumeration.fin n) A (cost w) d.1 d.2)

theorem edge_value (A : Adjacency n) (w : Weights n) (d : Edge n) :
    (edge A w d).1.map Code.value = RationalSparsestEdgeDistances.distance A w d := by
  cases found : (shortest (ResidualSearch.Enumeration.fin n) A (cost w) d.1 d.2).1 <;>
    simp only [edge,readPath,RationalSparsestEdgeDistances.distance,found,
      Option.map_none,Option.map_some,BinaryRawRational.decode_value]

def distanceWidth (n B : ℕ) : ℕ := n*(B+1)+1

def edgeWork (n B : ℕ) : ℕ := shortestBound n B 2+40*(distanceWidth n B+1)^2+1

def OptionFits (q : Option Code) (B : ℕ) : Prop := ∀ p, q = some p → p.Bounded B

theorem edge_bounds (A : Adjacency n) (w : Weights n) (d : Edge n) {B : ℕ} (fit : MatrixFits w B) :
    OptionFits (edge A w d).1 (distanceWidth n B) ∧ (edge A w d).2 ≤ edgeWork n B := by
  let trace := shortest (ResidualSearch.Enumeration.fin n) A (cost w) d.1 d.2
  have each (e : Edge n) : StoredBounded ((cost w) e).1 B := fit e.1 e.2
  have paid : trace.2 ≤ shortestBound n B 2 :=
    shortest_charge _ A (cost w) each (fun _ => le_rfl) d.1 d.2
  change OptionFits (readPath trace).1 (distanceWidth n B) ∧ (readPath trace).2 ≤ edgeWork n B
  unfold edgeWork
  cases h : trace.1 with
  | none =>
    simp only [readPath,h]
    constructor
    · intro p impossible
      cases impossible
    · omega
  | some p =>
    simp only [readPath,h]
    have width : StoredBounded p.cost (distanceWidth n B) :=
      shortest_stored _ A (cost w) each d.1 d.2 p h
    constructor
    · intro q shown
      cases shown
      rw [BinaryRawRational.decode_value]
      exact BinaryFractionalRows.stored_raw_bound width
    · have read := BinaryRawRational.decode_paid width
      omega

private def vertexRow (w : BinaryFractionalRows.Row n) (s u : Fin n) :
    Vector BinaryRational.Fraction n × ℕ :=
  let test := MeasuredPathMembership.sameVertex u s
  (Vector.replicate n (if test.1 then zero else w.get u),test.2+4)

def outgoing (w : BinaryFractionalRows.Row n) (s : Fin n) : Weights n × ℕ :=
  MeasuredBudgetPrices.tabulate (vertexRow w s)

theorem outgoing_value (w : BinaryFractionalRows.Row n) (s : Fin n) :
    (outgoing w s).1 = RationalSparsestVertexDistances.outgoing w s := by
  apply Vector.ext
  intro i hi
  simp only [outgoing,MeasuredBudgetPrices.tabulate_value,RationalSparsestVertexDistances.outgoing,
    Vector.getElem_ofFn,vertexRow]
  by_cases same : (⟨i,hi⟩ : Fin n) = s
  · rw [ite_eq_left ((MeasuredPathMembership.sameVertex_value _ _).mpr same),ite_eq_left same]
  · rw [ite_eq_right (fun t => same ((MeasuredPathMembership.sameVertex_value _ _).mp t)),ite_eq_right same]
    rfl

theorem outgoing_bounds (w : BinaryFractionalRows.Row n) (s : Fin n) {B : ℕ}
    (fit : ∀ i, StoredBounded (w.get i) B) :
    MatrixFits (outgoing w s).1 (max 1 B) ∧
      (outgoing w s).2 ≤ n*(MeasuredPathMembership.vertexComparisonWork n.size+4) := by
  constructor
  · rw [outgoing_value]
    intro u v
    change StoredBounded ((RationalSparsestVertexDistances.outgoing w s)[u.val][v.val]) _
    simp only [RationalSparsestVertexDistances.outgoing,Vector.getElem_ofFn,Vector.getElem_replicate,Fin.eta]
    split
    · exact stored_mono zero_stored (le_max_left ..)
    · exact stored_mono (fit u) (le_max_right ..)
  · apply MeasuredBudgetPrices.tabulate_charge
    intro u
    exact Nat.add_le_add_right
      (MeasuredPathMembership.sameVertex_charge u s (Nat.size_le_size u.isLt.le) (Nat.size_le_size s.isLt.le)) 4

def vertex (A : Adjacency n) (w : BinaryFractionalRows.Row n) (d : Edge n) : Option Code × ℕ :=
  let lifted := outgoing w d.1
  let distance := edge A lifted.1 d
  (distance.1,lifted.2+distance.2)

theorem vertex_value (A : Adjacency n) (w : BinaryFractionalRows.Row n) (d : Edge n) :
    (vertex A w d).1.map Code.value = RationalSparsestVertexDistances.distance A w d := by
  simp only [vertex,edge_value,outgoing_value,RationalSparsestVertexDistances.distance]

def vertexWork (n B : ℕ) : ℕ :=
  n*(MeasuredPathMembership.vertexComparisonWork n.size+4)+edgeWork n (max 1 B)

theorem vertex_bounds (A : Adjacency n) (w : BinaryFractionalRows.Row n) (d : Edge n) {B : ℕ}
    (fit : ∀ i, StoredBounded (w.get i) B) :
    OptionFits (vertex A w d).1 (distanceWidth n (max 1 B)) ∧ (vertex A w d).2 ≤ vertexWork n B := by
  obtain ⟨lifted,liftWork⟩ := outgoing_bounds w d.1 fit
  obtain ⟨stored,pathWork⟩ := edge_bounds A (outgoing w d.1).1 d lifted
  exact ⟨stored,Nat.add_le_add liftWork pathWork⟩

end DirectedFlowCutGap.MeasuredSparsestDistances
