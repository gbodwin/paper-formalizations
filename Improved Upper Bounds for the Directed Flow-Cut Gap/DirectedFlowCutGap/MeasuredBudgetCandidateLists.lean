import DirectedFlowCutGap.MeasuredBudgetCoverCandidate
import DirectedFlowCutGap.ConcurrentVertexBudgetGrid
import DirectedFlowCutGap.ConcurrentEdgeBudgetWidths

/-! Retain the measured work of every covering candidate in the original
price-and-mass grid. Grid construction and final selection are separate. -/
namespace DirectedFlowCutGap.MeasuredBudgetCandidateLists

open scoped BigOperators NNRat
open BinaryFractionalWalkOracle (Adjacency)
open BinaryRational (StoredBounded)
open ConcurrentEdgeOracle (Edge)
open ConcurrentEdgeCoverWidths (MatrixFits)
open RationalEdgeThresholds (Weights)
open RawNonnegativeRational (Code)
open NNRatStoredBounds (Bounded mono one_bounded mul_bounded sum_bounded value_bounded)
open ConcurrentEdgeBudgetWidths (grid_length grid_item)

variable {n m : ℕ}

def collect {α : Type*} (solve : Code → Code → α × ℕ) (pairs : List (ℚ≥0 × ℚ≥0)) :
    List α × ℕ :=
  let reached := pairs.map fun p => solve (Code.ofNNRat p.1) (Code.ofNNRat p.2)
  (reached.map Prod.fst,(reached.map Prod.snd).sum)

theorem collect_charge {α : Type*} (solve : Code → Code → α × ℕ) (pairs : List (ℚ≥0 × ℚ≥0)) {W : ℕ}
    (each : ∀ p ∈ pairs, (solve (Code.ofNNRat p.1) (Code.ofNNRat p.2)).2 ≤ W) :
    (collect solve pairs).2 ≤ pairs.length*W := by
  induction pairs with
  | nil => simp [collect]
  | cons p ps ih =>
    have current := each p List.mem_cons_self
    have tail := ih (fun q hq => each q (List.mem_cons_of_mem _ hq))
    simpa only [collect,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm] using
      Nat.add_le_add current tail

private theorem nat_fits (q : ℕ) : Bounded (q : ℚ≥0) q := by
  have h : (Code.ofNat q).Bounded q := MeasuredMultiplicityUpdate.ofNat_fits Nat.lt_two_pow_self.le
  simpa only [Code.value_ofNat] using value_bounded h

private theorem product_fits {ι : Type*} (members : Finset ι) (p : ι → ℚ≥0) (B : ℕ)
    (fit : ∀ i ∈ members, Bounded (p i) B) : Bounded (∏ i ∈ members, p i) (members.card*B) := by
  classical
  induction members using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty,Finset.card_empty,Nat.zero_mul] using one_bounded
  | @insert i xs away ih =>
    rw [Finset.card_insert_of_notMem away,Finset.prod_insert away]
    have rest := ih (fun j hj => fit j (Finset.mem_insert_of_mem hj))
    simpa only [Nat.add_mul,Nat.one_mul,Nat.add_comm] using mul_bounded (fit i (Finset.mem_insert_self ..)) rest

private theorem vertexFloor_fits (c : BinaryFractionalRows.Row n) {B : ℕ}
    (fit : ∀ i, StoredBounded (c.get i) B) : Bounded (ConcurrentVertexBudget.floorPrice c) (n*B) := by
  have one := mono one_bounded (Nat.zero_le B)
  have member (i : Fin n) : Bounded (ConcurrentVertexBudget.floorFactor c i) B := by
    have q := value_bounded (BinaryFractionalRows.stored_raw_bound (fit i))
    unfold ConcurrentVertexBudget.floorFactor
    split
    · rcases le_total (1 : ℚ≥0) (ConcurrentVertexBudget.raw c i) with lower | upper
      · rwa [min_eq_left lower]
      · rw [min_eq_right upper]
        exact q
    · exact one
  simpa only [ConcurrentVertexBudget.floorPrice,Finset.card_univ,Fintype.card_fin] using
    product_fits (Finset.univ : Finset (Fin n)) _ B (fun i _ => member i)

private theorem vertexPrice_fits (c : BinaryFractionalRows.Row n) (m : ℕ) {B : ℕ}
    (fit : ∀ i, StoredBounded (c.get i) B) : Bounded (ConcurrentVertexBudget.priceCeiling c m) (m+n*(B+1)) := by
  have h : Bounded (∑ i : Fin n,ConcurrentVertexBudget.raw c i) (n*(B+1)) := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      sum_bounded (Finset.univ : Finset (Fin n)) (ConcurrentVertexBudget.raw c) B
        (fun i _ => value_bounded (BinaryFractionalRows.stored_raw_bound (fit i)))
  exact mul_bounded (nat_fits m) h

private theorem vertexMass_fits (n m : ℕ) : Bounded (ConcurrentVertexBudget.massCeiling n m) (m+n) :=
  mul_bounded (nat_fits m) (nat_fits n)

def vertexPriceWidth (n m B : ℕ) : ℕ := 2*(n*B)+(m+n*(B+1))+2
def vertexMassWidth (n m : ℕ) : ℕ := m+n+2
def vertexCount (n m B : ℕ) : ℕ := (n*B+(m+n*(B+1))+3)*(m+n+3)

theorem vertex_pair_fits (c : BinaryFractionalRows.Row n) (m : ℕ) {B : ℕ}
    (fit : ∀ i, StoredBounded (c.get i) B) {p : ℚ≥0 × ℚ≥0} (member : p ∈ ConcurrentVertexBudget.pairs c m) :
    Bounded p.1 (vertexPriceWidth n m B) ∧ Bounded p.2 (vertexMassWidth n m) := by
  obtain ⟨b,present,rest⟩ := List.mem_flatMap.mp member
  obtain ⟨u,entry,rfl⟩ := List.mem_map.mp rest
  have fee := grid_item _ _ (vertexFloor_fits c fit) (vertexPrice_fits c m fit) present
  have mass := grid_item _ _ one_bounded (vertexMass_fits n m) entry
  exact ⟨fee,by simpa only [vertexMassWidth,Nat.mul_zero,Nat.zero_add] using mass⟩

theorem vertex_pair_count (c : BinaryFractionalRows.Row n) (m : ℕ) {B : ℕ}
    (fit : ∀ i, StoredBounded (c.get i) B) :
    (ConcurrentVertexBudget.pairs c m).length ≤ vertexCount n m B := by
  have fee := grid_length _ _ (vertexFloor_fits c fit) (vertexPrice_fits c m fit)
  have mass := grid_length _ _ one_bounded (vertexMass_fits n m)
  simp only [Nat.zero_add] at mass
  unfold ConcurrentVertexBudget.pairs
  simp only [List.length_flatMap,List.length_map,List.map_const',List.sum_replicate,nsmul_eq_mul]
  exact Nat.mul_le_mul fee mass

def edge (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    List (Weights n) × ℕ :=
  collect (MeasuredBudgetCoverCandidate.edge hn A c P) (ConcurrentEdgeBudgetGrid.pairs A c m)

theorem edge_value (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    (edge hn A c P).1 = ConcurrentEdgeBudgetGrid.candidates hn A c P := by
  simp only [edge,collect,List.map_map,Function.comp_def,MeasuredBudgetCoverCandidate.edge_value,
    Code.value_ofNNRat,ConcurrentEdgeBudgetGrid.candidates]

theorem edge_charge (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) {B : ℕ}
    (fit : MatrixFits c B) :
    (edge hn A c P).2 ≤
      ((n*n*B+(m+n*n*(B+1))+3)*(m+n*2+3))*MeasuredBudgetCoverCandidate.edgeWork n m B
        (ConcurrentEdgeBudgetWidths.priceWidth n m B) (ConcurrentEdgeBudgetWidths.massWidth n m) := by
  refine (collect_charge _ _ (fun p hp => ?_)).trans (Nat.mul_le_mul_right _ (ConcurrentEdgeBudgetWidths.pair_count A c m fit))
  obtain ⟨fee,mass⟩ := ConcurrentEdgeBudgetWidths.pair_fits A c m fit (show (p.1,p.2) ∈ _ from hp)
  exact MeasuredBudgetCoverCandidate.edge_charge hn A c P _ _ fit fee mass

def vertex (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n) (P : Vector (Edge n) m) :
    List (BinaryFractionalRows.Row n) × ℕ :=
  collect (MeasuredBudgetCoverCandidate.vertex hn A c P) (ConcurrentVertexBudget.pairs c m)

theorem vertex_value (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n) (P : Vector (Edge n) m) :
    (vertex hn A c P).1 = ConcurrentVertexBudgetGrid.candidates hn A c P := by
  simp only [vertex,collect,List.map_map,Function.comp_def,MeasuredBudgetCoverCandidate.vertex_value,
    Code.value_ofNNRat,ConcurrentVertexBudgetGrid.candidates]

theorem vertex_charge (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n) (P : Vector (Edge n) m)
    {B : ℕ} (fit : ∀ i, StoredBounded (c.get i) B) :
    (vertex hn A c P).2 ≤ vertexCount n m B*MeasuredBudgetCoverCandidate.vertexWork n m B
      (vertexPriceWidth n m B) (vertexMassWidth n m) := by
  refine (collect_charge _ _ (fun p hp => ?_)).trans (Nat.mul_le_mul_right _ (vertex_pair_count c m fit))
  obtain ⟨fee,mass⟩ := vertex_pair_fits c m fit hp
  exact MeasuredBudgetCoverCandidate.vertex_charge hn A c P _ _ fit fee mass

end DirectedFlowCutGap.MeasuredBudgetCandidateLists
